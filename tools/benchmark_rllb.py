#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
# Copyright (C) 2026 Theo H.
"""Benchmark the fast scorer against the supplied RLLB bundle's original C++ scorer."""
import argparse
import hashlib
import json
import lzma
from pathlib import Path
import platform
import statistics
import subprocess
import tempfile
import time
import zipfile

ROOT = Path(__file__).resolve().parents[1]
MODULE = "modules/04_n12_RLLB_GlobalTrie_Certificate/"
FILES = ("global_trie_multilevel.cpp", "generate_ports_only.cpp",
         "selections/Q210.selection.xz", "certificates/Q210_certificate_weights.bin.xz")
COMPARE = ("trie_levels", "dual_history", "dual_overlap_upper_raw", "certified_overlap_upper",
           "joining_cost_lower_bound", "length_lower_bound", "certified_reject_restricted")


def bundle_files(bundle):
    if bundle.is_dir():
        if (bundle / "src/global_trie_multilevel.cpp").is_file():
            return {name: (bundle / ("src" if name.endswith(".cpp") else "inputs") / Path(name).name).read_bytes()
                    for name in FILES}
        return {name: (bundle / MODULE / name).read_bytes() for name in FILES}
    with zipfile.ZipFile(bundle) as archive:
        result = {}
        for name in FILES:
            suffix = MODULE + name
            matching = [entry for entry in archive.namelist() if entry == suffix or entry.endswith("/" + suffix)]
            if len(matching) != 1:
                raise ValueError("Expected exactly one bundle file: " + suffix)
            result[name] = archive.read(matching[0])
        return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bundle", type=Path, default=ROOT / "data/rllb/20261122",
                        help="pinned reference folder, supplied ZIP, or extracted bundle root")
    parser.add_argument("--binary", type=Path, default=ROOT / "build/rllb")
    parser.add_argument("--cxx", default="g++")
    parser.add_argument("--iterations", type=int, default=20)
    parser.add_argument("--threads", type=int, default=4)
    parser.add_argument("--repeats", type=int, default=3)
    parser.add_argument("--output", type=Path, help="optional JSON report")
    args = parser.parse_args()
    if args.iterations < 0 or args.repeats < 1 or args.threads < 1:
        parser.error("iterations must be nonnegative; repeats and threads must be positive")
    binary = args.binary.resolve()
    if not binary.is_file():
        parser.error("Build the scorer first: make rllb")
    source = bundle_files(args.bundle)
    with tempfile.TemporaryDirectory(prefix="rllb-benchmark-") as directory:
        work = Path(directory)
        for name in ("global_trie_multilevel.cpp", "generate_ports_only.cpp"):
            (work / name).write_bytes(source[name])
        (work / "Q210.selection").write_bytes(lzma.decompress(source[FILES[2]]))
        (work / "prices.bin").write_bytes(lzma.decompress(source[FILES[3]]))
        for name, output in (("global_trie_multilevel.cpp", "legacy"), ("generate_ports_only.cpp", "generate")):
            subprocess.run([args.cxx, "-O3", "-std=c++20", str(work / name), "-o", str(work / output)], check=True)

        def run(label, command):
            started = time.perf_counter()
            with (work / (label + ".log")).open("w") as log:
                process = subprocess.run([str(arg) for arg in command], stdout=log, stderr=subprocess.STDOUT)
            if process.returncode:
                raise RuntimeError(label + " failed:\n" + (work / (label + ".log")).read_text())
            return time.perf_counter() - started

        generation = run("generate", [work / "generate", work / "Q210.selection", work / "Q210"])
        results = {}
        for scenario, rounds, prices in (("saved_certificate", 0, work / "prices.bin"),
                                        ("optimize", args.iterations, "-")):
            measurements = {"legacy": [], "fast_single": [], "fast_parallel": []}
            reference = None
            # Interleave implementations so one is not always measured first.
            for repetition in range(args.repeats):
                names = list(measurements)
                if repetition % 2:
                    names.reverse()
                for name in names:
                    output = work / (scenario + "-" + name + ".json")
                    executable = work / "legacy" if name == "legacy" else binary
                    command = [executable, work / "Q210", 179424, output, 6, rounds, .04,
                               522736428, prices, "-"]
                    if name != "legacy":
                        command += ["--threads", 1 if name == "fast_single" else args.threads]
                    elapsed = run(scenario + "-" + name, command)
                    value = json.loads(output.read_text())
                    scientific = {key: value[key] for key in COMPARE}
                    if reference is None:
                        reference = scientific
                    if scientific != reference:
                        raise RuntimeError("Scoring differs from the original: " + scenario + " " + name)
                    measurements[name].append(elapsed)
                    print(scenario, name, round(elapsed, 4), "seconds; same scores", flush=True)
            medians = {name: statistics.median(values) for name, values in measurements.items()}
            results[scenario] = {"seconds": measurements, "median_seconds": medians,
                                 "speedup_single": medians["legacy"] / medians["fast_single"],
                                 "speedup_parallel": medians["legacy"] / medians["fast_parallel"],
                                 "identical_scores_and_history": True, "scores": reference}
        compiler = subprocess.check_output([args.cxx, "--version"], text=True).splitlines()[0]
        cpu = "unknown"
        if Path("/proc/cpuinfo").exists():
            cpu = next((line.split(":", 1)[1].strip() for line in Path("/proc/cpuinfo").read_text().splitlines()
                        if line.startswith("model name")), cpu)
        report = {"scenario": "complete n12 Q210; 3,808,224 ports; 6,624 trails; trie depths 6..8",
                  "scope": "restricted intact weight-3 RLLB; no literal-word search or coverage check",
                  "compiler": compiler, "platform": platform.platform(), "cpu": cpu,
                  "flags": "-O3 -std=c++20; fast binary also uses -fopenmp",
                  "threads": args.threads, "iterations": args.iterations, "repeats": args.repeats,
                  "timing_method": "separate processes, reused input files, interleaved runs; not a cold-disk benchmark",
                  "input_sha256": {name: hashlib.sha256(data).hexdigest() for name, data in source.items()},
                  "fast_source_sha256": hashlib.sha256((ROOT / "search/rllb.cpp").read_bytes()).hexdigest(),
                  "port_generation_seconds_excluded_from_scorer_timings": generation, "results": results}
        if args.output:
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_text(json.dumps(report, indent=2) + "\n")
        for name, value in results.items():
            print(name, "single-thread speedup", round(value["speedup_single"], 2),
                  "parallel speedup", round(value["speedup_parallel"], 2))


if __name__ == "__main__":
    main()
