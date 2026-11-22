#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
# Copyright (C) 2026 Theo H.
"""Shared implementation of the per-record RLLB-first reproduction chains."""
import argparse
import hashlib
import importlib.util
import json
import lzma
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time
import uuid

ROOT = Path(__file__).resolve().parents[1]
ALPHABET = b"0123456789ABCDEFGHIJKLMNOPQRSTUV"


def digest(path):
    result = hashlib.sha256()
    with path.open("rb") as source:
        for data in iter(lambda: source.read(1024 * 1024), b""):
            result.update(data)
    return result.hexdigest()


def identity(path, n):
    raw, canonical = hashlib.sha256(), hashlib.sha256()
    mapping, count = {}, 0
    with path.open("rb") as source:
        for data in iter(lambda: source.read(1024 * 1024), b""):
            for symbol in dict.fromkeys(data):
                if symbol not in mapping:
                    if len(mapping) == n:
                        raise RuntimeError("Unexpected alphabet or whitespace in " + str(path))
                    mapping[symbol] = ALPHABET[len(mapping)]
            table = bytes.maketrans(bytes(mapping), bytes(mapping.values()))
            raw.update(data); canonical.update(data.translate(table)); count += len(data)
    if len(mapping) != n:
        raise RuntimeError("Incomplete alphabet in " + str(path))
    return {"length": count, "raw_sha256": raw.hexdigest(),
            "canonical_zero_based_sha256": canonical.hexdigest()}


def main(config_path):
    config_path = Path(config_path)
    config = json.loads(config_path.read_text(encoding="utf-8"))
    parser = argparse.ArgumentParser(description=config["title"] + "; RLLB screening first, record replay second")
    parser.add_argument("--output-dir", type=Path, help="new, nonexistent output directory")
    parser.add_argument("--screen-only", action="store_true", help="stop after the current C++ RLLB stage")
    parser.add_argument("--verify-coverage", action="store_true", help="also run a full literal permutation scan")
    parser.add_argument("--threads", type=int, default=4)
    parser.add_argument("--iterations", type=int, default=20)
    parser.add_argument("--cxx", default="g++")
    parser.add_argument("--make", default="make")
    args = parser.parse_args()
    if os.name == "nt":
        parser.error("Run this reproduction in WSL/Linux Bash")
    if args.threads < 1 or args.iterations < 0:
        parser.error("threads must be positive and iterations nonnegative")
    for name, expected in config["input_sha256"].items():
        if digest(ROOT / name) != expected:
            raise RuntimeError("Pinned input hash mismatch: " + name)
    output = (args.output_dir or ROOT / "build" / config["slug"] / ("reproduction-" + uuid.uuid4().hex)).resolve()
    if output.exists():
        raise FileExistsError("Output directory already exists: " + str(output))
    output.mkdir(parents=True)
    print("Output directory:", output, flush=True)
    started = time.perf_counter()
    commands = []

    def run(label, command, stdout_file=None):
        command = [str(value) for value in command]
        if stdout_file is None:
            result = subprocess.run(command, cwd=ROOT, capture_output=True)
            (output / (label + ".stdout.log")).write_bytes(result.stdout)
        else:
            with stdout_file.open("wb") as target:
                result = subprocess.run(command, cwd=ROOT, stdout=target, stderr=subprocess.PIPE)
        (output / (label + ".stderr.log")).write_bytes(result.stderr)
        commands.append({"label": label, "command": command, "exit_code": result.returncode})
        if result.returncode:
            raise RuntimeError(label + " failed; see logs in " + str(output))
        print(label + ": passed", flush=True)

    # This is the first computational chain for every record. Its mathematical
    # scope remains restricted, regardless of whether it rejects the candidate.
    run("build-rllb", [args.make, "rllb", "rllb-ports", "CXX=" + args.cxx])
    selection = output / "selection.txt"
    source = ROOT / config["screen_selection"]
    if source.suffix == ".xz":
        with lzma.open(source, "rb") as stream, selection.open("wb") as target:
            shutil.copyfileobj(stream, target)
    else:
        shutil.copyfile(source, selection)
    prefix = output / "selection"
    run("generate-rllb-ports", [ROOT / "build/rllb-ports", "--n", config["n"], selection, prefix])
    graph = json.loads((output / "selection.graph.json").read_text())
    if graph["charge"] != config["screen_charge"] or graph["trails"] != config["screen_trails"]:
        raise RuntimeError("Reconstructed selection metrics differ from the record inputs")
    run("rllb", [ROOT / "build/rllb", prefix, graph["charge"], output / "rllb.json", 6,
                 args.iterations, .04, config["target_to_beat"], "-", "-", "--n", config["n"],
                 "--threads", args.threads])
    summary = {"record": config["almanac_id"], "n": config["n"], "screen_completed": True,
               "screen_selection_role": config["screen_selection_role"], "selection": graph,
               "rllb": json.loads((output / "rllb.json").read_text()),
               "rllb_source_sha256": digest(ROOT / "search/rllb.cpp"),
               "word_replayed": False, "coverage_rechecked": False}
    if not args.screen_only:
        codec = output / "spra-codec"
        if not (ROOT / "SPRA/tools/reduced_codec.cpp").is_file():
            raise RuntimeError("Initialize the corpus first: git submodule update --init --recursive")
        run("build-spra-codec", [args.cxx, "-O2", "-std=c++20", ROOT / "SPRA/tools/reduced_codec.cpp", "-o", codec])

        def decode(label, archive, destination):
            packed = output / (label + ".spra")
            with lzma.open(archive, "rb") as source, packed.open("wb") as target:
                shutil.copyfileobj(source, target)
            run(label, [codec, "decode", packed], stdout_file=destination)
            packed.unlink()

        word = output / "word.txt"
        corpus = output / "corpus.txt"
        if config["n"] == 11:
            precursor = output / "precursor-43930543.txt"
            decode("decode-precursor", ROOT / config["precursor_archive"], precursor)
            if digest(precursor) != config["precursor_sha256"]:
                raise RuntimeError("Precursor word hash mismatch")
            spec = importlib.util.spec_from_file_location("record_replay", ROOT / config["replay_program"])
            module = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(module)
            # The supplied 529 materializer is parameterized for the separately
            # recovered 527 plan; this is not a recovered historical optimizer.
            module.EXPECTED_LEN = config["length"]
            module.EXPECTED_SHA = config["raw_sha256"]
            receipt = module.replay(precursor, ROOT / config["fiber_manifest"], ROOT / config["plan"], word)
            (output / "replay.json").write_text(json.dumps(receipt, indent=2) + "\n")
            decode("decode-corpus", ROOT / config["corpus_archive"], corpus)
        else:
            decode("decode-corpus", ROOT / config["corpus_archive"], corpus)
            # SPRA's corpus is canonically one-based. Keep the replay's emitted
            # word canonically zero-based for comparison with the Almanac API.
            table = bytes.maketrans(b"123456789ABCDEFGHIJKLMNOPQRSTUVW", ALPHABET)
            with corpus.open("rb") as source, word.open("wb") as target:
                for data in iter(lambda: source.read(1024 * 1024), b""):
                    target.write(data.translate(table))
        corpus_identity = identity(corpus, config["n"])
        if corpus_identity["canonical_zero_based_sha256"] != config["almanac_sha256"]:
            raise RuntimeError("Pinned SPRA corpus differs from the recorded Almanac identity")
        result = identity(word, config["n"])
        if result["length"] != config["length"] or result["canonical_zero_based_sha256"] != config["almanac_sha256"]:
            raise RuntimeError("Replayed word differs from the record identity")
        if result["raw_sha256"] != config["raw_sha256"]:
            raise RuntimeError("Replayed literal bytes differ from the expected labeling")
        summary.update(word_replayed=True, word=result, corpus=corpus_identity,
                       replay_scope=config["replay_scope"])
        if args.verify_coverage:
            run("build-literal-checker", [args.make, "checkers", "CXX=" + args.cxx])
            run("literal-coverage", [ROOT / "build/literal_check", config["n"],
                                     ALPHABET[:config["n"]].decode(), word])
            summary["coverage_rechecked"] = True
    summary.update(elapsed_seconds=time.perf_counter() - started, commands=commands)
    (output / "run-summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print("Completed:", output / "run-summary.json", flush=True)
    return summary
