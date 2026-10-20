#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
# Copyright (C) 2026 Theo H.
"""Build and verify the bundled N=8 plans without running a randomized search."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time
import uuid


ROOT = Path(__file__).resolve().parents[3]
PACKAGE = ROOT / "data/n8/46173"
CORPUS = ROOT / "words/8/46173/n8-46173_1indexed_canonical.txt"
MANIFEST_SHA256 = "e03895c622bbc8b352b851564e1b090a5891f1339de6aa54cc6a22122e5904a8"


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def compiler_path(value):
    found = shutil.which(value)
    require(found is not None, "Compiler not found: " + value)
    return str(Path(found).resolve())


def verify_package():
    manifest = PACKAGE / "SHA256SUMS"
    require(sha256(manifest) == MANIFEST_SHA256, "Package checksum manifest changed")
    files = {}
    for line in manifest.read_text(encoding="utf-8").splitlines():
        expected, name = line.split("  ", 1)
        path = (PACKAGE / name).resolve()
        path.relative_to(PACKAGE.resolve())
        require(sha256(path) == expected, "Package checksum mismatch: " + name)
        files[name] = expected
    return files


def canonical_word(word):
    require(word.endswith(b"\n"), "Expected a final LF in the solution")
    word = word[:-1]
    require(set(word) == set(b"01234567"), "Unexpected solution alphabet")
    labels = {}
    normalized = bytearray()
    for symbol in word:
        if symbol not in labels:
            labels[symbol] = ord("1") + len(labels)
        normalized.append(labels[symbol])
    return bytes(normalized) + b"\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cc", default="gcc", help="GCC C compiler executable")
    parser.add_argument("--cxx", default="g++", help="GCC C++ compiler executable")
    parser.add_argument("--output-dir", type=Path, help="New, nonexistent output directory")
    args = parser.parse_args()

    files = verify_package()
    cc, cxx = compiler_path(args.cc), compiler_path(args.cxx)
    output = (args.output_dir or ROOT / "build/n8-46173" / ("reproduction-" + uuid.uuid4().hex)).resolve()
    require(not output.exists(), "Output directory already exists: " + str(output))
    output.mkdir(parents=True)
    print("Output directory:", output, flush=True)
    env = os.environ.copy()
    env["PATH"] = os.pathsep.join([str(Path(cc).parent), str(Path(cxx).parent), env.get("PATH", "")])
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    started = time.perf_counter()
    commands = []

    def run(name, command):
        command = [str(arg) for arg in command]
        result = subprocess.run(command, cwd=PACKAGE, env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        (output / (name + ".stdout.log")).write_bytes(result.stdout)
        (output / (name + ".stderr.log")).write_bytes(result.stderr)
        commands.append({"name": name, "command": command, "exit_code": result.returncode})
        require(result.returncode == 0, name + " failed; see logs in " + str(output))
        print(name + ": passed", flush=True)
        return result.stdout

    suffix = ".exe" if os.name == "nt" else ""
    search = output / ("trailsearch" + suffix)
    checker = output / ("literal_check" + suffix)
    run("build-trailsearch", [cc, "-O2", "-std=gnu11", "-fopenmp", "src/trailsearch.c", "-o", search, "-lm"])
    run("build-literal-check", [cxx, "-O2", "-std=c++17", "src/literal_check.cpp", "-o", checker])

    examples = PACKAGE / "examples/n8"
    for name in ("reference", "solution"):
        replayed = output / (name + "-replayed.txt")
        run(name + "-replay", [search, examples / "base.txt", replayed, "--plan-in", examples / (name + ".plan"), "--time", "0", "--threads", "1"])
        require(replayed.read_bytes() == (examples / (name + ".txt")).read_bytes(), name + " replay differs from packaged word")

    candidate = output / "solution-replayed.txt"
    coverage = json.loads(run("literal-coverage", [checker, "8", "01234567", candidate, "--deletions"]))
    require(coverage["length"] == 46173, "Unexpected solution length")
    require(coverage["distinct_permutations"] == 40320 and coverage["missing_permutations"] == 0, "Incomplete permutation coverage")
    require(coverage["tested_deletions"] == 46173 and coverage["coverage_preserving_deletions"] == [], "Unexpected single-deletion result")

    python_replay = output / "python-replayed.txt"
    run("python-replay", [sys.executable, "src/applyplan.py", examples / "base.txt", examples / "base.tsv", examples / "solution.plan", python_replay])
    require(python_replay.read_bytes() == candidate.read_bytes(), "Independent Python replay differs")

    regenerated = output / "regenerated-base.txt"
    table = output / "regenerated-base.tsv"
    run("regenerate-base", [sys.executable, "src/geng.py", examples / "selection.txt", regenerated, "--table", table])
    require(regenerated.read_bytes() == (examples / "base.txt").read_bytes(), "Regenerated base differs")
    require(table.read_bytes() == (examples / "base.tsv").read_bytes(), "Regenerated base table differs")

    canonical = canonical_word(candidate.read_bytes())
    require(canonical == CORPUS.read_bytes(), "Canonical solution differs from corpus word")
    (output / "canonical-solution.txt").write_bytes(canonical)
    summary = {
        "success": True,
        "package": "data/n8/46173",
        "package_files_verified": len(files),
        "manifest_sha256": MANIFEST_SHA256,
        "parent_replay_byte_identical": True,
        "solution_replay_byte_identical": True,
        "python_spelling_byte_identical": True,
        "regenerated_base_byte_identical": True,
        "regenerated_table_byte_identical": True,
        "canonical_solution_matches_corpus": True,
        "solution_sha256_with_lf": sha256(candidate),
        "canonical_corpus_sha256_with_lf": sha256(CORPUS),
        "literal_checker_result": coverage,
        "elapsed_seconds": time.perf_counter() - started,
        "tools": {"cc": cc, "cxx": cxx, "python": sys.executable},
        "commands": commands,
    }
    (output / "run-summary.json").write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    print("Verified: length 46173; all 40320 permutations; no coverage-preserving single deletion.")
    print("Canonical replay matches:", CORPUS.relative_to(ROOT))
    print("Logs and run-summary.json:", output)


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, RuntimeError) as error:
        print("Reproduction failed:", error, file=sys.stderr)
        sys.exit(1)
