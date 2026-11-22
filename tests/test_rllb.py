# SPDX-License-Identifier: GPL-3.0-or-later
# Copyright (C) 2026 Theo H.
"""Check RLLB against exhaustive arrangements, checkpoints, and both input layouts."""
import itertools
import json
import os
from pathlib import Path
import random
import struct
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]


def actual_maximum_overlap(groups):
    """Enumerate actual paths and coupled phases; no trie/dual code is reused."""
    def overlap(left, right):
        return max(k for k in range(len(left)) if k == 0 or left[-k:] == right[:k])
    best = 0
    for order in itertools.permutations(range(len(groups))):
        for path in itertools.product(*(groups[i] for i in order)):
            best = max(best, sum(overlap(a, b) for a, b in zip(path, path[1:])))
    return best


class RllbTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temporary = tempfile.TemporaryDirectory()
        cls.directory = Path(cls.temporary.name)
        cls.binary = cls.directory / ("rllb.exe" if os.name == "nt" else "rllb")
        subprocess.run(["g++", "-O2", "-std=c++20", "-fopenmp", "-Wall", "-Wextra",
                        str(ROOT / "search/rllb.cpp"), "-o", str(cls.binary)], check=True)

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def fixture(self, groups, heads=False):
        prefix = self.directory / "case"
        lines = ["trail\tfirst_port\tn_ports\tnative_length\tfirst_head" if heads else
                 "trail\tstart\tlength\tfirstport\tports"]
        data = bytearray()
        first = 0
        for trail, group in enumerate(groups):
            lines.append(f"{trail}\t{first}\t{len(group)}\t1\t0" if heads else
                         f"{trail}\t0\t1\t{first}\t{len(group)}")
            for word in group:
                code = 0
                for symbol in word:
                    code = (code << 4) | symbol
                data.extend(struct.pack("<Q", code) if heads else struct.pack("<IQ", 0, code))
            first += len(group)
        prefix.with_suffix(".trails.tsv").write_text("\n".join(lines) + "\n")
        prefix.with_suffix(".heads.bin" if heads else ".ports.bin").write_bytes(data)
        return prefix

    def run_bound(self, prefix, n=12, depth=6, iterations=12, prices="-", output_prices="-", threads=1, grouped=False):
        output = self.directory / "result.json"
        command = [str(self.binary), str(prefix), "0", str(output), str(depth),
                   str(iterations), "0.07", "0", str(prices), str(output_prices),
                   "--n", str(n), "--threads", str(threads)]
        if grouped:
            command.append("--grouped")
        process = subprocess.run(command,
                                 capture_output=True, text=True, timeout=30)
        self.assertEqual(process.returncode, 0, process.stderr)
        return json.loads(output.read_text())

    def test_exhaustive_legal_arrangements(self):
        rng = random.Random(20261121)
        cases = 0
        for n in (11, 12, 13):
            h = n - 3
            for depth in (h - 3, h - 2, h - 1):
                for repetition in range(5):
                    if repetition == 0:
                        groups = [[tuple(range(i, i + h))] for i in range(3)]
                    else:
                        groups = [[tuple(rng.sample(range(n), h)) for _ in range(2)] for _ in range(3)]
                    prefix = self.fixture(groups, heads=(n == 13))
                    result = self.run_bound(prefix, n, depth)
                    maximum = actual_maximum_overlap(groups)
                    self.assertGreaterEqual(result["certified_overlap_upper"], maximum)
                    self.assertLessEqual(result["joining_cost_lower_bound"], h * len(groups) - maximum)
                    self.assertFalse(result["certified_for_unrestricted_search"])
                    if n == 13:
                        coarse = self.run_bound(prefix, n, depth, grouped=True)
                        self.assertGreaterEqual(coarse["certified_overlap_upper"], maximum)
                        self.assertLessEqual(coarse["joining_cost_lower_bound"], h * len(groups) - maximum)
                    cases += 1
        self.assertEqual(cases, 45)

    def test_head_layout_and_keys_above_32_bits(self):
        groups = [[(12, 1, 2, 3, 4, 5, 6, 7, 8, 9)],
                  [(11, 1, 2, 3, 4, 5, 6, 7, 8, 9)]]
        result = self.run_bound(self.fixture(groups, heads=True), n=13, depth=9)
        keys = {word[:9] for group in groups for word in group}
        keys |= {word[-9:] for group in groups for word in group}
        self.assertEqual(result["trie_levels"][0]["nodes"], len(keys))
        # The two long prefixes differ only above the 32-bit range.
        self.assertEqual(len(keys), 3)

    def test_identical_ports_on_same_trail_are_not_neighbors(self):
        word = tuple(range(9))
        result = self.run_bound(self.fixture([[word, word]]), iterations=0)
        self.assertTrue(all(level["incoming_available"] == level["outgoing_available"] == 0
                            for level in result["trie_levels"]))

    def test_grouped_n13_matches_archived_trace(self):
        reference = json.loads((ROOT / "tests/data/rllb_grouped_n13.json").read_text())
        prefix = self.fixture(reference["groups"], heads=True)
        output = self.directory / "grouped.json"
        histories = []
        for threads in (1, 4):
            subprocess.run([str(self.binary), str(prefix), "0", str(output), "6",
                            str(reference["iterations"]), str(reference["step"]), "0",
                            "--n", "13", "--grouped", "--threads", str(threads)],
                           capture_output=True, check=True)
            got = json.loads(output.read_text())["dual_history"]
            self.assertEqual(len(got), len(reference["dual_history"]))
            for actual, expected in zip(got, reference["dual_history"]):
                self.assertLessEqual(abs(actual - expected), 0.000051)
            histories.append(got)
        self.assertEqual(*histories)

    def test_parallel_determinism(self):
        rng = random.Random(529)
        groups = [[tuple(rng.sample(range(12), 9)) for _ in range(5)] for _ in range(50)]
        prefix = self.fixture(groups)
        one = self.run_bound(prefix, threads=1)
        four = self.run_bound(prefix, threads=4)
        for key in ("dual_history", "dual_overlap_upper_raw", "length_lower_bound", "trie_levels"):
            self.assertEqual(one[key], four[key])

    def test_checkpoint_saves_actual_best_prices_and_ignores_old_score(self):
        groups = [[tuple(range(i, i + 9))] for i in range(3)]
        prefix = self.fixture(groups)
        checkpoint = self.directory / "prices.bin"
        original = self.run_bound(prefix, output_prices=checkpoint)
        data = bytearray(checkpoint.read_bytes())
        struct.pack_into("<d", data, 16, 0.0)  # Deliberately false remembered score.
        checkpoint.write_bytes(data)
        recomputed = self.run_bound(prefix, prices=checkpoint, iterations=0)
        self.assertEqual(recomputed["certified_overlap_upper"], original["certified_overlap_upper"])
        self.assertAlmostEqual(recomputed["dual_overlap_upper_raw"], original["dual_overlap_upper_raw"], places=8)
        self.assertGreater(recomputed["dual_overlap_upper_raw"], 0)
        struct.pack_into("<d", data, 40, float("nan"))
        checkpoint.write_bytes(data)
        failed = subprocess.run([str(self.binary), str(prefix), "0", str(self.directory / "invalid.json"),
                                 "6", "0", "0", "0", str(checkpoint)], capture_output=True, text=True)
        self.assertNotEqual(failed.returncode, 0)
        self.assertIn("non-finite checkpoint price", failed.stderr)

    def test_truncated_ports_rejected(self):
        prefix = self.fixture([[tuple(range(9))]])
        prefix.with_suffix(".ports.bin").write_bytes(b"short")
        failed = subprocess.run([str(self.binary), str(prefix), "0", str(self.directory / "bad.json")],
                                capture_output=True, text=True)
        self.assertNotEqual(failed.returncode, 0)
        self.assertIn("length mismatch", failed.stderr)


if __name__ == "__main__":
    unittest.main()
