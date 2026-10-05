"""Compile and check paint-waste against an independent window-set oracle."""
import itertools
import math
from pathlib import Path
import random
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]


class PaintWasteTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.directory = tempfile.TemporaryDirectory()
        cls.binary = Path(cls.directory.name) / "paint-waste.exe"
        subprocess.run(["g++", "-std=c++20", "-O2", "-Wall", "-Wextra",
                        "-pedantic", str(ROOT / "tools/reduced_alphabet.cpp"),
                        "-o", str(cls.binary)], check=True)

    @classmethod
    def tearDownClass(cls):
        cls.directory.cleanup()

    def run_word(self, word, *args):
        return subprocess.run([str(self.binary), *map(str, args)], input=word,
                              text=True, capture_output=True)

    def stats(self, word, n):
        result = self.run_word(word, "-s", n)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stderr, "")
        self.assertNotIn("\x1b", result.stdout)
        return dict((key, int(value)) for key, value in
                    (line.split(": ") for line in result.stdout.splitlines()))

    def test_concrete_valid_word(self):
        self.assertEqual(self.stats("123121321", 3), {
            "length": 9, "symbols": 9, "n": 3, "windows": 7,
            "dirty": 1, "clean": 6, "max_dirty_run": 1,
            "max_clean_run": 3, "dirty_runs": 1, "clean_runs": 2,
            "required_permutations": 6, "distinct_permutations": 6,
            "missing_permutations": 0, "repeated_permutation_windows": 0,
            "valid_superpermutation": 1})

    def test_independent_oracle(self):
        rng = random.Random(42)
        for n in range(1, 6):
            alphabet = "12345"[:n]
            permutations = {"".join(p) for p in itertools.permutations(alphabet)}
            words = ["", alphabet[:-1], alphabet * 3]
            words += ["".join(rng.choice(alphabet) for _ in range(80)) for _ in range(5)]
            for word in words:
                with self.subTest(n=n, word=word):
                    windows = [word[i:i+n] for i in range(max(0, len(word)-n+1))]
                    clean = [w for w in windows if w in permutations]
                    stats = self.stats(word, n)
                    self.assertEqual(stats["length"], len(word))
                    self.assertEqual(stats["windows"], len(windows))
                    self.assertEqual(stats["clean"], len(clean))
                    self.assertEqual(stats["dirty"], len(windows)-len(clean))
                    self.assertEqual(stats["distinct_permutations"], len(set(clean)))
                    self.assertEqual(stats["missing_permutations"], math.factorial(n)-len(set(clean)))
                    self.assertEqual(stats["repeated_permutation_windows"], len(clean)-len(set(clean)))
                    self.assertEqual(stats["valid_superpermutation"], int(set(clean) == permutations))

    def test_default_order_decimal_statistics_and_long_depth(self):
        word = "12" * 250 + "11"
        result = self.run_word(word, 2)
        self.assertEqual(result.returncode, 0)
        self.assertEqual(result.stderr, "")
        before, statistics = result.stdout.split("statistics:\n")
        self.assertIn("reduced_alphabet_words:\n[1f4:2]", before)
        short = self.run_word(word, 2, "-s")
        self.assertEqual(statistics, short.stdout)
        self.assertEqual(self.stats(word, 2)["max_clean_run"], 500)

    def test_whitespace_and_corpus(self):
        self.assertEqual(self.stats("1 23\r\n121\t321", 3), self.stats("123121321", 3))
        stats = self.stats((ROOT / "words/5/153-recursive.txt").read_text(), 5)
        self.assertEqual(stats["length"], 153)
        self.assertEqual(stats["distinct_permutations"], 120)
        self.assertEqual(stats["valid_superpermutation"], 1)

    def test_rejected_arguments_and_input(self):
        for args in [[], [0], [10], ["3foo"], [3, "--unknown"], ["-s", "-s", 3]]:
            self.assertNotEqual(self.run_word("123", *args).returncode, 0)
        for word in ["124", "120", "12x"]:
            self.assertNotEqual(self.run_word(word, "-s", 3).returncode, 0)
        self.assertEqual(self.run_word("", "--help").returncode, 0)


if __name__ == "__main__":
    unittest.main()
