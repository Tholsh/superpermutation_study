# Reproduce N=11 / 43,930,529

The paper is [43930529.pdf](43930529.pdf), with [LaTeX source](43930529.tex). See the [input pins](record.json), [import provenance](source-import.json), [current receipt](reproduction-summary.json), and [personal research notes](NOTES.md).

## Chain 1: current C++ RLLB screening

Run from the repository root in WSL/Linux Bash. The scorer to run is [`search/rllb.cpp`](../../../search/rllb.cpp), built as `build/rllb`. Its [shared guide](../../rllb/README.md) documents arguments and bound scope.

```sh
make rllb rllb-ports
mkdir -p build/n11-43930529
cp data/n11/43930529/inputs/n11_43930529_full_selection.txt build/n11-43930529/selection.txt
./build/rllb-ports --n 11 build/n11-43930529/selection.txt build/n11-43930529/selection
./build/rllb build/n11-43930529/selection 20089 build/n11-43930529/rllb.json 6 20 .04 43930534 - - --n 11 --threads 4
```

The final 529 native selection is screened. The word is then assembled from the 543 precursor and supplied recovered plan.

This first chain regenerates the completed trail/port graph, then runs the new RLLB scorer. It is a contemporary reproducibility stage, not a claim that the new optimized program was the historical discovery program. RLLB here covers one intact weight-3 opening per completed trail. Its rejection flag does not reject weight-2 openings, split trails, or the unrestricted arrangement search; passing it does not construct a word.

## Chain 2: exact record witness

The per-record runner executes **Chain 1 first**, then replays the record:

```sh
git submodule update --init --recursive
python3 docs/n11/43930529/reproduce.py
# Run only the RLLB chain:
python3 docs/n11/43930529/reproduce.py --screen-only
# Optional independent full permutation scan:
python3 docs/n11/43930529/reproduce.py --verify-coverage
```

Dependencies: GNU Make, 64-bit GCC/G++, Python 3.10+, and the pinned SPRA submodule. `--threads`, `--iterations`, `--cxx`, `--make`, and `--output-dir` select the screening budget, tools, and a fresh output directory. NumPy, SciPy, and a solver are not needed for this saved-witness chain.

Each run creates `build/n11-43930529/reproduction-<id>/`, refuses existing output directories, and records source commands, generated native metrics, the RLLB JSON, literal and canonical word hashes, and `run-summary.json`. Generated words and binaries remain outside the corpus submodule. The default verifies exact word identity; the historical factorial coverage result is recorded separately, and a full rescan is opt-in.

## Word identities

The [Almanac entry](https://superpermutations.com/w/W-0131) identifies the canonically zero-based word. Canonicalization assigns `0,1,...` in order of first appearance; it is a global alphabet permutation and differs from simply adding or subtracting one from historical labels.

```text
emitted word SHA-256: 3743ea507d76b8f907b8f2ddba0f9825b5ee62159e609b0c5a4dfe30fa8d34be
Almanac canonical SHA-256: a9b1567086163abe20c4037db4b92f4e74be181795b7c6d4572d001bab74186d
```

Both are checked by the runner. SPRA's corpus copies are canonically one-based; comparison uses canonical zero-based hashes.

## Saved assembly and search provenance

`data/n11/43930529/inputs/` contains the original 543 SPRA precursor, the 48-fiber manifest, the supplied recovered 529 order, and the complete 529 native selection. The supplied `src/replay_529.py` materializes the 50-unit plan without reading the target 529 word. The runner independently compares its canonical hash with the pinned SPRA corpus.

`src/joint_50unit_search.py` identifies itself as a **new replacement** for the lost historical placement optimizer. It performs exact fixed-order template/phase DP inside a heuristic order search, keeping the two core units in the input order's core slots. It is not the original discovery program. An optional contemporary search is:

```sh
python3 data/n11/43930529/src/joint_50unit_search.py --source build/precursor-43930543.txt --manifest data/n11/43930529/inputs/n11_43930543_fiber_manifest.csv --order data/n11/43930529/inputs/recovered_529_order.tsv --iterations 100 --seed 529 --out-prefix build/new-n11-search
```

Use a decoded precursor from a completed per-record run at the `--source` path. The standalone search's shorter TSV is an optimizer output format, not the recovered replay-plan schema. Its output needs separate word validation before being presented as a result. No command here claims to replay the lost original optimizer's exact move sequence.
