# Reproduce N=11 / 43,930,527

The paper is [43930527.pdf](43930527.pdf), with [LaTeX source](43930527.tex). See the [input pins](record.json), [import provenance](source-import.json), [current receipt](reproduction-summary.json), and [personal research notes](NOTES.md).

## Chain 1: current C++ RLLB screening

Run from the repository root in WSL/Linux Bash. The scorer to run is [`search/rllb.cpp`](../../../search/rllb.cpp), built as `build/rllb`. Its [shared guide](../../rllb/README.md) documents arguments and bound scope.

```sh
make rllb rllb-ports
mkdir -p build/n11-43930527
cp data/n11/43930529/inputs/n11_43930529_full_selection.txt build/n11-43930527/selection.txt
./build/rllb-ports --n 11 build/n11-43930527/selection.txt build/n11-43930527/selection
./build/rllb build/n11-43930527/selection 20089 build/n11-43930527/rllb.json 6 20 .04 43930529 - - --n 11 --threads 4
```

The 529 predecessor selection is screened as a control. It is not asserted to be the final 527 native selection. The 527 word is then assembled from the 543 precursor and a separately recovered exact plan.

This first chain regenerates the completed trail/port graph, then runs the new RLLB scorer. It is a contemporary reproducibility stage, not a claim that the new optimized program was the historical discovery program. RLLB here covers one intact weight-3 opening per completed trail. Its rejection flag does not reject weight-2 openings, split trails, or the unrestricted arrangement search; passing it does not construct a word.

## Chain 2: exact record witness

The per-record runner executes **Chain 1 first**, then replays the record:

```sh
git submodule update --init --recursive
python3 docs/n11/43930527/reproduce.py
# Run only the RLLB chain:
python3 docs/n11/43930527/reproduce.py --screen-only
# Optional independent full permutation scan:
python3 docs/n11/43930527/reproduce.py --verify-coverage
```

Dependencies: GNU Make, 64-bit GCC/G++, Python 3.10+, and the pinned SPRA submodule. `--threads`, `--iterations`, `--cxx`, `--make`, and `--output-dir` select the screening budget, tools, and a fresh output directory. NumPy, SciPy, and a solver are not needed for this saved-witness chain.

Each run creates `build/n11-43930527/reproduction-<id>/`, refuses existing output directories, and records source commands, generated native metrics, the RLLB JSON, literal and canonical word hashes, and `run-summary.json`. Generated words and binaries remain outside the corpus submodule. The default verifies exact word identity; the historical factorial coverage result is recorded separately, and a full rescan is opt-in.

## Word identities

The [Almanac entry](https://superpermutations.com/w/W-0132) identifies the canonically zero-based word. Canonicalization assigns `0,1,...` in order of first appearance; it is a global alphabet permutation and differs from simply adding or subtracting one from historical labels.

```text
emitted word SHA-256: 8b78860eebb7d25ffbf1147b6609d5c156e2fed2e0a16c5a23ad949cc0b5825c
Almanac canonical SHA-256: d0a74cf72adeb2d117933fa6237dec71113f32df8c07eeb28ad5d859e63a44a5
```

Both are checked by the runner. SPRA's corpus copies are canonically one-based; comparison uses canonical zero-based hashes.

## Recovered 527 assembly

The supplied 529 materializer is parameterized with the 527 expected length/hash and `data/n11/43930527/inputs/recovered_527_order.tsv`. This plan was recovered in this repository by exact matching of the 543 source's relabeled whole-fiber templates and unchanged cores against the known 527 witness. It reconstructs the literal 527 word without reading that witness during replay.

The saved plans give:

| Accounting | 529 plan | 527 plan |
| --- | ---: | ---: |
| Sum of piece lengths | 43,930,683 | 43,930,685 |
| Sum of literal overlaps | 154 | 158 |
| Emitted length | 43,930,529 | 43,930,527 |

The five units `34,38,39,40,41` move across the first core. The first core moves from position 37 to 42 in zero-based order indexing. Two extra piece symbols and four extra overlap symbols give a net saving of two.

The optional `data/n11/43930527/src/recover_527_order.py` documents the recovery procedure. Build `build/spra/reduced_codec` as in the shared corpus guide, then run it from the repository root. It writes a recovered plan under `build/rllb-records/`; it is a witness-derived recovery tool, not the missing historical free-core optimizer. Its byte-for-byte witness check uses the historical inverse label map `123456789AB -> 2053618479A`.

A final 527 native selection is not inferred merely from the 529 selection, nor is the historical free-core search source claimed to have been recovered.
