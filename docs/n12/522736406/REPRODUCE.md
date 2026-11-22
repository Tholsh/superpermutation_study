# Reproduce N=12 / 522,736,406

The paper is [522736406.pdf](522736406.pdf), with [LaTeX source](522736406.tex). See the [input pins](record.json), [import provenance](source-import.json), [current receipt](reproduction-summary.json), and [personal research notes](NOTES.md).

## Chain 1: current C++ RLLB screening

Run from the repository root in WSL/Linux Bash. The scorer to run is [`search/rllb.cpp`](../../../search/rllb.cpp), built as `build/rllb`. Its [shared guide](../../rllb/README.md) documents arguments and bound scope.

```sh
make rllb rllb-ports
mkdir -p build/n12-522736406
xz -dc data/n12/522736406/inputs/n12_522736406.selection.xz > build/n12-522736406/selection.txt
./build/rllb-ports --n 12 build/n12-522736406/selection.txt build/n12-522736406/selection
./build/rllb build/n12-522736406/selection 182712 build/n12-522736406/rllb.json 6 20 .04 522736409 - - --n 12 --threads 4
```

The supplied final 406 native selection is screened. Exact witness replay then decodes the pinned SPRA archive. The original selection-to-plan assembly is not claimed to be self-contained.

This first chain regenerates the completed trail/port graph, then runs the new RLLB scorer. It is a contemporary reproducibility stage, not a claim that the new optimized program was the historical discovery program. RLLB here covers one intact weight-3 opening per completed trail. Its rejection flag does not reject weight-2 openings, split trails, or the unrestricted arrangement search; passing it does not construct a word.

## Chain 2: exact record witness

The per-record runner executes **Chain 1 first**, then replays the record:

```sh
git submodule update --init --recursive
python3 docs/n12/522736406/reproduce.py
# Run only the RLLB chain:
python3 docs/n12/522736406/reproduce.py --screen-only
# Optional independent full permutation scan:
python3 docs/n12/522736406/reproduce.py --verify-coverage
```

Dependencies: GNU Make, 64-bit GCC/G++, Python 3.10+, and the pinned SPRA submodule. `--threads`, `--iterations`, `--cxx`, `--make`, and `--output-dir` select the screening budget, tools, and a fresh output directory. NumPy, SciPy, and a solver are not needed for this saved-witness chain.

Each run creates `build/n12-522736406/reproduction-<id>/`, refuses existing output directories, and records source commands, generated native metrics, the RLLB JSON, literal and canonical word hashes, and `run-summary.json`. Generated words and binaries remain outside the corpus submodule. The default verifies exact word identity; the historical factorial coverage result is recorded separately, and a full rescan is opt-in.

## Word identities

The [Almanac entry](https://superpermutations.com/w/W-0136) identifies the canonically zero-based word. Canonicalization assigns `0,1,...` in order of first appearance; it is a global alphabet permutation and differs from simply adding or subtracting one from historical labels.

```text
emitted word SHA-256: 6bf1ef85a2cc52add9238329a7c3129e06ef9c0fd76a8dc9d3215a33441a1558
Almanac canonical SHA-256: 6bf1ef85a2cc52add9238329a7c3129e06ef9c0fd76a8dc9d3215a33441a1558
```

Both are checked by the runner. SPRA's corpus copies are canonically one-based; comparison uses canonical zero-based hashes.

## What is and is not replayed

The native selection and 2,832-row plan are preserved in `data/n12/522736406/inputs/`. The original plan references 2,826 `base` entries, three `cand0` entries, and three `cand3` entries; those source trail catalogues are not included in the supplied package. A saved plan with such external source IDs is not, by itself, a self-contained selection-to-word materializer.

The current reproducible chain therefore provides exact final-selection completion and RLLB scoring, followed by exact reconstruction of the known word through SPRA decoding. It does **not** claim to regenerate the historical selection search, arrangement search, or the missing source catalogues. `evidence/original-validation.json` is the supplied historical scan result; it is distinct from this repository's current identity checks.

The plan's opening overhangs total 25,557 and its overlaps total 19,063, giving net joining cost 6,494, consistent with `F3 + Q + J = 522,547,200 + 182,712 + 6,494 = 522,736,406`.

## Independent RLLB certificate control

The shared Q210 control is a different selection from the record selection. It demonstrates why the updated screen was needed:

```sh
mkdir -p build/rllb-q210
xz -dc data/rllb/20261122/inputs/Q210.selection.xz > build/rllb-q210/selection.txt
xz -dc data/rllb/20261122/inputs/Q210_certificate_weights.bin.xz > build/rllb-q210/prices.bin
./build/rllb-ports --n 12 build/rllb-q210/selection.txt build/rllb-q210/selection
./build/rllb build/rllb-q210/selection 179424 build/rllb-q210/certificate.json 6 0 0 522736428 build/rllb-q210/prices.bin -
```

Expected: 6,624 trails; `U <= 49,770`; `J >= 9,846`; restricted `L >= 522,736,470`. The comparison length 522,736,428 belongs to that historical screening experiment. This is not the charge, trail count, or target of the 406 record chain above.
