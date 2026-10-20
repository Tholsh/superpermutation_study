# Reproduce the N=8 word of length 46,173

The repository includes the source, fixed input selection, and saved assembly plans needed to reproduce the reduction from Jakub Halfar's 46,174-symbol word to 46,173 symbols. The solution uses the same sixteen complete trails in Jay Pantone's construction, changing their order and openings. Replaying the saved plan is deterministic and takes no randomized search.

The mathematical writeup is [46173.tex](46173.tex). The [source import record](source-import.json) records the ZIP hash and corpus relationship; the [verified reproduction receipt](reproduction-summary.json) records the checks run in this repository.

## Files

The original ZIP was extracted byte-for-byte into [`data/n8/46173/`](../../../data/n8/46173/), preserving its internal paths and all 25 files. Its [README](../../../data/n8/46173/README.md) also documents standalone Make and PowerShell commands.

| Path relative to `data/n8/46173/` | Purpose |
| --- | --- |
| `src/trailsearch.c` | Halfar's unchanged assembly search and saved-plan replayer. |
| `src/literal_check.cpp` | Pantone's independent literal coverage and single-deletion checker. |
| `src/applyplan.py` | Independent Python spelling of the saved plan. |
| `src/geng.py`, `src/gen12.py` | Selection-to-base generator and its dependency. |
| `examples/n8/selection.txt` | Fixed input selection. |
| `examples/n8/base.txt`, `base.tsv` | Base word and trail table used by both plans. |
| `examples/n8/reference.plan`, `reference.txt` | Saved parent plan and 46,174-symbol word. |
| `examples/n8/solution.plan`, `solution.txt` | Saved winning plan and 46,173-symbol word. |
| `evidence/` | Original search and verification records. |
| `SHA256SUMS` | Original checksums of the other 24 bundled files. |
| `LICENSE`, `NOTICE`, `PROVENANCE.md` | Upstream terms, attribution, and pinned source revisions. |

The bundled model and word files retain their original zero-based labels, because plans and checksums refer to those exact bytes. The corpus copy remains [`words/8/46173/n8-46173_1indexed_canonical.txt`](../../../words/8/46173/n8-46173_1indexed_canonical.txt). Canonicalization assigns `1` through `8` in order of first appearance; it is not simply adding one to every label. For this solution, `5,2,4,0,3,1,6,7` map to `1,2,3,4,5,6,7,8`.

## Run the complete reproduction

Requires Python 3.8 or newer, GCC with OpenMP, and G++. No Make, network access, prebuilt executable, solver, or GPU is required by this runner. Run from the repository root in PowerShell or a POSIX shell:

```sh
python docs/n8/46173/reproduce.py
```

Use `python3` where that is your Python executable. On Windows, install the MSYS2 UCRT64 compilers and keep their directory on `PATH`. Compiler paths can also be supplied explicitly:

```powershell
python docs/n8/46173/reproduce.py --cc C:/msys64/ucrt64/bin/gcc.exe --cxx C:/msys64/ucrt64/bin/g++.exe
```

The runner checks the pinned checksum manifest and every bundled file, then:

1. Builds the C replayer and C++ literal checker from source.
2. Replays the parent and solution plans and compares both words byte-for-byte with the bundled originals.
3. Independently checks the solution's coverage and every single-symbol deletion.
4. Spells the solution again with the Python replayer and compares the bytes.
5. Regenerates the base and its table from the selection and compares both files byte-for-byte.
6. Canonically relabels the solution and compares it with the existing corpus word.

Each run creates a fresh `build/n8-46173/reproduction-<id>/` directory containing executables, generated words, stdout/stderr logs for every command, and `run-summary.json`. The repository ignores this build output. Use `--output-dir PATH` to choose a different, nonexistent directory; existing output directories are refused. A failed build or comparison exits nonzero. The original root ZIP is not required after extraction.

## Verified result

The [repository reproduction](reproduction-summary.json) passed all six stages on October 20, 2026, including exact base-table regeneration and agreement with the canonical corpus word.

| Check | Result |
| --- | --- |
| Parent length | 46,174 |
| Solution length | 46,173 |
| Distinct permutations | 40,320 = 8! |
| Missing permutations | 0 |
| Permutation occurrences | 40,376 |
| Extra occurrences | 56 |
| Single-symbol deletions tested | 46,173 |
| Coverage-preserving single-symbol deletions | 0 |

SHA-256 hashes including the single final LF:

```text
source solution:  9ec23c8c05d60e51786d5fedea27aa3b6b2841c96fe15cf82c6095ecede7b475
canonical corpus: 8acf0fb6ecd633ac43a6b98edf7e9de74f62e987fe0f85c9059ed49008609b81
```

The saved plan has sixteen complete-trail `O` events, including three weight-2 openings. With boundary width 5 and cyclic spelling sum 46,144, the parent pays 25 joining symbols and the solution pays 3 opening symbols plus 21 joining symbols. The net saving is one symbol. No complete trail is omitted or split, and no opening drops a permutation occurrence.

The unchanged standalone package also includes `make search` for the original 60-second randomized experiment. Wall-clock timing makes rediscovery nondeterministic even with the same seed; use the saved solution plan for exact reproduction. Complete coverage and resistance to single-symbol deletion do not prove minimum length.

## Attribution

Halfar supplied the selection, parent word, and search/replay implementation. Pantone supplied the construction and independent literal checker. Their pinned revisions and the scope of the experiment are recorded in the preserved [PROVENANCE.md](../../../data/n8/46173/PROVENANCE.md). Imported code retains its Apache-2.0 terms and upstream notices; see the preserved [LICENSE](../../../data/n8/46173/LICENSE), [NOTICE](../../../data/n8/46173/NOTICE), and repository [third-party notices](../../../THIRD_PARTY_NOTICES.md).
