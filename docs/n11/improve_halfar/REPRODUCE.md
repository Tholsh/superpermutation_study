# Reproducing the N11 course exchange optimization

The repository now includes all source and model files needed to reproduce the reduction from Halfar's 43,930,628-character word to 43,930,624 characters. The optimizer and three independent checkers are built from source. No external `Superperm/research` checkout or prebuilt checker is required.

## Included dependencies

| Repository path | Purpose |
| --- | --- |
| `search/course_exchange.cpp` | Optimizer entry point. |
| `boundary-spectral-n11-20261004/coupled_cycle_search.cpp` | Coupled course routines. |
| `boundary-spectral-n11-20261004/phase_cut_spectral.cpp` | Course phase routines. |
| `boundary-spectral-n11-20261004/boundary_spectral.cpp` | Model and boundary routines. |
| `boundary-spectral-n11-20261004/construct.cpp` | Pinned upstream constructor helpers. |
| `data/n11/rows.txt.xz` | Pinned model rows, compressed from 6,422,995 to 375,940 bytes. |
| `data/n11/circles.txt` | Matching connector circles. |
| `tools/verification/literal_check.cpp` | Literal permutation coverage checker. |
| `tools/verification/verify_standalone.cpp` | Independent inversion-rank checker. |
| `tools/verification/verify_sorted.cpp` | Independent packed-window sorting checker. |

Paths above are relative to the repository root. [local-dependencies.json](local-dependencies.json) pins their SHA-256 hashes. [dependency-hashes.json](dependency-hashes.json) preserves the historical external paths and hashes; those paths are no longer required. The only change to the imported optimizer library is making `boundary_spectral.cpp` include the local `construct.cpp`. The constructor helpers and model data retain their original contents.

The library folder contains only its four required C++ sources. Old experiment directories, replay scripts, binaries, and duplicate input archives have been removed. Relevant reconstruction and optimization evidence remains in this documentation folder; words remain in the corpus.

## Run the complete reproduction

From the repository root, in PowerShell:

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File docs/n11/improve_halfar/reproduce.ps1
```

Defaults are GCC at `C:\msys64\ucrt64\bin\g++.exe` and Python at `C:\msys64\ucrt64\bin\python.exe`. Override them for another installation:

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File docs/n11/improve_halfar/reproduce.ps1 -Compiler 'D:\msys64\ucrt64\bin\g++.exe' -Python 'D:\msys64\ucrt64\bin\python.exe'
```

The script checks required paths and pinned hashes, builds the optimizer and all three checkers, and extracts the rows and baseline word using Python's `lzma` module with binary I/O. It creates a fresh temporary working directory and a fresh `reproduction-<id>` report directory beside this document. Executables, extracted inputs, and the generated word stay in the temporary directory. Only small reports are copied into the repository; existing runs are not overwritten.

Use 64-bit GCC: the libraries use `__int128` and the optimizer uses `__builtin_popcount`. GCC 13.1.0 from MSYS2 was used here. Cached openings alone occupy 958,454,784 bytes, with additional RAM needed for inputs, course ownership, traceback, and hash tables.

## Exact commands and inputs

With the variables initialized by [reproduce.ps1](reproduce.ps1), the build and optimization are:

```powershell
& $Compiler -O3 -std=c++17 $usedFiles[0] -o $binaryPath
& $binaryPath $rowsPath $circlesPath $inputPath $outputDir 2 900 --global-all-phases
```

The script also builds each source in `tools/verification/` with `-O3 -std=c++17`. C++17 matches the original optimizer build; the paint-waste tool separately requires C++20. `2` satisfies the window-size argument requirement. `900` enables optimization, but the global mode does not enforce it as a strict timeout. The output directory must not already exist.

The baseline archive is `words/11/superpermutation-11-43930628.txt.xz`. Its extracted SHA-256 is:

```text
784c892b81283ece13f5b1ef8c49d13b0bcb4d3c1ec49882e5593f034e86b596
```

The extracted rows must match:

```text
99f7f9aac8f970126a1eb7668cbc5d0e5b6d9f362611f1258c44305eb2a3a015
```

Use the 43,930,628-character baseline to reproduce the saving. Starting from the already improved 43,930,624 word is a different experiment.

The optimizer reconstructs the baseline byte for byte as 2,800 cyclic courses, then enumerates 39,935,616 literal openings. Extra copies within a course can shorten the wrapping prefix needed to cover its assigned permutations. A global dynamic program jointly chooses openings and maximal literal overlaps, keeping the course order fixed. It does not search arbitrary course orders or prove global minimality.

## Verification and results

The generated candidate is `global-phase-n11-43930624.txt`. The script runs:

```powershell
& $literalChecker 11 0123456789A $candidatePath
& $inversionChecker 11 0123456789A $candidatePath 43930624
& $sortedChecker 11 0123456789A $candidatePath 43930624 (Join-Path $reportDir 'independent-sorted.json')
Get-FileHash -Algorithm SHA256 -LiteralPath $candidatePath
```

Success requires all three checkers to exit zero and the output to have this SHA-256:

```text
0f3b2dcf607aaf3e7985c9daf2d87c07f8947522490dfea90b05a90c7fd5aa6b
```

Expected coverage is 39,916,800 distinct permutations, zero missing, 39,935,616 occurrences, and 18,816 repeats. The output is 43,930,624 bytes without a final newline, saving four characters.

The earlier [external-dependency run](reproduction-af6cd7ba0e304f5a9f8da3ae81f59c2c/run-summary.json) matched that result with a 57.5-second solve. The new [run using repository sources](reproduction-3c6a701841e14280bd021d1959d07263/run-summary.json) also reproduced the exact output hash and passed all three checkers, with a solve time of approximately 63.2 seconds. Each run contains `optimization.log`, reconstruction reports, the global phase schedule and summary, three independent coverage reports, dependency/tool hashes, and `run-summary.json` with the actual candidate path and input/output hashes.

Temporary files may be removed after inspection. The report directory retains the reproducibility evidence without storing another uncompressed corpus word or any executables.
