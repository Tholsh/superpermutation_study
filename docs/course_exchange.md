# Course exchange: build and run

`search/course_exchange.cpp` is the N=11 search entry point. `boundary_transfer.cpp` supplies the row model, boundary ports, overlap costs, and exact transfer calculations used by the search. Its former name was `boundary_spectral.cpp`; the library directory keeps its historical name for provenance.

## Build

Use GNU Make and 64-bit GCC (the libraries require `__int128` and `__builtin_popcount`). From the repository root in PowerShell with MSYS2/MinGW:

```powershell
mingw32-make course_exchange checkers
./build/course_exchange.exe
```

The command without arguments prints usage and exits with an error. On Linux, macOS, or MSYS2 Bash with GNU Make:

```sh
make course_exchange checkers
./build/course_exchange
```

`make` alone builds the optimizer. `checkers` builds the three independent verification tools; `paint-waste` optionally builds the paint tool with C++20. `boundary_transfer` builds the renamed library's standalone boundary-spectrum analysis program. Outputs and generated dependency files stay in the ignored `build/` directory. `make clean` removes only these named outputs. On Windows, use `mingw32-make` in place of `make`.

The default optimizer/checker flags are `-O3 -std=c++17`. Override the compiler or flags, for example:

```powershell
mingw32-make -B course_exchange 'CXX=C:/msys64/ucrt64/bin/g++.exe' 'CXXFLAGS=-O0 -g -std=c++17'
```

Use `-B` when changing compiler flags to force a rebuild. Ordinary builds automatically rebuild when an included library changes. The libraries are included into one translation unit and must not be linked as separate objects:

```text
course_exchange.cpp -> coupled_cycle_search.cpp -> phase_cut_spectral.cpp
                    -> boundary_transfer.cpp -> construct.cpp
```

All four library sources are in `boundary-spectral-n11-20261004/`. The model inputs are `data/n11/rows.txt.xz` and `data/n11/circles.txt`. [Local dependency hashes](n11/improve_halfar/local-dependencies.json) pin current sources and data; the [historical manifest](n11/improve_halfar/dependency-hashes.json) preserves their original locations.

## Run

```text
course_exchange ROWS CIRCLES WORD FRESH_OUT WINDOW_SIZE SECONDS [MODE]
```

- `ROWS`, `CIRCLES`: matching model input files; extract the rows first.
- `WORD`: an uncompressed N=11 word in the model's alphabet.
- `FRESH_OUT`: a new output directory that must not already exist.
- `WINDOW_SIZE`: number of consecutive courses considered by the default exchange search, from 2 to 8.
- `SECONDS`: nonnegative search budget; 0 performs reconstruction only. This is not a strict timeout for every mode or preprocessing step.

Examples in PowerShell with extracted inputs:

```powershell
# Audit the reconstruction.
./build/course_exchange.exe rows.txt circles.txt word-n11.txt out-audit 2 0
# Search two-course exchanges with a 60-second budget.
./build/course_exchange.exe rows.txt circles.txt word-n11.txt out-exchange 2 60
# Optimize openings across the fixed course order.
./build/course_exchange.exe rows.txt circles.txt word-n11.txt out-global 2 60 --global-all-phases
```

| Mode | Search |
| --- | --- |
| No flag | Single-course phase improvements, then local course exchanges. |
| `--pair-swaps` | Two-site swaps with constituent and all-phase openings. |
| `--occupation-swaps` | Pair swaps using extra permutation copies within their owning course. |
| `--adjacent-all-phases` | Adjacent pairs, trying both orders and all openings. |
| `--global-all-phases` | Global opening optimization with the course order fixed. |

The program writes reconstruction reports, mode-specific JSON/JSONL logs, and candidate `.txt` words when improvements are found. Search begins after byte-exact reconstruction and requires each course to occur once. Independently verify candidate coverage before treating a candidate as an improved superpermutation.

The [full reproduction guide](n11/improve_halfar/REPRODUCE.md) and [PowerShell script](n11/improve_halfar/reproduce.ps1) reproduce the four-character saving from Halfar's 43,930,628 word, building the optimizer and all three checkers through this Makefile.
