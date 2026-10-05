# Superpermutation study

A corpus of superpermutation words and C++ tools for inspecting waste and searching for shorter constructions. A superpermutation contains every permutation of its alphabet as a contiguous substring.

## Corpus

[`words/`](words/) groups words by alphabet size, from `5` through `13`. Filenames generally record the word length and sometimes the construction or author. Some files contain collections of words; others are compressed as `.gz`, `.xz`, or `.zip`. Tools that read stdin can consume a decompression pipe; tools that take a filename need an extracted file.

Distinct words imported from the boundary-spectral experiments are archived once in `words/11/`. `words/11/imported-words.json` records their hashes and original paths. Unverified candidates are kept separately in `words/11/candidates/`; they should not be treated as verified superpermutations.

The corpus also includes word submissions from all six open pull requests to [jaypantone/superperm-upper-43-80](https://github.com/jaypantone/superperm-upper-43-80/pulls), checked on October 4, 2026. [`words/pull-request-imports.json`](words/pull-request-imports.json) records pinned commits, source blob hashes, word hashes, and which submissions were already present. Submitted xz archives retain their original compression; plain-text submissions are compressed with the settings below, using their alphabet size as the delta distance. Import checks cover archive integrity, alphabet, and length; they do not independently verify permutation coverage.

| Alphabet size | Newly imported length | Pull request |
| --- | --- | --- |
| 9 | 408,731 | [#1](https://github.com/jaypantone/superperm-upper-43-80/pull/1) |
| 10 | 4,034,873 | [#3](https://github.com/jaypantone/superperm-upper-43-80/pull/3) |
| 11 | 43,930,668 | [#4](https://github.com/jaypantone/superperm-upper-43-80/pull/4) |
| 12 | 522,745,538 | [#5](https://github.com/jaypantone/superperm-upper-43-80/pull/5) |
| 13 | 6,747,918,058 | [#5](https://github.com/jaypantone/superperm-upper-43-80/pull/5) |

[`docs/n11/improve_halfar/`](docs/n11/improve_halfar/) contains reconstruction and exchange reports, including `dependency-hashes.json`, which records the original search dependencies. Experiment reports and replay scripts may still refer to word paths recorded in the import manifest.

### Compression and extraction

Use the following commands in a POSIX shell (Linux, macOS, WSL, or MSYS2 Bash). Binary compression output should not be passed through older PowerShell text pipelines.

The imported N=11 words match the corpus's permutation-specific xz format: delta distance `11`, LZMA2 with a `256 MiB` dictionary, and SHA-256 integrity checks. Existing corpus archives also include plain LZMA2/CRC64 files. The new archives use LZMA2 preset `9`; the original archives do not record their encoder preset.

```sh
# Compress a new N=11 word; keep the original with -k.
xz -k -T1 --check=sha256 --delta=dist=11 --lzma2=preset=9,dict=256MiB word-n11.txt

# Compress stdin directly into an archive.
cat word-n11.txt | xz -T1 --check=sha256 --delta=dist=11 --lzma2=preset=9,dict=256MiB > word-n11-copy.txt.xz

# Extract an xz word to a normal .txt file, keeping its archive.
xz -dk words/11/superpermutation-11-43930667.txt.xz

# Extract other corpus formats, keeping the archives.
gzip -dk words/6/872-treelike.txt.gz
unzip words/7/7_5907_COV.zip -d extracted-7_5907_COV
```

For another alphabet size, set the delta distance to that size. `xz -t archive.txt.xz` checks archive integrity; it does not verify permutation coverage.

## Paint waste

[`tools/reduced_alphabet.cpp`](tools/reduced_alphabet.cpp) builds the `paint-waste` tool. It reads a word from standard input, ignores whitespace, and supports alphabets `1` through `N` for `1 <= N <= 9`.

For each length-`N` window, it marks the final character red if the window contains repeated symbols. It prints the colored word to stdout and statistics to stderr: clean/dirty window counts, longest dirty run, and reduced-alphabet `[depth:index]` pairs (in hexadecimal). A clean window is a permutation; this tool does not check that every distinct permutation is present.

Run these commands from the repository root with a C++20 compiler such as GCC. In PowerShell with MinGW GCC:

```powershell
g++ -std=c++20 -O2 tools/reduced_alphabet.cpp -o paint-waste.exe
Get-Content words/5/153-recursive.txt | ./paint-waste.exe 5
```

On Linux/macOS with GCC:

```sh
g++ -std=c++20 -O2 tools/reduced_alphabet.cpp -o paint-waste
./paint-waste 5 < words/5/153-recursive.txt
```

To use an xz word directly through stdin, without extracting it first (POSIX shell):

```sh
# Make a compressed N=5 example, then pipe it into the tool.
xz -k -T1 --check=sha256 --delta=dist=5 --lzma2=preset=9,dict=256MiB words/5/153-recursive.txt
xz -dc words/5/153-recursive.txt.xz | ./paint-waste 5
```

`-dc` decompresses to stdout and preserves the archive. Paint waste supports only `N <= 9`; the N=11 course-exchange program takes a word filename and needs extraction first.

## Course exchange search

The course-exchange snapshot/search program is currently stored in [`search/course_exchange.cpp`](search/course_exchange.cpp). It targets `N = 11`: it reconstructs an input word as cyclic courses, checks the reconstruction, and searches for savings by changing course openings or exchanging courses.

### Build prerequisites

This source is not standalone. It includes:

```text
boundary-spectral-n11-20261004/coupled_cycle_search.cpp
```

That directory is at the repository root and contains only the four required library sources: `coupled_cycle_search.cpp`, `phase_cut_spectral.cpp`, `boundary_spectral.cpp`, and `construct.cpp`. The include chain is:

```text
course_exchange.cpp -> coupled_cycle_search.cpp -> phase_cut_spectral.cpp
                    -> boundary_spectral.cpp -> construct.cpp
```

Prebuilt executables, old replay scripts, and unrelated experiment outputs are omitted to save space. The pinned model inputs are `data/n11/rows.txt.xz` and `data/n11/circles.txt`; the reproduction script extracts the rows into a temporary directory.

All source and model dependencies are included. [`local-dependencies.json`](docs/n11/improve_halfar/local-dependencies.json) pins their hashes; [`dependency-hashes.json`](docs/n11/improve_halfar/dependency-hashes.json) preserves the original source locations. The three independent checker sources are in `tools/verification/`.

The four-character improvement from Halfar's 43,930,628 word has been reproduced. See the [instructions and run log](docs/n11/improve_halfar/REPRODUCE.md) and [PowerShell script](docs/n11/improve_halfar/reproduce.ps1). The script builds the optimizer and all three checkers from this checkout.

Compile with GCC (the source uses GCC's `__builtin_popcount`):

```powershell
g++ -std=c++20 -O2 search/course_exchange.cpp -o course_exchange.exe
```

On Linux/macOS, use the same command with `-o course_exchange`.

### Usage

```text
course_exchange ROWS CIRCLES WORD FRESH_OUT WINDOW_SIZE SECONDS [MODE]
```

- `ROWS`, `CIRCLES`: matching model input files.
- `WORD`: an uncompressed N=11 word in the model's alphabet.
- `FRESH_OUT`: a new output directory; it must not already exist.
- `WINDOW_SIZE`: number of consecutive courses considered by the default exchange search, from `2` to `8`.
- `SECONDS`: nonnegative search budget; `0` performs reconstruction only. This is not a strict timeout for every mode or preprocessing step.

Examples in PowerShell, using placeholder model and word paths:

```powershell
# Audit the course reconstruction.
./course_exchange.exe rows.txt circles.txt word-n11.txt out-audit 2 0

# Search exchanges of two consecutive courses with a 60-second budget.
./course_exchange.exe rows.txt circles.txt word-n11.txt out-exchange 2 60

# Optimize openings across the entire fixed course order.
./course_exchange.exe rows.txt circles.txt word-n11.txt out-global 2 60 --global-all-phases
```

Optional modes:

| Mode | Search |
| --- | --- |
| No flag | Single-course phase improvements, then local course exchanges. |
| `--pair-swaps` | Two-site course swaps with constituent and all-phase openings. |
| `--occupation-swaps` | Pair swaps that also use extra copies of permutations within their owning course. |
| `--adjacent-all-phases` | Adjacent pairs, trying both orders and all available openings. |
| `--global-all-phases` | Global opening optimization with the course order fixed. |

The program writes reconstruction reports, mode-specific JSON/JSONL logs, and candidate `.txt` words when improvements are found. Search proceeds only after byte-exact reconstruction and requires each course to occur once. Independently verify permutation coverage before treating a candidate as a valid improved superpermutation.
