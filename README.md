# Superpermutation study

A corpus of superpermutation words and C++ tools for inspecting waste and searching for shorter constructions. A superpermutation contains every permutation of its alphabet as a contiguous substring.

## Corpus

[`words/`](words/) groups words by alphabet size, from `5` through `13`, then by word length: `words/N/LENGTH/`. For example, the recursive N=5 word is [`words/5/153/153-recursive.txt`](words/5/153/153-recursive.txt). Through **N=9**, every `.txt` file contains exactly one superpermutation, using one-based labels `123…N`. Collections retain their own folders inside the length folder, such as `words/6/872/872-treelike/872-00001.txt` (length and source ordinal). Existing individual word filenames are retained. Repeated occurrences from different sources are preserved.

Author notes and cycle descriptions live in [`data/corpus/`](data/corpus/), outside the word files. The [normalization manifest](data/corpus/normalization-n1-n9.json) records source hashes, collection order, relocated metadata, and full permutation-coverage validation. N=10 and above retain their original labels and compression; check the import manifests and use `-z` for zero-based words. Tools that read stdin can consume a decompression pipe; tools that take a filename need an extracted file.


[`docs/n11/improve_halfar/`](docs/n11/improve_halfar/) contains reconstruction and exchange reports, including `dependency-hashes.json`, which records the original search dependencies. Experiment reports and replay scripts may still refer to word paths recorded in the import manifest.

## Math

You can find the writeup in [`docs/n11/improve_halfar/math/`](docs/n11/improve_halfar/math/)

## Compression and extraction

Use the following commands in a POSIX shell (Linux, macOS, WSL, or MSYS2 Bash). Binary compression output should not be passed through older PowerShell text pipelines.

The imported N=11 words match the corpus's permutation-specific xz format: delta distance `11`, LZMA2 with a `256 MiB` dictionary, and SHA-256 integrity checks. Existing corpus archives also include plain LZMA2/CRC64 files. The new archives use LZMA2 preset `9`; the original archives do not record their encoder preset.

```sh
# Compress a new N=11 word; keep the original with -k.
xz -k -T1 --check=sha256 --delta=dist=11 --lzma2=preset=9,dict=256MiB word-n11.txt

# Compress stdin directly into an archive.
cat word-n11.txt | xz -T1 --check=sha256 --delta=dist=11 --lzma2=preset=9,dict=256MiB > word-n11-copy.txt.xz

# Extract an xz word to a normal .txt file, keeping its archive.
xz -dk words/11/43930667/superpermutation-11-43930667.txt.xz

# N <= 9 collections are already split into individual text files.
head -c 80 words/6/872/872-treelike/872-00001.txt
```

For another alphabet size, set the delta distance to that size. `xz -t archive.txt.xz` checks archive integrity; it does not verify permutation coverage.

## Relabel word files

[`tools/relabel_words.py`](tools/relabel_words.py) converts between zero-based `0123456789ABC` and one-based `123456789ABCD` labels using Python 3.8 or newer. `--to 0` expects one-based input; `--to 1` expects zero-based input. Each uppercase letter is one symbol (`9` becomes `A` when converting to one-based labels). Whitespace, line endings, word length, and filenames are preserved. Optionally use `-n N` to validate the source alphabet size; the default is 13. Only word symbols and ASCII whitespace are accepted.

```powershell
# A single file, in either direction; write to a different output file.
python tools/relabel_words.py --to 0 -n 3 one-based.txt zero-based.txt
python tools/relabel_words.py --to 1 -n 3 zero-based.txt restored.txt
# Convert every .txt file recursively, retaining relative subdirectories.
./tools/relabel-folder.ps1 -To 0 -N 5 -Source words/5 -Destination converted-zero -DryRun
./tools/relabel-folder.ps1 -To 0 -N 5 -Source words/5 -Destination converted-zero
./tools/relabel-folder.ps1 -To 1 -N 5 -Source converted-zero -Destination converted-one
```

For Bash (Linux, macOS, WSL, or MSYS2):

```sh
bash tools/relabel-folder.sh --to 0 -n 5 --dry-run words/5 converted-zero
bash tools/relabel-folder.sh --to 0 -n 5 words/5 converted-zero
bash tools/relabel-folder.sh --to 1 -n 5 converted-zero converted-one
# Stream a compressed zero-based N=11 word into a one-based text file.
xz -dc words/11/43930624/superpermutation-11-43930624.txt.xz | python3 tools/relabel_words.py --to 1 -n 11 > one-based-n11.txt
```

For example, `123121321` becomes `012010210` and converts back exactly. Folder conversion processes plain `.txt` files only, skips symlinks, and requires separate, non-nested input/output folders. Extract compressed archives first. `--dry-run` lists planned conversions without checking word contents. Existing outputs are refused unless you pass `--overwrite` (PowerShell: `-Overwrite`). File outputs are published only after complete validation; a failed file leaves no partial output. A folder run stops at the first error, retaining already completed files. Stream output can contain a valid prefix before an input error, so check the exit status. Run `python tools/relabel_words.py --help` for all options; PowerShell accepts `-Python PATH`, and Bash accepts a `RELABEL_PYTHON` environment override.

## Paint waste

[`tools/reduced_alphabet.cpp`](tools/reduced_alphabet.cpp) builds the `paint-waste` tool. It reads a word from standard input, ignores whitespace, and supports `1 <= N <= 13` on a 64-bit platform. Its default labels are `123456789ABCD`; `-z` / `--zero-based` selects `0123456789ABC`. Use the first N characters of the selected alphabet, with uppercase letters.

For each length-`N` window, it marks the final character red if the window contains repeated symbols. It prints the colored word, reduced-alphabet `[depth:index]` pairs (in hexadecimal), and then decimal statistics to stdout. Statistics include length, clean/dirty windows and runs, distinct/missing permutations, and binary `valid_superpermutation` coverage. Use `-s` to print only statistics. See the [full run guide and field definitions](docs/reduced_alphabet.md).

Run these commands from the repository root with a C++20 compiler such as GCC. In PowerShell with MinGW GCC:

```powershell
g++ -std=c++20 -O2 tools/reduced_alphabet.cpp -o paint-waste.exe
Get-Content words/5/153/153-recursive.txt | ./paint-waste.exe 5
```

A concrete coverage check, showing four fields from the statistics-only output:

```powershell
'123121321' | ./paint-waste.exe -s 3 | Select-String '^(length|distinct_permutations|missing_permutations|valid_superpermutation):'
```

```text
length: 9
distinct_permutations: 6
missing_permutations: 0
valid_superpermutation: 1
```

Validity `1` means all `N!` distinct permutations occur. A completed analysis exits successfully even when validity is `0`; inspect that field when validating a word.

Use `-m` to mark dirty characters as `[X]` instead of using color. The reduced alphabet and statistics keep exactly the same format:

```powershell
'123121321' | ./paint-waste.exe -m 3
# Painted word: 12312[1]321
```

`-s -m` prints only the usual statistics, since `-s` suppresses the word.

For the zero-based version of the same valid word:

```powershell
'012010210' | ./paint-waste.exe -z -s 3
```

Above N=9, the tool always uses statistics-only output. Without `-s`, it asks for confirmation through the terminal; explicit `-s` accepts that mode without prompting. If no terminal is available, rerun with `-s`. Large words are streamed; exact coverage at N=13 needs about 742 MiB of RAM. See the [full run guide](docs/reduced_alphabet.md) for alphabet and confirmation details.

On Linux/macOS with GCC:

```sh
g++ -std=c++20 -O2 tools/reduced_alphabet.cpp -o paint-waste
./paint-waste 5 < words/5/153/153-recursive.txt
```

To use an xz word directly through stdin, without extracting it first (POSIX shell):

```sh
# Make a compressed N=5 example, then pipe it into the tool.
xz -k -T1 --check=sha256 --delta=dist=5 --lzma2=preset=9,dict=256MiB words/5/153/153-recursive.txt
xz -dc words/5/153/153-recursive.txt.xz | ./paint-waste 5
```

`-dc` decompresses to stdout and preserves the archive. To validate a zero-based N=11 corpus word directly:

```sh
xz -dc words/11/43930624/superpermutation-11-43930624.txt.xz | ./paint-waste -z -s 11
```

The N=11 course-exchange program takes a word filename and needs extraction first.

## Course exchange search

[`search/course_exchange.cpp`](search/course_exchange.cpp) reconstructs an N=11 word as cyclic courses and searches for savings by changing openings or exchanging courses. Build from the repository root with GNU Make and 64-bit GCC:

```powershell
mingw32-make course_exchange
./build/course_exchange.exe rows.txt circles.txt word-n11.txt out-audit 2 0
```

On Linux/macOS, use `make course_exchange` and `./build/course_exchange`. See the [build and run guide](docs/course_exchange.md) for inputs, search modes, and checkers, or the [complete reproduction](docs/n11/improve_halfar/REPRODUCE.md) for the four-character improvement from Halfar's word.

## License

Our software is free software under the **GNU General Public License, version 3 or later (GPL-3.0-or-later)**. You may use, study, modify, and redistribute it under those terms. Distributed derivatives must preserve the GPL freedoms and provide the corresponding source as required by the license. It comes without warranty. See [LICENSE](LICENSE) for the full terms.

Imported code retains its upstream terms and attribution; see [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md). Corpus words and imported documents retain their authorship.
