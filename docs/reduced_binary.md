# Reduced-alphabet binary codec

`tools/reduced_codec.cpp` builds `reduced-codec`, a reversible first pass for xz
or another general-purpose compressor. Select `--bits 4` (the default) or
`--bits 6` for both fields: unsigned clean-run depth and signed copy offset.
Tuples occupy **8 or 12 packed bits**, respectively. The header identifies the
version, layout, alphabet, and word length; decode detects the field width.

Both commands write their result to **stdout**. The encoder writes raw binary;
the decoder writes word symbols with **no final newline**. Neither command opens
an output filename or asks for terminal confirmation. Redirect stdout or pipe it
to another program; otherwise the output goes to the terminal. Success is quiet.
Errors go to stderr and return status 1; success returns 0.

## Build and run

From the repository root, with a C++20 compiler:

```sh
g++ -std=c++20 -O2 -Wall -Wextra -pedantic tools/reduced_codec.cpp -o reduced-codec
./reduced-codec encode 5 words/5/153/153-recursive.txt > word-n5.spra
./reduced-codec encode --bits 6 5 words/5/153/153-recursive.txt > word-n5-six.spra
./reduced-codec decode word-n5.spra > restored-n5.txt
```

The interface is:

```text
reduced-codec encode [--bits 4|6] [-z|--zero-based] N [INPUT|-]
reduced-codec decode [INPUT|-]
```

Omitting `INPUT`, or using `-`, reads stdin. `N` must be between 1 and 32. The
encoder also accepts `--bits=6` and `--bits=4`; options may appear before or after
N. Decode reads N, the field width, and the alphabet mode from the header; it takes
none of those flags. Four-bit output remains byte-for-byte compatible with
existing version-1 files. An older decoder rejects the new `0x66` layout.

Input labels are the first N characters of `123456789ABCDEFGHIJKLMNOPQRSTUVW`, or
`0123456789ABCDEFGHIJKLMNOPQRSTUV` with `-z`. Each uppercase letter is one
symbol. The encoder ignores ASCII spaces, tabs, CR, LF, form feeds, and vertical tabs, and rejects all
other bytes outside the chosen alphabet. Decode restores those same labels in a
single word; it does not restore whitespace. Several input lines are concatenated,
so supply one word per invocation. Coverage of all N! permutations is not checked.

For stdin and a zero-based word, in a POSIX shell:

```sh
printf '012010210\n' | ./reduced-codec encode -z 3 > word-n3.spra
./reduced-codec decode < word-n3.spra > restored-n3.txt
```

### PowerShell / Windows

Build the executable in PowerShell, then use `cmd /c` for byte-preserving
redirection. This avoids the text conversions in older PowerShell native-command
pipelines and redirects. The program itself sets its streams to binary mode on
Windows, including when binary input arrives on stdin.

```powershell
g++ -std=c++20 -O2 -Wall -Wextra -pedantic tools/reduced_codec.cpp -o reduced-codec.exe
cmd /c '.\reduced-codec.exe encode 5 words\5\153\153-recursive.txt > word-n5.spra'
if ($LASTEXITCODE -ne 0) { throw 'Encoding failed; discard word-n5.spra.' }
cmd /c '.\reduced-codec.exe decode word-n5.spra > restored-n5.txt'
if ($LASTEXITCODE -ne 0) { throw 'Decoding failed; discard restored-n5.txt.' }
# Select six-bit fields; decode uses the same command for either layout.
cmd /c '.\reduced-codec.exe encode --bits 6 5 words\5\153\153-recursive.txt > word-n5-six.spra'
```

Quote paths containing spaces inside the command string:

```powershell
cmd /c '.\reduced-codec.exe encode 5 "input word.txt" > "packed word.spra"'
cmd /c '.\reduced-codec.exe decode "packed word.spra" > "restored word.txt"'
```

Do not pass `.spra` data through `Get-Content`, `Out-File`, or a text encoding.
Redirection creates or truncates the destination before the program runs, so use
different input and output paths and check the exit status before keeping a file.

## Converted N=9 corpus

All seven records under `words/9/` have `.spra` and `.spra.xz` copies alongside
their original `.txt` files, keeping the same base filenames. Every word fits
version 1, layout `0x44`: four-bit depth and offset fields, with one-based labels.
The original text files and their whitespace are preserved.

| Representation, all seven records | Total bytes |
| --- | ---: |
| Original text files | 2,861,987 |
| Normalized word symbols | 2,861,975 |
| `.spra` binaries | 320,639 |
| `.spra.xz` archives, default xz | 4,360 |

Every saved archive was decompressed, compared with its binary copy, and decoded
back to the normalized source word. The [conversion manifest](../data/corpus/reduced-n9.json)
records source and output hashes, lengths, tuple counts, and verification results.

Restore a raw binary in PowerShell:

```powershell
cmd /c '.\reduced-codec.exe decode words\9\408731\superpermutation-9-408731.spra > restored-n9.txt'
```

Or restore an xz archive in a POSIX shell:

```sh
set -o pipefail
xz -dc words/9/408731/superpermutation-9-408731.spra.xz |
  ./reduced-codec decode > restored-n9.txt
```

The restored file has no whitespace or final newline. N and the field width are
read from the binary header.

## Put xz after the first pass

Use plain `xz` with its default settings. Compression needs no preset, filter,
dictionary, threading, or checksum arguments. In a POSIX shell:

```sh
set -o pipefail
./reduced-codec encode 5 words/5/153/153-recursive.txt | xz > word-n5.spra.xz
xz -d < word-n5.spra.xz | ./reduced-codec decode > restored-n5.txt
```

For an existing zero-based xz corpus word:

```sh
xz -dc words/11/43930624/superpermutation-11-43930624.txt.xz |
  ./reduced-codec encode -z 11 | xz > word-n11.spra.xz
```

In PowerShell, after saving `word-n5.spra` with the commands above:

```powershell
cmd /c 'xz < word-n5.spra > word-n5.spra.xz'
cmd /c 'xz -d < word-n5.spra.xz > unpacked-n5.spra'
cmd /c '.\reduced-codec.exe decode unpacked-n5.spra > restored-n5.txt'
```

Check command exit statuses and discard incomplete results on failure. `xz` is
an external second pass. Compare the complete `.spra.xz` file, including its
header and seed, with xz applied directly to the same normalized word.

### Measured comparisons with default xz

These measurements were rerun with **xz (XZ Utils) 5.4.3**, invoking `xz` without
compression arguments. Both inputs have ASCII whitespace removed. Every direct
xz archive was decompressed and checked against the word's SHA-256. Each encoded
archive was decompressed, checked against the binary, decoded, and checked
against the normalized word. All successful round trips matched.

The input corpus archives are decompressed first. Their existing archive sizes
are not the baseline: the direct column recompresses the words with plain xz.
Results can differ between xz versions. All sizes below are bytes.

| N | Word length | Direct xz | Four-bit + xz | Six-bit + xz |
| ---: | ---: | ---: | ---: | ---: |
| 1 | 1 | 60 | 76 | 76 |
| 2 | 3 | 60 | 76 | 76 |
| 3 | 9 | 68 | 84 | 84 |
| 4 | 33 | 88 | 88 | 92 |
| 5 | 153 | 132 | 96 | 104 |
| 6 | 872 | 308 | 140 | 156 |
| 7 | 5,913 | 640 | 132 | 156 |
| 8 | 46,181 | 3,420 | 264 | 320 |
| 9 | 408,731 | 23,564 | 856 | 1,152 |
| 10 | 4,034,889 | 204,820 | 5,192 | 6,952 |
| 11 | 43,930,624 | 1,968,180 | 45,752 | 57,412 |

N=1..4 use recursive words. The corpus examples are `153-recursive`,
`872-treelike/872-00001`, `5913-palindromic`, `superperm8_46181_1`,
`superperm9_408731_19_canonical`, `superpermutation-10-4034889`, and
`superpermutation-11-43930624`. N=10 and N=11 use zero-based labels.

The transform increases or ties compressed size on the tiny N=1..4 examples and
starts winning at N=5 in this sample. On all seven selected N=5..11 words,
six-bit output compresses larger than four-bit output. It provides more range.
These are construction-dependent measurements.

### Full N=11 example

The [43,930,624-symbol word](../words/11/43930624/superpermutation-11-43930624.txt.xz)
contains 3,994,998 tuples. Before xz, the four-bit file is 3,995,032 bytes and the
six-bit file is 5,992,531 bytes. With default xz they become **45,752** and
**57,412** bytes, respectively; direct xz takes **1,968,180** bytes. Six-bit xz
output is about 25.5% larger than four-bit output on this word.

Both layouts decode to this normalized SHA-256:

```text
0f3b2dcf607aaf3e7985c9daf2d87c07f8947522490dfea90b05a90c7fd5aa6b
```

### N=13 prefix beyond the four-bit range

The **first 16 MiB only** of
`words/13/6747918058/superpermutation-13-6747918058.txt.xz` gives:

| Representation | Bytes |
| --- | ---: |
| Normalized word prefix | 16,777,216 |
| Direct xz | 660,684 |
| Four-bit codec | Rejected: offset +10 at symbol 9,374,975 |
| Six-bit binary | 1,949,766 |
| Six-bit binary + xz | 736 |

The six-bit archive round trip matches the whole tested prefix, including the
later offset -10. This does not test the complete N=13 word or its permutation
coverage.

### Reproduce the measurements

[`tools/benchmark_reduced_codec.py`](../tools/benchmark_reduced_codec.py) accepts
plain or `.xz` input, compares direct xz with both layouts, verifies round trips,
and reports JSON to stdout. It uses bounded memory and temporary files. Build
the codec and make sure `xz` is on PATH, then run:

```sh
python tools/benchmark_reduced_codec.py 8 words/8/46181/superperm8_46181_1.txt
python tools/benchmark_reduced_codec.py -z 11 words/11/43930624/superpermutation-11-43930624.txt.xz
python tools/benchmark_reduced_codec.py -z --prefix-bytes 16777216 13 words/13/6747918058/superpermutation-13-6747918058.txt.xz
```

Use `--codec PATH` for another executable or `--bits 6` to measure only that
layout. A rejected layout is reported with its error. The script clears
`XZ_DEFAULTS` and `XZ_OPT` for its child processes so environment overrides do
not change the default settings. The runs above used Python 3.10.12.

The [complete measurement report](reduced_xz_benchmarks.json) records source
paths, normalized lengths and hashes, raw and compressed sizes, xz version, and
round-trip results.

### Normalized 3+5 experiment

A three-bit literal depth reaches only 7. An alternative is to use those bits
as an index into an N-relative table:

```text
depth_table = [0, N-3, N-2, N-1, N, N+1, N+2, N+3]
ordinary_byte = (depth_code << 5) | (signed_offset & 31)
```

The five-bit signed offset covers -16..+15. An escape is needed for other depths,
farther references, or dirty symbols without an earlier occurrence. In this
experiment byte `0x80` is the escape: ordinarily it would mean depth N followed
by offset zero, which would produce a clean window and therefore cannot be an
ordinary dirty tuple. The escape carries an unsigned LEB128 actual depth followed
by a one-byte literal symbol ID. This also handles first appearances and long
copy distances without retaining the entire decoded history. Symbol IDs up to
31 suffice for N=32; wider header counts and position counters are still needed.

For the complete N=11 example, seven of 3,994,998 tuples have depths outside the
table. A trial serialization with those seven escapes has 3,995,046 bytes and
compresses to 45,760 bytes with plain xz, versus 3,995,032 and 45,752 bytes for
the current 4+4 format. The trial parser checked every reconstructed dirty symbol
against the original word, and the xz round trip preserved the trial bytes.
This was rerun with the same default xz settings as the main measurements.
It is an exploratory format, not implemented by `reduced-codec`; the trial uses
a hypothetical version-2 `0x35` header and remains separate from the implemented
4+4 and 6+6 layouts.

## Tuple semantics

The encoder retains the first `min(word_length, N-1)` symbols as a seed. Starting
at the next symbol, it classifies length-N windows as clean (all symbols distinct)
or dirty (some symbol repeated), just like `paint-waste`.

For every dirty window it emits:

```text
high B bits: depth     number of clean windows since the preceding dirty window
low B bits: offset     signed B-bit two's complement (B = 4 or 6)
```

The first depth counts clean windows starting with the first length-N window;
consecutive dirty windows have depth zero. The offset is relative to the copy
position N symbols ago. If the next output position is `t` (zero-based) and the
referenced earlier position is `r`, then:

```text
offset = r - (t - N) = N - copy_distance
copy_distance = N - offset
```

The encoder references the **nearest earlier occurrence** of the dirty symbol.
The decoder accepts any available backward reference with the encoded distance
that produces a dirty window. It first generates `depth` clean symbols, then
copies the referenced symbol.

Each clean step is unique: emit the alphabet symbol missing from the preceding
N-1 symbols. Once a clean window is established, further clean steps are simple
distance-N copies. A clean step after a repeated N-1-symbol suffix is invalid.
After all tuples, the decoded length specifies how many trailing clean symbols
remain. No trailing-run tuple is stored.

Two's complement is decoded as `low < 2^(B-1) ? low : low - 2^B`.
For four-bit fields, for example:

| Low nibble | Signed offset | Copy distance |
| --- | ---: | --- |
| `0x7` | +7 | N-7 |
| `0x1` | +1 | N-1 |
| `0x0` | 0 | N |
| `0xF` | -1 | N+1 |
| `0x8` | -8 | N+8 |

Zero is an ordinary offset in version 1. An all-zero tuple is ordinary in either
layout (`0x00` in 4+4, twelve zero bits in 6+6).
There are no cycle macros, repeat markers, or extension opcodes in this version.
The tuple count provides framing; a zero byte does not terminate the body.

The signed binary offset differs from the historical displayed index in
`paint-waste`: that index is a bounded lookback diagnostic with its own indexing
convention and zero fallback. Do not pack the printed pairs directly into this
format.

## Version 1 wire format

All multibyte integers are **unsigned 64-bit little-endian**, independent of the
host. Offsets in this table are byte offsets from the beginning of the file.

| Offset | Size | Field |
| ---: | ---: | --- |
| 0 | 4 | ASCII magic `SPRA` (`53 50 52 41` in hex). |
| 4 | 1 | Format version: `0x01`. |
| 5 | 1 | Tuple layout: `0x44` (four bits per field) or `0x66` (six bits per field). |
| 6 | 1 | Flags: bit 0 selects zero-based labels; all other bits must be zero. |
| 7 | 1 | N, stored directly as an integer from 1 through 32. |
| 8 | 8 | Decoded symbol count, excluding whitespace. |
| 16 | 8 | Tuple count. |
| 24 | `min(decoded_length, N-1)` | Seed symbol IDs, one byte each, in `0..N-1`. |
| After seed | `ceil(2 * B * tuple_count / 8)` | Packed tuples in order, B given by the layout. |

The exact file size is `24 + min(decoded_length, N-1) + body_bytes`. The body is
`tuple_count` bytes for 4+4, or `3 * floor(tuple_count / 2) + 2 * (tuple_count % 2)`
bytes for 6+6. Empty words have just a 24-byte header. N=1 needs no seed and no
tuples; its length alone
determines the word. Decode rejects unknown versions/layouts, reserved flags,
invalid seeds or references, impossible clean/dirty steps, nonzero padding,
missing bytes, tuples that exceed the decoded length, and extra bytes after the body. It handles one
file per invocation; concatenated `.spra` files are not accepted.

The tuple body is a most-significant-bit-first stream, separate from the
little-endian header counters. For B=6 each tuple is the 12-bit value
`(depth << 6) | (offset & 63)`. Two successive values `a`, `b` occupy:

```text
a >> 4, ((a & 15) << 4) | (b >> 8), b & 255
```

An odd final value `a` occupies `a >> 4, (a & 15) << 4`: the unused low four bits
must be zero. Tuple count determines how many values to read, so padding cannot
be confused with another tuple. No padding is needed for B=4.

For `123121321` at N=3, the full file is:

```text
53 50 52 41 01 44 00 03   magic, version, layout, flags, N
09 00 00 00 00 00 00 00   decoded length = 9
01 00 00 00 00 00 00 00   tuple count = 1
00 01                     seed IDs for "12"
31                        depth 3, offset +1 (distance 2)
```

Decode produces seed `12`, three clean steps `312`, dirty copy `1`, and three
trailing clean steps `321`, yielding `123121321`.

With `--bits 6`, the same word has layout byte `66` and tuple bytes `0C 10`
instead of `31`. Its file size is 28 bytes. The decoded tuple is still depth 3,
offset +1.

## Range limits and failure behavior

Both layouts have **strict field limits**; neither encodes every possible word.

| `--bits` | Tuple bits | Recorded depth | Signed offset | Allowed copy distance |
| ---: | ---: | ---: | ---: | --- |
| 4 | 8 | 0..15 | -8..+7 | `max(1, N-7)..N+8` |
| 6 | 12 | 0..63 | -32..+31 | `max(1, N-31)..N+32` |

A word is encodable only when every recorded depth fits, every dirty symbol has
an earlier occurrence, and its nearest-reference offset fits the selected
range. N in the header does not guarantee that every construction at that N fits.
A first appearance inside a dirty window cannot be represented by a copy
reference and is rejected too. Four-bit mode remains the default; the encoder
does not retry with six-bit fields automatically.

Trailing clean runs can be arbitrarily long because they are represented by the
decoded length. A clean run longer than 15 or 63, respectively, **before a dirty
symbol** is rejected. Values never wrap or truncate to fit. Zero-offset escapes
and cycle macros are not implemented.

At N=32, six-bit mode supports copy distances 1..64, but still rejects longer
recorded runs and farther references. Header counts and position counters remain
unsigned 64-bit: words cannot exceed `2^64-1` symbols. A complete N=32
superpermutation would require at least 32! windows, whose count needs 118 bits;
even 21! exceeds the current length field. Supporting the N=32 alphabet therefore
does not mean this format can store a complete superpermutation at that N.

### Concrete four-bit N=13 failure

In `words/13/6747918058/superpermutation-13-6747918058.txt.xz`, the encoder first
rejects symbol 9,374,975 (one-based): its nearest occurrence is three positions
back, giving offset `13-3 = +10`. An older occurrence 16 positions back could
encode that particular symbol with offset -3; the encoder selects the
nearest occurrence.

There is also a failure that choosing another occurrence cannot fix: at symbol
9,374,985, the nearest `7` is 23 symbols back, giving offset `13-23 = -10`.
No occurrence lies in the nibble's distance range 6..21. The surrounding
consecutive clean windows are:

```text
ends at 9,374,973: B7C9A81265304
ends at 9,374,986: 205146389AC7B
```

All twelve windows between them are dirty. These two permutations have no
positive suffix/prefix overlap, so the actual 13-symbol connector is already
shortest for these fixed endpoints. The out-of-range reference by itself does
not demonstrate removable padding or prove the whole word nonminimal.

Six-bit mode represents both offsets; the prefix test above verifies this with
the implemented encoder and decoder.

### Resource use and errors

The encoder reads its input once, checks it completely, and temporarily spools
the tuple body to disk to determine the header's counts. Memory use is fixed I/O
buffers plus O(N) state; temporary disk use is one byte per four-bit tuple, or
three bytes per pair of six-bit tuples plus two bytes for any final odd tuple.
The temporary file is removed when closed. Input validation or range failures
publish no bytes to stdout, though shell redirection may already have created an
empty destination. Output/device errors can still leave a partial file.

The decoder streams without spooling the restored word. A late error can leave
a decoded prefix on stdout; discard that output on a nonzero exit status.
Version 1 has no checksum: structural validation does not detect every bit flip.
An outer xz stream supplies its integrity check with the default settings.

## Regression checks

```sh
python -m unittest discover -s tests -v
```

The codec suite compiles into a temporary directory and checks independently
specified binary vectors, signed boundaries and zero offsets, N=32, both label
modes, empty/short words, whitespace normalization, corpus round trips, the former
bounded-history collision, large buffers, outer xz, range rejection, malformed
files, odd/even tuple packing, zero padding, layout selection, and named-input/stdin
behavior. The existing paint-waste suite verifies that the diagnostic tool still
behaves as before.

All **31 regression tests passed** after switching the outer-compression checks
to default xz. The codec corpus tests exercise binary -> xz -> binary -> word
for both field widths. The separate benchmark runs above also verify the full
N=10/N=11 words and the N=13 prefix through xz before decoding.
