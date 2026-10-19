# Reduced-alphabet binary codec

`tools/reduced_codec.cpp` builds `reduced-codec`, a reversible first pass for gzip
or another general-purpose compressor. Version 1 stores each reduced-alphabet
tuple in **one byte**: an unsigned depth nibble and a signed copy-offset nibble.
The header identifies the version, layout, alphabet, and word length.

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
./reduced-codec decode word-n5.spra > restored-n5.txt
```

The interface is:

```text
reduced-codec encode [-z|--zero-based] N [INPUT|-]
reduced-codec decode [INPUT|-]
```

Omitting `INPUT`, or using `-`, reads stdin. `N` must be between 1 and 16. Decode
reads N and the alphabet mode from the header; it takes no N or alphabet flag.

Input labels are the first N characters of `123456789ABCDEFG`, or
`0123456789ABCDEF` with `-z`. Each uppercase letter is one symbol. The encoder
ignores ASCII spaces, tabs, CR, LF, form feeds, and vertical tabs, and rejects all
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
```

Quote paths containing spaces inside the command string:

```powershell
cmd /c '.\reduced-codec.exe encode 5 "input word.txt" > "packed word.spra"'
cmd /c '.\reduced-codec.exe decode "packed word.spra" > "restored word.txt"'
```

Do not pass `.spra` data through `Get-Content`, `Out-File`, or a text encoding.
Redirection creates or truncates the destination before the program runs, so use
different input and output paths and check the exit status before keeping a file.

## Put gzip after the first pass

In Bash (for example WSL or MSYS2), enable `pipefail` so a failure anywhere in the
pipeline returns a failing status:

```sh
set -o pipefail
./reduced-codec encode 5 words/5/153/153-recursive.txt | gzip -c > word-n5.spra.gz
gzip -dc word-n5.spra.gz | ./reduced-codec decode > restored-n5.txt
```

For an existing zero-based xz corpus word that fits the nibble ranges:

```sh
xz -dc words/11/43930624/superpermutation-11-43930624.txt.xz |
  ./reduced-codec encode -z 11 | gzip -c > word-n11.spra.gz
```

Check each pipeline's status and discard incomplete results on failure. Gzip is
an external second pass; the codec neither invokes it nor claims that every word
will compress smaller. Compare total `.spra.gz` size, including the header, with
gzip applied directly to the word.

### Measured corpus example

A full round trip of the [43,930,624-symbol N=11 word](../words/11/43930624/superpermutation-11-43930624.txt.xz), encoded with `-z`, produced:

| Representation | Bytes |
| --- | ---: |
| Word, with whitespace removed | 43,930,624 |
| Version 1 `.spra`, including header and seed | 3,995,032 |
| Word followed directly by gzip level 9 | 8,940,093 |
| `.spra` followed by gzip level 9 | 29,073 |

The binary contains 3,994,998 tuples. The decoded word's SHA-256 matches the
normalized corpus word:

```text
0f3b2dcf607aaf3e7985c9daf2d87c07f8947522490dfea90b05a90c7fd5aa6b
```

These gzip measurements used Python's `gzip.GzipFile` with `compresslevel=9`, an
empty filename, and `mtime=0` for both inputs. Other gzip implementations may
produce different sizes; this is a corpus example, not a general size guarantee.

The same level-9 comparison on other selected words gave the following sizes.
Both inputs use the word with whitespace removed, and the reduced column includes
the complete binary header and seed:

| N | Word length | Direct gzip | Reduced format + gzip |
| ---: | ---: | ---: | ---: |
| 1 | 1 | 21 | 31 |
| 2 | 3 | 23 | 31 |
| 3 | 9 | 29 | 36 |
| 4 | 33 | 42 | 43 |
| 5 | 153 | 77 | 49 |
| 6 | 872 | 300 | 94 |
| 7 | 5,913 | 1,500 | 73 |
| 8 | 46,181 | 11,579 | 186 |
| 9 | 408,731 | 100,267 | 550 |
| 10 | 4,034,889 | 891,364 | 3,450 |
| 11 | 43,930,624 | 8,940,093 | 29,073 |

The examples at N=1..4 are the recursive words of lengths 1, 3, 9, and 33.
The corpus examples are `153-recursive`, `872-treelike/872-00001`,
`5913-palindromic`, `superperm8_46181_1`,
`superperm9_408731_19_canonical`, `superpermutation-10-4034889`, and
`superpermutation-11-43930624`. N=10 and N=11 use zero-based labels.
The header costs more than the transform saves on these tiny N=1..4 examples;
the crossover is N=5 in this sample. This is construction-dependent, not a
general theorem about N.

### Exploring wider tuples

Equivalent reserializations of the N=11 tuples give the following comparison.
The wider layouts are experiments for a future format; the current codec accepts
only the version-1 `0x44` layout.

| Depth bits + offset bits | Uncompressed file bytes | Gzip level-9 bytes |
| --- | ---: | ---: |
| 4 + 4, byte-aligned | 3,995,032 | 29,073 |
| 6 + 6, packed across bytes | 5,992,531 | 43,585 |
| 8 + 8, byte-aligned | 7,990,030 | 50,971 |

The 8+8 experiment writes a depth byte followed by a sign-extended offset byte
for each tuple. The 6+6 experiment packs two 12-bit tuples into three bytes;
an odd final tuple has four zero padding bits. Both retain the seed and counts
and identify their proposed layout in the header. These measurements use the
same normalized word and gzip settings as above. Gzip recovers much of the
expanded stream's redundancy, but compressed size still rises about 75% for
8+8 on this word. Bit packing is not always smaller after gzip: for the N=9
example, 6+6 gives 839 bytes and 8+8 gives 831 bytes.

A 6+6 layout represents depth 0..63 and signed offset -32..+31. At N=32 that
supports every copy distance from 1 through 64, although longer runs and farther
references would still need an extension or rejection rule. Format-wide support
for complete N=32 words also needs wider lengths and position counters: 32!
requires 118 bits, and even 21! exceeds the current uint64 decoded-length field.

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
compresses to 29,074 bytes with gzip level 9, versus 3,995,032 and 29,073 bytes for
the current 4+4 format. The trial parser checked every reconstructed dirty symbol
against the original word. This is an exploratory format, not implemented by
`reduced-codec`; the version-1 wire format below is unchanged.

## Tuple semantics

The encoder retains the first `min(word_length, N-1)` symbols as a seed. Starting
at the next symbol, it classifies length-N windows as clean (all symbols distinct)
or dirty (some symbol repeated), just like `paint-waste`.

For every dirty window it emits:

```text
bits 7..4: depth       number of clean windows since the preceding dirty window
bits 3..0: offset      signed four-bit two's complement
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

Two's complement is decoded as `low < 8 ? low : low - 16`. For example:

| Low nibble | Signed offset | Copy distance |
| --- | ---: | --- |
| `0x7` | +7 | N-7 |
| `0x1` | +1 | N-1 |
| `0x0` | 0 | N |
| `0xF` | -1 | N+1 |
| `0x8` | -8 | N+8 |

Zero is an ordinary offset in version 1, and byte `0x00` is an ordinary tuple.
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
| 5 | 1 | Tuple layout: `0x44` (four depth bits, four offset bits). |
| 6 | 1 | Flags: bit 0 selects zero-based labels; all other bits must be zero. |
| 7 | 1 | N, stored directly as an integer from 1 through 16. |
| 8 | 8 | Decoded symbol count, excluding whitespace. |
| 16 | 8 | Tuple count. |
| 24 | `min(decoded_length, N-1)` | Seed symbol IDs, one byte each, in `0..N-1`. |
| After seed | `tuple_count` | Packed tuple bytes, in order. |

The exact file size is `24 + min(decoded_length, N-1) + tuple_count` bytes. Empty
words have just a 24-byte header. N=1 needs no seed and no tuples; its length alone
determines the word. Decode rejects unknown versions/layouts, reserved flags,
invalid seeds or references, impossible clean/dirty steps, missing bytes, tuples
that exceed the decoded length, and extra bytes after the body. It handles one
file per invocation; concatenated `.spra` files are not accepted.

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

## Range limits and failure behavior

This is a **strict nibble format**, not a universal codec for all words. A word
is encodable only when every recorded depth fits 0..15, every dirty symbol has an
earlier occurrence, and its nearest-reference offset fits -8..+7. Copy distances
must therefore lie in `max(1, N-7)..N+8`. N in the header is not a guarantee that
every construction at that N fits. In particular, the corpus contains N=13 bends
outside this range. A first appearance inside a dirty window cannot be represented
by a copy reference and is rejected too.

Trailing clean runs can be arbitrarily long because they are represented by the
decoded length. A clean run longer than 15 **before a dirty symbol** is rejected.
Values never wrap or truncate to fit. Wider fields or escapes can be introduced
through a future version/layout; none are guessed by this decoder.

### Concrete N=13 failure

In `words/13/6747918058/superpermutation-13-6747918058.txt.xz`, the encoder first
rejects symbol 9,374,975 (one-based): its nearest occurrence is three positions
back, giving offset `13-3 = +10`. An older occurrence 16 positions back could
encode that particular symbol with offset -3; version 1's encoder selects the
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

### Resource use and errors

The encoder reads its input once, checks it completely, and temporarily spools
the tuple body to disk to determine the header's counts. Memory use is fixed I/O
buffers plus O(N) state; temporary disk use is approximately one byte per tuple.
The temporary file is removed when closed. Input validation or range failures
publish no bytes to stdout, though shell redirection may already have created an
empty destination. Output/device errors can still leave a partial file.

The decoder streams without spooling the restored word. A late error can leave
a decoded prefix on stdout; discard that output on a nonzero exit status.
Version 1 has no checksum: structural validation does not detect every bit flip.
An outer gzip stream supplies its usual integrity check.

## Regression checks

```sh
python tests/test_reduced_codec.py
python tests/test_reduced_alphabet.py
```

The codec suite compiles into a temporary directory and checks an independently
specified binary vector, signed boundaries and zero offsets, N=16, both label
modes, empty/short words, whitespace normalization, corpus round trips, the former
bounded-history collision, large buffers, outer gzip, range rejection, malformed
files, and named-input/stdin behavior. The existing paint-waste suite verifies
that the diagnostic tool still behaves as before.
