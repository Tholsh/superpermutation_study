# Boundary-phase reassembly: n=8, length 46,173

A small, self-contained **source** package for the verified 46,173-letter
word. Copy this directory into another repository without changing its
internal paths. No Git checkout, solver license, GPU, network connection,
or machine-specific executable is required.

The winning search is Jakub Halfar's **unchanged** `trailsearch.c`, working
on his selection in Jay Pantone's construction. This package does not
claim a new search implementation, an all-n improvement, or minimality.
Retain `LICENSE`, `NOTICE`, and `PROVENANCE.md` when redistributing it.

## Contents

- `src/trailsearch.c`: the existing randomized assembly search and plan replayer.
- `src/literal_check.cpp`: Pantone's independent literal coverage/deletion checker.
- `src/applyplan.py`: Halfar's independent plan speller (optional Python 3).
- `src/geng.py`, `src/gen12.py`: Halfar's selection-to-base generator and dependency.
- `examples/n8/`: the fixed selection, base/table, parent word/plan, and solution word/plan.
- `evidence/`: original discovery and verification receipts, plus package test results.
- `SHA256SUMS`: hashes of the other packaged files; word hashes include their final LF.

No binaries or n>=9 plaintext words are included. This is the **n=8**
reproducer, not a bundle of our separate n=11/n=12 experimental solvers.

## Build and exact replay (Linux or an MSYS2 UCRT64 shell)

Requires GCC with OpenMP, G++, and GNU Make. The default build does not
require CPU-specific instruction flags. From this directory:

```sh
make
make check
```

`make check` rebuilds the parent and solution from their saved plans,
compares both byte-for-byte with the included words, and independently
scans the solution. Expected: length 46173, 40320 distinct permutations,
and zero missing. The saved plan is the deterministic recipe; no search
is needed to reproduce the result. Output is written only under `build/`.
Replay targets refuse to overwrite existing output files; use a fresh
`BUILD` directory for another run, e.g. `make BUILD=build2 check`.

For an additional independent plan spelling using Python 3:

```sh
make check-python
```

To regenerate the base from the included selection (optional):

```sh
python3 src/geng.py examples/n8/selection.txt build/regenerated-base.txt --table build/regenerated-base.tsv
cmp examples/n8/base.txt build/regenerated-base.txt
```

The files are small n=8 examples. Do not apply this plaintext workflow to
large corpus words when your repository requires compressed storage.

## Equivalent PowerShell commands

Use GCC/G++ from MSYS2 UCRT64 on PATH, including its OpenMP runtime DLL.
Run each command successfully before proceeding. Choose fresh output names.

```powershell
New-Item -ItemType Directory build
gcc -O2 -std=gnu11 -fopenmp src/trailsearch.c -o build/trailsearch.exe -lm
g++ -O2 -std=c++17 src/literal_check.cpp -o build/literal_check.exe
./build/trailsearch.exe examples/n8/base.txt build/replayed.txt --plan-in examples/n8/solution.plan --time 0 --threads 1
if ($LASTEXITCODE -ne 0) { throw 'Plan replay failed' }
if ((Get-FileHash build/replayed.txt).Hash -ne (Get-FileHash examples/n8/solution.txt).Hash) { throw 'Replay bytes differ' }
./build/literal_check.exe 8 01234567 build/replayed.txt --deletions
if ($LASTEXITCODE -ne 0) { throw 'Literal coverage check failed' }
```

## Try the original 60-second search

```sh
make search
```

This executes:

```sh
build/trailsearch examples/n8/base.txt build/search.txt --plan-in examples/n8/reference.plan --time 60 --threads 1 --seed 27003 --kmax 12 --T0 0.7 --ckpt 15 --sync 15
build/literal_check 8 01234567 build/search.txt
```

**The same seed is not a guarantee of the same discovery.** The search is
wall-clock dependent; compiler, hardware, and timing affect its trajectory.
The original log records the first gain at about one second / iteration
6176 and best length 46173 after 60 seconds. The successful final plan has
16 whole-trail `O` events, three weight-2 openings, no split segments, and
no occurrence-dropping openings. The original search permitted splits and
duplicate-skipping; neither was used in the saved winning plan.

## What changed mathematically

All 16 closed trails remain complete; the row selection is unchanged.
With boundary width h=5 and cyclic spelling sum 46144, the exact ledger is

```text
L = 5 + 46144 + opening_cost + join_cost
parent:   46149 + 0 + 25 = 46174
solution: 46149 + 3 + 21 = 46173
```

Each join costs `5 - longest_literal_suffix_prefix_overlap`. Thus the
three additional opening symbols buy four joining symbols. The source
is a literal discrete search over these interactions, not a Fourier or
eigenvalue solver.

Expected solution SHA-256 (including its single final LF):

```text
9ec23c8c05d60e51786d5fedea27aa3b6b2841c96fe15cf82c6095ecede7b475
```

Excluding that LF:

```text
6ad59b18b8cd281fe0052a0e6898d74e533c6c56f68776948fb0f1c912c4a613
```

All 40320 S8 permutations are covered. There are 40376 valid permutation
occurrences, hence 56 repeats. The literal single-deletion scan finds no
coverage-preserving one-symbol deletion; this does not prove minimality.
