# Fast RLLB scoring

`search/rllb.cpp` accelerates the supplied phase-coupled RLLB scorer. It consumes completed trail/port graphs directly. Its two price families are the full connector-key trie used at N=12 and the grouped endpoint-symbol prices used in the archived N=13 experiments.

Run builds and examples in WSL/Linux Bash:

```sh
make rllb rllb-ports
./build/rllb --help
```

The default uses up to four OpenMP threads. `--threads 1` selects serial scoring; `--threads N` selects another thread count. `OMP_NUM_THREADS=1` also limits the default to one thread. A serial build is available with `make -B rllb RLLB_CXXFLAGS='-O3 -std=c++20'`.

## Full-key trie scoring

The positional arguments match the supplied N=12 `global_trie_multilevel` program:

```text
rllb PREFIX CHARGE OUTPUT.json [min_key=7] [iterations=80] [step=0.04]
     [target=522736428] [prices_in|-] [prices_out|-]
     [--n 11|12|13] [--threads N] [--grouped]
```

For a complete Q210 port graph and its saved certificate:

```sh
./build/rllb build/Q210 179424 build/certificate.json 6 0 0 522736428 build/prices.bin -
# Optimize prices from zero and save the best price vector:
./build/rllb build/Q210 179424 build/score.json 6 20 .04 522736428 - build/best-prices.bin
```

`PREFIX.trails.tsv` describes consecutive, nonempty ranges of legal opening phases. Both supplied graph layouts are accepted:

| Table columns | Binary file |
| --- | --- |
| `trail start length firstport ports` | `PREFIX.ports.bin`: little-endian 4-byte offset and 8-byte packed endpoint word per phase |
| `trail first_port n_ports native_length first_head` | `PREFIX.heads.bin`: little-endian 8-byte packed endpoint word per phase |

Use `./build/rllb-ports --n 12 SELECTION PREFIX` to produce these files without a literal word, and supply the selection's charge. The scorer checks file layout, alphabet, and trail ranges. Validation that the graph completes the intended selection belongs to the generator.

N defaults to 12. Select N=11 or N=13 with `--n` and an explicit target length. Endpoint width is `h=n-3`; full-key trie depths range from `min_key` through `h-1`. N=13 keys retain all 36 bits at depth 9.

## N=13 grouped-price scoring

To keep the archived N=13 first/last-symbol grouping and its AdaGrad updates:

```sh
./build/rllb build/n13_candidate 1812288 build/n13-score.json 6 12 .04 6747800155 --n 13 --grouped
```

The target above is an explicit historical comparison length, not a claim about the current record. Omit `--grouped` to use full connector keys instead. Full keys and symbol groups are different price families; their iteration traces should not be compared as if they were the same scorer. Grouped mode does not read or write full-key checkpoints.

The grouped implementation keeps 8 bytes per port instead of the archived program's 16-byte precomputed group-index record. It computes small table indices from packed endpoint words while evaluating independent trails in parallel. A 57,883-port, 426-trail N=13 packet check matched all 31 iterations of the archived grouped scorer to its printed precision, in both serial and four-thread execution. This was a packet-level compatibility check, not a complete N=13 word-length experiment.

## What became faster

The full-key implementation builds connector indices with linear radix passes rather than repeated comparison sorts and per-port binary searches. States occupy 8 bytes rather than 12. Each iteration precomputes key prices, evaluates independent trails in parallel, and reconstructs the selected incoming/outgoing roles only for the winning phase of each trail. Gradient updates visit touched keys rather than scanning every node. Trail totals and gradient accumulation retain their original order, so changing the thread count does not change the result.

On the complete N=12 Q210 graph (3,808,224 ports, 6,624 trails, depths 6--8), the [recorded benchmark](benchmark.json) compares the original C++ implementation with this implementation. Timings include reading the graph, building the trie, and scoring; selection-to-port generation and compilation are excluded. Input files are reused between interleaved runs; this is not a cold-disk benchmark.

| Complete N=12 Q210 task | Original C++ | Fast, 1 thread | Fast, 4 threads | Speedup with 4 threads |
| --- | ---: | ---: | ---: | ---: |
| 20 price-update iterations | 5.522 s | 1.936 s | 1.038 s | 5.32x |
| Reloaded certificate, no price updates | 4.474 s | 0.596 s | 0.519 s | 8.61x |

Medians of three interleaved runs on an AMD Ryzen 5 9600X under Ubuntu WSL 2, GCC 15.2.0, `-O3 -std=c++20` (OpenMP enabled for the fast binary).

The benchmark requires identical trie statistics, dual histories, and final bounds, not just similar timings. It recomputes the saved certificate `U <= 49,770`, `J >= 9,846`, and `L >= 522,736,470` against the historical target 522,736,428.

Reproduce from the small pinned reference inputs in `data/rllb/20261122/` (`--bundle` also accepts the original research ZIP or its extracted root):

```sh
python3 tools/benchmark_rllb.py --threads 4 --repeats 3 --output build/rllb-benchmark.json
python3 tests/test_rllb.py
```

The tests include exhaustive legal orders/openings at N=11,12,13, the archived grouped N=13 trace, thread determinism, long connector keys, malformed inputs, and checkpoint recomputation. They do not decode or revalidate the record words.

## Bound and checkpoint semantics

For the restricted model of one intact weight-3 opening per completed trail,

```text
F3 = n! + (n-1)! + (n-2)!
L = F3 + Q + (n-3)T - O
O <= U(theta)
L >= F3 + Q + (n-3)T - ceil(U(theta) + conservative numerical guard)
```

The same opening phase supplies both endpoint roles of each trail. Full-key mode retains the archived conservative `1e-5` ceiling guard and its tie rules. This is a restricted arrangement bound; it does not reject weight-2 openings, split trails, or unrestricted superpermutations. Passing the screen is not a constructed word.

N=12 full-key checkpoints keep the supplied binary layout. Loaded prices are evaluated afresh on the current graph; a stored historical best value is not trusted as a transferable certificate. New checkpoints store the actual best price vector, rather than the last iterate paired with a different best score.

The current [529](../n11/43930529/REPRODUCE.md), [527](../n11/43930527/REPRODUCE.md), and [406](../n12/522736406/REPRODUCE.md) record guides run `search/rllb.cpp` as their first computational stage. Papers, personal notes, and record-specific receipts live in those directories.

The source is based on `modules/04_n12_RLLB_GlobalTrie_Certificate/global_trie_multilevel.cpp` and `modules/10_n13_RLLB_Monodromy_Kernel/direct_kraft_screen.cpp` in the user-supplied November 22, 2026 RLLB bundle. It is an optimization of those supplied implementations, separate from the 50-unit placement/replay programs.
