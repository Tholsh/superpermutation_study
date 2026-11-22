# n=13 compound-exchange selection-first checkpoint

**No cold-start assembly has been performed.** We first optimize valid, balanced selections and retain the benchmark's arrangement separately.

The exact compound-core lift changes 504 of 3,628,800 n=13 native loops. Across the complete selection with Halfar N's 48 residual blocks retained, it has charge Q=1,820,352, completed trails T=21,444, Q+T=1,841,796. The Halfar N benchmark is Q=1,818,768, T=23,808, Q+T=1,842,576. The gain is **780 symbols in the structural floor**. The 504-row patch is stored in `best_joint.delta.tsv`, with original and replacement row states and grades.

We **exhaustively** ranked the original twelve conflict pairs, choosing orientation A, orientation B, or neither for each: 3^12=531,441 combinations. None beats -780. We also independently scored a 50-row alternative packet derived from the same parent exchange. It improves the floor by -55 alone against -68 for the original 42-row packet, but overlaps other packet positions differently. A 30,000-trial joint selection search involving 72 old/alternative packets returned -780; this wider family is **not** exhaustively solved.

## A second, lower-floor selection family

Halfar `selection/data/block_7_4_step1.txt` contains a legal (7,4) residual block with Q=2443, D=406, 26 port-monodromy trails on its 5 closed walks. The block used by Halfar N (`selection/data/block_7_4_n13.txt`) has Q=2611, D=266, 20 port-monodromy trails. Replacing one residual block therefore changes Q by **-168**, T by **+146**, and Q+T by **-22**. These block substitutions are mutually disjoint and preserve the balanced core, so any subset of 48 residual blocks is a valid selection. The below candidates have exact computed structural totals:

| Replaced residual fibers | Q | T | Q+T | vs Halfar N |
|---:|---:|---:|---:|---:|
| 0 | 1,820,352 | 21,444 | 1,841,796 | -780 |
| 1 | 1,820,184 | 21,590 | 1,841,774 | -802 |
| 12 | 1,818,336 | 23,196 | 1,841,532 | -1,044 |
| 24 | 1,816,320 | 24,948 | 1,841,268 | -1,308 |
| 48 | 1,812,288 | 28,452 | 1,840,740 | **-1,836** |

**Selection-stage caution:** the final row of the table introduces 7,008 additional trails versus the compact-trail selection; its structural floor is better, but literal joining is likely harder. This is an **unpriced** bound, not the global-trie-priced RLLB. We should price chains and overlaps before choosing the 48-fiber variant for arrangement.

## Reproduce selections (no arrangement)

Download the original `n13-selection.txt.xz` from [Halfar's repository](https://github.com/jhalfar/superpermutations/tree/main/reproduce/selections), plus the two residual-block files in [selection/data](https://github.com/jhalfar/superpermutations/tree/main/selection/data).

```bash
python select_first.py n13-selection.txt.xz block_7_4_n13.txt block_7_4_step1.txt core_only.selection.xz --fibers none
python select_first.py n13-selection.txt.xz block_7_4_n13.txt block_7_4_step1.txt low_floor.selection.xz --fibers all
```

The script checks all expected old states before replacing any rows, checks both 5,040-loop blocks' closure and monodromy, and asserts exact Q values, changed row counts, 48 source fibers, and 3,628,800 total rows. To independently check the complete emitted selection:

```bash
xz -dc core_only.selection.xz > core_only.selection
python selection/check12.py core_only.selection
```

The original 4,096 binary ranking, score certificates, source, and exact 504-row patch are preserved. No n=13 word or SPRA archive is claimed.
