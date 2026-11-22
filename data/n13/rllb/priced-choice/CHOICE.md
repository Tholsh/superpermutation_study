# n=13 — selection-first RLLB pricing and cold-start choice

**Chosen:** the complete **low-floor hybrid**, comprising the verified 504-row n=13 compound-core exchange and 48 relabelled copies of Halfar's earlier `block_7_4_step1.txt` residual block. **This is a selection decision, not a completed word.**

## Exact structural accounting

| Component | Compact N-block hybrid | Low-floor Step1 hybrid |
|---|---:|---:|
| Core charge Q (shared) | 1,695,024 | 1,695,024 |
| Core trails (shared) | 7,716 | 7,716 |
| Full Q | 1,820,352 | 1,812,288 |
| Full T | 21,444 | 28,452 |
| Full Q+T | 1,841,796 | **1,840,740** |
| Delta vs Halfar N | -780 | **-1,836** |

## Exact phase-coupled nine-overlap chains (per residual block)

An integer program selects at most one of the 11 legal cut phases per rowless trail, at most one incoming and one outgoing nine-symbol-overlap link, and excludes directed subtours. For N, the optimum is 182 links among 266 rowless trails: 84 chains. For Step1, it is 308 links among 406 rowless trails: 98 chains (its 322-link relaxation has 14 directed cycles). The isolated chain-price difference is +14 for Step1, reducing its native -22 advantage to -8 per replaced fiber. Independent phase and cycle checks succeeded.

We generated all 10-character cut heads for **every** completed slice of both 5,040-loop block selections and reconstructed their exact closed trails by literal head/tail linkage. The counts were N: 58,051 slice states, 286 total trails, Q=2611; Step1: 57,883 slice states, 432 total trails, Q=2443. Both endpoint graphs were balanced with zero missing links.

## Full block, multilevel overlap-trie dual (local, per block)

The global-trie dual was adapted to legal 10-symbol cut states at depths 8 and 9; the incoming and outgoing roles of each trail use **the same cut phase**, with independent real-valued connector prices. For 75 subgradient iterations and conservative ceilings:

| Per-block score | N | Step1 |
|---|---:|---:|
| Charge Q | 2,611 | 2,443 |
| Closed trails | 286 | 432 |
| Depth-8 nodes | 30,863 | 30,912 |
| Depth-9 nodes | 47,012 | 46,718 |
| Dual overlap upper U | 2,438.751 | 3,756.351 |
| Joining lower bound `10T-ceil(U)` | 421 | 563 |
| Local priced `Q+10T-ceil(U)` | 3,032 | **3,006** |

Hence the **isolated residual-block local priced score favors Step1 by 26 per fiber, or 1,248 across 48 fibers**. This is a ranking signal, NOT a global n=13 word-length certificate. The dual could be tightened with more iterations; the score is valid for the local model at each of the evaluated price vectors.

At the whole-residual-family level, an exact key-matching scan found **zero cross-fiber overlap-8 and overlap-9 connections** between the 48 N blocks, and likewise zero for 48 Step1 blocks. There can nevertheless be cross-boundary overlaps with the common core, especially at depth 8; they have not been fully priced. A permissive core superset test for one fiber admitted such boundary matches.

## Decision

**Cold-start the all-Step1 low-floor hybrid first.** Its structural advantage survives local phase-coupled chain pricing, and the more detailed depth-8/9 block trie price favors it further. Preserve the compact hybrid as a control. This is a choice under quantified uncertainty—not proof that its globally arranged word will be shorter. Before claiming a record, run the whole-selection verifier, a global joint overlap price, cold-start placement and phase optimization, and a literal/SPRA factorial coverage check.

## Reproduction

The accompanying `select_first.py` and `best_joint.delta.tsv` are from the saved selection-first package. After obtaining the published original files from `jhalfar/superpermutations`, run `prepare_chosen.sh` to generate both selections and verify their native loop/monodromy counts. No word is arranged in this package.
