# n=13 A-monodromy kernel packet: multiple RLLB screening cycles

2026-11-22. **Native-selection and restricted-model screening results only; no new literal record word has been constructed.**

## Why this search

Earlier 108-step recursive A-braid whole-walk-demotion selections had excessive joining floors. Returning to the n=9/10 lesson (balanced row-incidence/occupation kernels) and n=11 lesson (heterogeneous packets and phase-coupled placement), the experiment decomposed the published Step1 -> N residual (7,4) packet difference, not an already costly whole-walk demotion. The n=12 lesson is to screen global phase-coupled trie overlap BEFORE any literal cold start.

## New local construction

Both published packet inputs have 5,040 degree-13 native cyclic classes on 11 row letters (`0..A`), with old 7 letters in the same cyclic order. Step1 has Q=2443, D=406, T=432, and 5 active walks. N has Q=2611, D=266, T=286, and 5 active walks.

Their difference consists of exactly 259 changed native classes, partitioned into 8 independent balanced occupancy switches: one component of 161 classes and seven components of 14 classes. Every one of their 2^8=256 switch combinations was enumerated and validated for exact occupation, row incidence closure, charge, and completed-port monodromy.

The minimum Q+T is **2869**, attained by 56 combinations. This archive uses mask 38 (14-row components 1,2,5, with 0-indexed component 0 being the 161-row switch). Thus the 42-row patch `step1_to_kernelhybrid.delta` applied to `block_7_4_step1.txt` gives the new packet `n13_kernel_hybrid_7_4.packet`:

- Q=2443, D=406, 5 active walks, 20 active completion trails, T=426, Q+T=2869.
- One valid **288-row closed active walk has 10-port monodromy cycle type (7,3)**. In Step1 a corresponding 294-row walk has port cycles (3,1,1,1,1,1,1,1). This implements the n11 A-style odd-degree (3,7) cycle type on an actual occupation-complete native packet, but it is **not** a proof of a general recursive lift map.
- 56 masks attain minimum Q+T; all 56 have the (7,3) cycle. Full results are in `n13_7_4_256_kernel_profiles.json`.

## Complete degree-13 native selections

Start from `n13_6747834425.selection.xz` (the prior full 504-core-exchange/48-Step1 selection); relabel the above local packet to the 48 residual 7-letter fibers, keeping the existing connected core unchanged. Three full selections are supplied:

| Selection | Residual assignment | Q | D | T | Q+T | Intact-weight-3 RLLB | Margin below 6,747,800,155 |
|---|---|---:|---:|---:|---:|---:|---:|
| `n13_kernel_hybrid_48.selection.xz` | 48 hybrid | 1,812,288 | 19,488 | 28,164 | 1,840,452 | 6,747,779,661 | 20,494 |
| `n13_kernel_ABH_mixed.selection.xz` | 26 hybrid, 15 N, 7 Step1 (original n11 A/B/H fiber positions) | 1,814,808 | 17,388 | 26,106 | 1,840,914 | 6,747,780,123 | 20,032 |
| `n13_kernel_24N24H.selection.xz` | 24 N, 24 hybrid | 1,816,320 | 16,128 | 24,804 | 1,841,124 | 6,747,780,333 | 19,822 |

The A/B/H labels in the mixture identify inherited **fiber locations and an analog assignment**; these are NOT claimed to be exact recursive lifts of the original n11 B/H grade sequences. All three native files have exactly **3,628,800 distinct parent cyclic classes, zero balance defects, and exactly 479,001,600 distinct completed degree-13 cyclic classes, without missing or repeated classes** in the independent C++ slice completion/coverage checks. None was expanded into a 6.7-billion-character word.

Independent native verifier reports are `*.native.log`, completed-slice graph generation logs `*.generate.log`, exhaustive factorial bitmap audits `*.coverage.log`.

## RLLB screening and limitations

For n=13, `F3 = 13! + 12! + 11! = 6,745,939,200`. In the **one intact weight-3 cut per completed trail model**, there are T trails, each with a 10-letter opening cost before overlap. Consecutive cut words overlap by at most nine letters. Consequently every such arrangement obeys

`L >= F3 + Q + 10*T - 9*(T-1) = F3 + Q + T + 9`.

To beat the 6,747,800,155 benchmark, it is necessary that Q+T <= 1,860,945 under this model. Passing is NOT sufficient. A very poor actual joining can easily erase the 20k screening slack.

The n12-style **global phase-coupled connector-trie dual** was run on all 41.7m legal cut positions for the all-hybrid and 26/15/7 mixed candidates. Its returned lower bounds were 6,747,779,651 and 6,747,780,113, respectively; these are 10 below the simpler analytic lower bounds and therefore **do not tighten the rejection gate**. This is a valid restricted-model check, not a certificate that useful overlaps can be realized in one Hamiltonian path. The 24/24 trie has a partial valid bound 6,747,780,323 from the first three iterations but the run was not completed. The trie implementation `direct_kraft_screen.cpp` uses grouped prefix/suffix keys and a simple dual and should not be mistaken for an optimized global matching algorithm.

As in the n12 notes, this model does not cover every possible weight-2 cut, split-trail arrangement, or overlapping duplicated literal windows. A bound restricted to one intact weight-3 cut must NOT be described as an unrestricted lower bound for all superpermutations.

Local depth-9 optimistic cross-trail matchings (ignoring global path and full phase compatibility): Step1=419 of 432, hybrid=413 of 426, N=273 of 286. All three have 13 unmatched trails in this relaxation. This is NOT a realized global arrangement or a proof of viable joining overhead; it motivates retaining the lower-trail packet mixtures despite their marginally weaker Q+T scores.

The n10 universal 2-strand four-row braid was separately tested on Step1: 154 legal uses, all increase Q+T by 10 through 24. Detached-only circuit searches did not find a floor improvement. So the 14-class balanced swaps supplied the win for this round.

## Rebuild exact native selections

The archive includes a standalone deterministic generator `rebuild_screened_selections.py` and its five small inputs. Example:

```
python3 rebuild_screened_selections.py \
  --baseline n13_6747834425.selection.xz \
  --step1 block_7_4_step1.txt \
  --fiber-map n13_direct_11to13_fiber_seed.tsv \
  --delta step1_to_kernelhybrid.delta \
  --n-hex step1_to_N_259.hex \
  --family all_hybrid --output rebuilt.selection.xz
```

For the other variants use `--family abh_mix` or `--family 24n24h`. The rebuild checks class mappings and declares exactly the number of modified rows. Original Step1 and N data are from https://github.com/jhalfar/superpermutations/tree/main/selection/data and baseline from the original user n13 reproducibility archive.

Uncompressed-selection SHA-256:
- all-hybrid: `83911a4c505c843b12c9eec8e29461ddfdfe2391378bc87eb5a7b26ca565cac7`
- 26/15/7 mix: `3422389c0a6f71e82c2aeda7e96a7fddec01496ae2bc74762b9a3450bfc10c03`
- 24/24: `ce3624ed2525feb0177177910b92713b2339b7b47f64f30b0ef728aeb43c2dc3`

Compile independent checks (`g++ -O3 -std=c++20 -pthread`), run native verifier on expanded native selection, generate completed slices/ports from selection using `generate_trails_generic.cpp` and run bitmap audit using `check_classes.cpp` on generated slices. The original logs are included for all three complete selections. Build/read options for individual C++ experimental tools are recorded in their sources.

**Conclusion:** A valid new local (7,4) selection with n11-style (3,7) monodromy exists. Three different complete n13 selections are valid and clear the simple necessary RLLB gate by about 20k symbols. We have NOT established that their achievable global joining costs clear the benchmark or constructed a record word. The next task is cost-aware global phase-and-order optimization over complete fibers/cores, not unfocused literal enumeration.
