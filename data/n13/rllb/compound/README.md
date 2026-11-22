# n=13 A-packet compensator: repeat-aware native-selection experiment

**Scope:** Direct n=11 A-braid monodromy extension into n=13. This report distinguishes closed row itineraries, complete native selections, restricted joining lower bounds, and literal superpermutation words. **No new n=13 literal word is claimed.**

## 1. The original 108-step candidate

The supplied `low_cost_4_closed_walk.tsv` is a closed 108-step row itinerary with port monodromy cycle lengths `(3,7)`, deficit sum 172, 99 distinct cyclic classes and nine repeated class visits. It is not a one-choice-per-class native selection.

A repeated cyclic class is allowed in a superpermutation, but it costs real symbols if the class is fully completed again. An n=13 native cyclic class has baseline completion contribution `13!+12!+11!` divided by `10!`, or **1859** symbols. Accordingly, full repetition is far costlier than the earlier deficit-only score suggested. This 1859 increment applies to *full duplicate native completion*, not an uncosted short detour.

A repeated-state decomposition exposes two removable 10-step full-row circuits with identity port action. Removing them preserves closure and exact `(3,7)` monodromy, leaving **88 steps, deficit 172, and only one repeated class**. Similar reduction of other archived four- and five-gadget compensators yielded several **zero-repeat** closed row itineraries.

The cheapest zero-repeat itinerary in the tested catalogue has **98 active rows, deficit 232, port cycles `(3,7)`**. Its native grade-to-state edges are verified, but it is still only a partial row walk until integrated with all required cyclic classes.

## 2. Explicit integration into the full native selection

We start from the complete `direct11_step1.selection`, which itself was built from the archived n=11 source (not copied from the n=12 E word). For each motif, identify all originally active closed row walks intersecting any motif class. Demote those entire baseline walks to detached classes, except that the motif takes its own classes. This preserves one chosen row per cyclic class and keeps the remaining original walks intact. The corrected motif is itself closed.

This **whole-walk-demotion splice** is deliberately conservative: it guarantees a complete, balanced native selection without solving the harder short-range circuit exchange. It can be expensive because a small motif may intersect long core walks.

The 98-step Q232 splice is independently valid with `Q=1,689,924`, `T=270,106`, but has restricted floor `6,747,899,230` (its exact linear-path weight-3 cut floor is 9 letters higher). The local one-hop mixed-integer repair, which tries to alter only rows directly adjacent to the 148 imbalance endpoints, is infeasible within that candidate neighborhood; this is NOT a proof against more distant repairs.

## 3. Search beyond the original low-charge motif

Thirteen zero-repeat reduced motifs (88–108 steps, deficits 232–362) were screened against the complete direct-n11 selection. For each fixed motif we enumerated **all 7! × 4! = 120,960 old/new-alphabet relabelings**, computing the exact charge and completed-trail count of the guaranteed balanced demotion splice. The best fixed motif was a **108-step, charge-362** itinerary, not the cheapest motif.

For this leading motif we also checked 36 distinct placements of the two newly inserted symbols, again with all 120,960 relabelings each. Total evaluated in these two stages, counting the original leading start only once: **5,806,080** placements/relabelings in the specified tested family.

The best candidate's selected relabeling is `0123456789A -> 013245678A9`, on the saved `candidate_12_108step_Q362.tsv` phase. Its complete selected output is `n13_108step_compound_best_demote.selection.xz`.

## 4. Independently verified best complete selection

| Measure | Verified value |
|---|---:|
| Degree | 13 |
| Native 2-loop classes | 3,628,800 |
| Duplicate / missing 2-loop classes | 0 / 0 |
| Row-state balance defects | 0 |
| Charge Q | 1,786,938 |
| Detached loops D | 70,808 |
| Active row walks | 1,230 |
| Active completion trails | 11,162 |
| Total completed trails T | 81,970 |
| Native cyclic contribution F3+Q | 6,747,726,138 |
| Full native SPRA/Pantone completion slices | 41,703,738 |
| Distinct cyclic classes in full completion | 479,001,600 |
| Missing/repeated cyclic classes | 0 / 0 |
| Verified best selection (uncompressed) SHA-256 | `1bec251539707b029d7d6daaacede62b844f0b08812d94d86198c1eaa0a1cda3` |

A separate C++ completion-slice generator verified all heads and tails balance, generated all 81,970 completed trails, and an independent 4-thread factorial-class bitmap scan found all **479,001,600** n=13 cyclic classes exactly once, without malformed entries.

## 5. Updated n=12-style RLLB screen

Let `F3=13!+12!+11!=6,745,939,200`. In the restricted **intact weight-3** model, each of the T closed completion trails is opened once, adding 10 opening symbols. Each of the T-1 suffix-prefix joins has length at most 9. Thus the model has the exact universal bound:

`L >= F3 + Q + 10T - 9(T-1) = F3 + Q + T + 9`.

For the best complete selection:

`L >= 6,747,808,117` (**8,117 above 6,747,800,000**).

The independent global, phase-coupled radix-trie screen (depths 6 through 9, conservative dual bound) gives `L >= 6,747,808,107`, ten symbols weaker due to the deliberately permissive dummy-closing-edge and numerical guard. No stronger price vector was found by its 16 iterations. The straightforward exact weight-3 linear path bound above therefore dominates it.

Consequently, **no intact weight-3 one-cut-per-trail arrangement of this complete selection can meet the target**. The global search over the specified 5,806,080 whole-walk-demotion variants likewise did not find one whose basic restricted floor falls below the target.

**Crucial limitation:** These bounds do not reject opening trails at weight 2, splitting trails, transport-only repeats, or globally coupled exchanges that repair the native state graph without demoting entire original walks. The n=12 notes explicitly warn against extending a weight-3 certificate to those unrestricted operations. To beat the target from this best selection would require at least 8,118 symbols of benefit beyond even the ideal intact weight-3 joins.

## 6. Next constructive target

A monodromy-correct partial braid is not enough: the row-state incidence defects left by replacing the old selected rows must be repaired via **short, occupation-preserving exchange circuits**. On the best 108-step motif, one-hop repair restricted to native classes directly adjacent to the defect states is infeasible. The viable search is to allow nonlocal, coupled native circuits while explicitly pricing any duplicated completion and depth-2/split openings.

The key progress is thus a **complete, verified selection derived from the recursive A-monodromy construction**, together with a precise diagnosis of why its conservative integration is not record-competitive in the intact-weight-3 model. No literal word was assembled from it, because the requested sub-6,747,800,000 threshold already fails in that model.
