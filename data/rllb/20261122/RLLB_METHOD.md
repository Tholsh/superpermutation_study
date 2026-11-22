# RLLB: definitions, exact claims, and replay

## The restricted model (one intact weight-3 cut per completed trail)

For degree `n`, put `F3 = n!+(n-1)!+(n-2)!`, selection charge `Q`, and completed trails `T`. An intact weight-3 cut has length `H=n-3` symbols (n12: 9; n13: 10). If `O` is the sum of actual legal suffix-prefix overlaps across the `T-1` joins (each at most `H-1`), then this **restricted construction model** gives

```
L = F3 + Q + H*T - O.
L >= F3 + Q + T + (H-1).
```

This analytic floor alone is often too weak, because not every trail can choose an independent ideal phase and matching neighbor.

## Global multilevel connector-trie pricing (n12)

The original implementation is `modules/04_n12_RLLB_GlobalTrie_Certificate/global_trie_multilevel.cpp`. A port `p` on trail `i` supplies its incoming `prefix_k(p)` and outgoing `suffix_k(p)` for `k` at trie depths `m..H-1`. The **same port phase** determines both ends of a trail. Give each distinct trie key a real price `theta[k,key]`. Define

```
B_i(p, theta) = max((m-1)/2,
                       max_{m<=k<H; incoming available} [k/2 - theta[k,prefix_k(p)]])
               + max((m-1)/2,
                       max_{m<=k<H; outgoing available} [k/2 + theta[k,suffix_k(p)]]).
U(theta) = sum_i max_{p in legal_port_phases(i)} B_i(p,theta).
```

For any realizable intact-cut arrangement, `O <= U(theta)`. When a true join matches a key, its two price contributions cancel; fallback terms dominate smaller overlaps. Appending a zero-overlap dummy edge covers the two endpoints. Therefore **for any supplied dual price vector**:

```
L >= F3 + Q + H*T - ceil(U(theta))
```

The original program includes conservative rounding. Improving the dual price vector improves the bound without constructing a Hamiltonian trail order. It **cannot** establish that a candidate passing the gate is arrangeable. On the sample n12 Q210 selection, the saved depths 6/7/8 checkpoint gives `U<=49770`, `T=6624`, `Q=179424`, `J>=9846`, and `L>=522736470`. It rejects Q210 **only** in the intact weight-3 model relative to target length 522736428.

The tests in `test_exhaustive.py` independently enumerate small phase/route cases and check the dual upper bound exceeds actual maximum overlap. The supplied checkpoint can be validated without trusting the score saved in JSON: `bash scripts/replay_n12_RLLB_certificate.sh` reloads checkpoint weights with previous best set to infinity.

## n13 layer

`modules/10_n13_RLLB_Monodromy_Kernel/direct_kraft_screen.cpp` uses four depths 6..9 but deliberately groups keys by endpoint letters, not their full strings. Equal full keys always receive equal prices, preserving a sound (possibly very weak) restricted dual. The n13 structural reference is `F3=6745939200`, and for one intact weight-3 cut:

```
L >= 6745939200 + Q + T + 9.
```

This gate is inexpensive and necessary **within the restricted model**, but it is not an accurate estimate of a final word's length. The n13 packet outputs contain complete native selection audits, bounded profiles, and literal-oracle logs where originally recorded; see each module README for whether full literal assembly occurred.

## Separate layers that are not global RLLB proofs

- Native incidence/occupation and `G_v` closure are exact discrete constraints. `blockcore.py`, `verify_generic_selection.cpp`.
- Exact port monodromy yields completed trail counts (`T`) for a given selected packet. It does *not* choose a full path through trails.
- A min-plus cut DP is **exact for a fixed unit order and enumerated legal cut modes**. Search across all orders remains heuristic unless enumerated/certified.
- Port-to-port cost-one chain packing can be a certified MILP optimum **for that packing subproblem**; it does not certify global completion.
- Genuine prefix-free first-hit Kraft subsets satisfy the coding inequality, but raw bridge labels often are not prefix-free; spectral radii of raw bridge graphs are useful diagnostics, not a global Kraft proof.
- Global price vectors projected into individual row costs are heuristics; they are audited again on the full native selection.

## Missing generality and safe interpretation

This particular RLLB layer excludes weight-2 cuts, splitting/recutting intact trails, deliberate repeated clean windows and certain compound/nonlocal interfaces. Those features can rescue a candidate that the restricted layer rejects. Do **not** use its `restricted_reject=yes` as a claim that an unrestricted n12/n13 record is impossible. Do not treat a model-specific lower bound as a feasible constructed length. This warning is not optional: the n12 study demonstrated attractive `Q+T` packets that were poor after honest global connection pricing.
