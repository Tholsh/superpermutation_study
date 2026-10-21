/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Coeff2.Words
import Coeff2.Walks
import Coeff2.Loops
import Coeff2.Breaks
import Coeff2.Charges

/-!
# All definitions of the paper (umbrella module)

The definitions are split by paper section:
* `Coeff2.Words`   — §2: permutation words, `wt`, proper edges, rotation classes,
                    marked 2-loops `(α, K)`, `V(L)`, `L(σ)`; §3: `ρ`, the door.
* `Coeff2.Walks`   — §2: walks, `len`, covering walks, `Λ(n)`, superpermutations,
                    `S(n)`, `HPV(n)`; prefix walks.
* `Coeff2.Loops`   — §3: the active-loop convention `H_t`, entered loops, the statistics
                    `p, c, v` (with the paper's positional convention for `c`), the
                    excess statistics `e, r, ℓ`, the increments and local defects.
* `Coeff2.Breaks`  — §4: first entries `E_i, τ_i, x_i`, the successor map `M`, the
                    canonical ride `R_{h,r}`, breaks and `A`, `P`, `A_meet`, `A₀`.
* `Coeff2.Charges` — §5: orbit incidence `μ`, shared orbits `D`, `q`, the first-visit
                    owner `F(O)`, the charge sets `𝒞(j)` and the charge map, window
                    modes, slots and `G_{O,L}`, `C`, `G`, `B`; the abstract system of
                    seven facts.
-/
