/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Coeff2.Loops

/-!
# First entries, the successor map, breaks, and defect positions (paper §4)

Formalization choices:
* The paper's list `E₀, E₁, …, E_{v(W)−1}` of entered loops in order of first entry is
  realized through the strictly increasing enumeration `tauIdx` of first-entry *times*
  (`tauIdx W 0 = 0`; each later value is the least first-entry time exceeding the
  previous one, junk `0` when exhausted).  `Efe W i` and `xEntry W i` are then `E_i` and
  `x_i`.  The paper's index range `0 ≤ i ≤ v(W)−1` corresponds to `i < numFE W`, and
  `numFE W = vStat W` is a (provable) statement, not a definition.
* The canonical successor `M` and the ride `R_{h,r}` are total functions on raw words.
-/

namespace Coeff2

open List

variable {n : ℕ}

namespace Walk

/-- Time `t` is a *first-entry* time: the loop active at `t` was not active at any
earlier time.  (Time `0` always qualifies.) -/
noncomputable def IsFirstEntryTime (W : Walk n) (t : ℕ) : Prop :=
  t < W.numVerts ∧ ∀ s < t, W.activeLoop s ≠ W.activeLoop t

/-- The number of first-entry times (equivalently — a statement, `numFE_eq_vStat` — the
number `v(W)` of entered marked 2-loops). -/
noncomputable def numFE (W : Walk n) : ℕ := {t | W.IsFirstEntryTime t}.ncard

/-- `tauIdx W i` is the paper's `τ_i`: the `i`-th first-entry time, in increasing order.
`τ₀ = 0` (the start of the walk always first-enters its loop), and `τ_{i+1}` is the
least first-entry time greater than `τ_i` (junk value `0` when none exists, i.e. for
`i ≥ numFE W`). -/
noncomputable def tauIdx (W : Walk n) : ℕ → ℕ
  | 0 => 0
  | i + 1 => sInf {t | W.IsFirstEntryTime t ∧ tauIdx W i < t}

/-- Paper §4: `E_i`, the `i`-th distinct marked 2-loop in order of first entry. -/
noncomputable def Efe (W : Walk n) (i : ℕ) : MarkedLoop :=
  W.activeLoop (W.tauIdx i)

/-- Paper §4: `x_i = π_{τ_i}`, the permutation of the walk that opens `E_i`. -/
noncomputable def xEntry (W : Walk n) (i : ℕ) : List ℕ :=
  W.vert (W.tauIdx i)

/-- The first entry time `τ(L)` of an entered marked 2-loop `L` (paper §5). -/
noncomputable def tauLoop (W : Walk n) (L : MarkedLoop) : ℕ :=
  sInf {t | t < W.numVerts ∧ W.activeLoop t = L}

/-- `L` was already entered before time `t`. -/
noncomputable def EnteredBefore (W : Walk n) (t : ℕ) (L : MarkedLoop) : Prop :=
  ∃ s < t, W.activeLoop s = L

end Walk

/-- Paper §4, the canonical successor map `M` on first-entry permutations.  If the entry
permutation `x` ends in `α`, `u = del_α(x)`, and the leftward rotation `u^{(n−2)}` is
written `β γ r` (with `β, γ` single symbols and `r` of length `n−3`), then
`M(x) = r γ β α`. -/
def Msucc (n : ℕ) (x : List ℕ) : List ℕ :=
  let α := x.getLastD 0
  let w := (x.erase α).rotate (n - 2)
  w.drop 2 ++ [w.getD 1 0, w.getD 0 0, α]

/-- Paper §4/§5 (Lemma pinned): the anchors of the canonical HPV ride through the marked
2-loop opened at `x`: `R_{0,0} = x`, and `R_{h+1,0}` is the target of the standard
weight-2 door out of `R_{h,n−1} = ρ^{n−1}(R_{h,0})`. -/
def rideAnchor (n : ℕ) (x : List ℕ) : ℕ → List ℕ
  | 0 => x
  | h + 1 => door ((rideAnchor n x h).rotate (n - 1))

/-- Paper §5 (Lemma pinned): the vertex `R_{h,r} = ρ^r(R_{h,0})` of the canonical ride
through the loop opened at `x`. -/
def ride (n : ℕ) (x : List ℕ) (h r : ℕ) : List ℕ :=
  (rideAnchor n x h).rotate r

namespace Walk

/-- Paper §4: `j` is a *break* if `x_{j+1} ≠ M(x_j)`; the index `j` ranges over the
positions with a successor, `0 ≤ j ≤ v(W)−2`, i.e. `j + 1 < numFE W`. -/
noncomputable def IsBreak (W : Walk n) (j : ℕ) : Prop :=
  j + 1 < W.numFE ∧ W.xEntry (j + 1) ≠ Msucc n (W.xEntry j)

/-- Paper §4: `A`, the set of breaks. -/
noncomputable def breakSet (W : Walk n) : Set ℕ := {j | W.IsBreak j}

/-- Paper §4: `P = {i : d_i > 0}`, the edges with positive local defect. -/
noncomputable def Pset (W : Walk n) : Set ℕ :=
  {i | i + 1 < W.numVerts ∧ 0 < W.defect i}

/-- Paper §4: the break `j` meets a positive-defect edge if some `i ∈ P` lies in the
walk interval `τ_j ≤ i < τ_{j+1}`. -/
noncomputable def MeetsP (W : Walk n) (j : ℕ) : Prop :=
  ∃ i ∈ W.Pset, W.tauIdx j ≤ i ∧ i < W.tauIdx (j + 1)

/-- Paper §4: `A_meet`, the set of breaks meeting a positive-defect edge. -/
noncomputable def AmeetSet (W : Walk n) : Set ℕ :=
  {j ∈ W.breakSet | W.MeetsP j}

/-- Paper §4: `A₀ = A \ A_meet`, the breaks whose walk interval contains no
positive-defect edge. -/
noncomputable def A0Set (W : Walk n) : Set ℕ :=
  W.breakSet \ W.AmeetSet

end Walk

end Coeff2
