/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Coeff2.Breaks

/-!
# Shared orbits, the charge map, window modes, slots (paper §5), and the abstract
inequality system (paper §5, Proposition "interface")

Formalization choices:
* Orbit incidence `O ⊆ V(L)` is the ∀-form over representatives of the quotient `O`;
  the paper's "equivalently, one vertex of `O` lies in `V(L)`" is a statement.
* `q = Σ_{O∈D} (μ(O)−1)` is a `finsum` (`∑ᶠ`), with truncated subtraction (harmless:
  `μ(O) ≥ 2` on `D`).
* The paper's "fix once and for all a total order on the finite set of pairs `(O,L)`"
  is realized by the (choice-derived) well-order `WellOrderingRel`; the chosen charge
  `(O(j), L(j))` is the `WellFounded.min` of `𝒞(j)` for it, with a junk value when
  `𝒞(j) = ∅`.
-/

namespace Coeff2

open List

variable {n : ℕ}

/-- Paper §5: a full rotation orbit `O` is *incident* with a marked 2-loop `L` if
`O ⊆ V(L)`. -/
def Incident (n : ℕ) (O : RotClass) (L : MarkedLoop) : Prop :=
  ∀ w, rotClass w = O → w ∈ V n L

namespace Walk

/-- Paper §5: `Ω(O)`, the set of entered owners of `O` (entered marked 2-loops with
which `O` is incident). -/
def OmegaSet (W : Walk n) (O : RotClass) : Set MarkedLoop :=
  {L | W.Entered L ∧ Incident n O L}

/-- Paper §5: `μ(O)`, the number of entered marked 2-loops with which `O` is
incident. -/
noncomputable def mu (W : Walk n) (O : RotClass) : ℕ := (W.OmegaSet O).ncard

/-- Paper §5: a rotation orbit is *shared* if it is incident with at least two entered
marked 2-loops; `D` is the set of shared rotation orbits. -/
noncomputable def Dset (W : Walk n) : Set RotClass := {O | 2 ≤ W.mu O}

/-- Paper §5: the excess incidence count `q = Σ_{O∈D} (μ(O) − 1)`. -/
noncomputable def qStat (W : Walk n) : ℕ := ∑ᶠ O ∈ W.Dset, (W.mu O - 1)

/-- Paper §5: `s(O)`, the least index at which the walk visits the orbit `O` (the walk
is covering, so for a genuine orbit of permutations this exists; junk `0` otherwise). -/
noncomputable def sVisit (W : Walk n) (O : RotClass) : ℕ :=
  sInf {t | t < W.numVerts ∧ rotClass (W.vert t) = O}

/-- Paper §5: the first-visit owner `F(O) = L(π_{s(O)})`. -/
noncomputable def Fowner (W : Walk n) (O : RotClass) : MarkedLoop :=
  genLoop (W.vert (W.sVisit O))

/-- Paper §5: an owner `L ∈ Ω(O)` is a *pre-entry owner* of `O` if some vertex of `O`
was visited before `L` was first entered: there is `t < τ(L)` with `π_t ∈ O`. -/
noncomputable def PreEntryOwner (W : Walk n) (O : RotClass) (L : MarkedLoop) : Prop :=
  L ∈ W.OmegaSet O ∧ ∃ t < W.tauLoop L, rotClass (W.vert t) = O

/-- Paper §5, display (7): for `j ∈ A₀`, the set `𝒞(j)` of pairs `(O, L)` with `O ∈ D`,
`O` incident with `L`, `L = E_j` or `L = E_{j+1}`, and (`L = E_{j+1}` ⟹ `L ≠ F(O)`). -/
noncomputable def chargeSet (W : Walk n) (j : ℕ) : Set (RotClass × MarkedLoop) :=
  {s | s.1 ∈ W.Dset ∧ Incident n s.1 s.2 ∧
    (s.2 = W.Efe j ∨ s.2 = W.Efe (j + 1)) ∧
    (s.2 = W.Efe (j + 1) → s.2 ≠ W.Fowner s.1)}

/-- Paper §5: `j` (in `A₀`) is *charged* if `𝒞(j) ≠ ∅`. -/
noncomputable def Charged (W : Walk n) (j : ℕ) : Prop :=
  (W.chargeSet j).Nonempty

/-- Paper §5: the chosen charge `(O(j), L(j))`, the least element of `𝒞(j)` in a total
order fixed once and for all (here: the well-order `WellOrderingRel`); junk value when
`𝒞(j) = ∅`. -/
noncomputable def charge (W : Walk n) (j : ℕ) : RotClass × MarkedLoop :=
  letI := Classical.dec (W.chargeSet j).Nonempty
  if h : (W.chargeSet j).Nonempty then
    (WellOrderingRel.isWellOrder (α := RotClass × MarkedLoop)).toIsWellFounded.wf.min
      (W.chargeSet j) h
  else (rotClass [], (0, rotClass []))

/-- Paper §5: the charge at `j` is *left* when `L(j) = E_j`. -/
noncomputable def LeftCharge (W : Walk n) (j : ℕ) : Prop :=
  (W.charge j).2 = W.Efe j

/-- Paper §5: the charge at `j` is *right* when `L(j) = E_{j+1}`. -/
noncomputable def RightCharge (W : Walk n) (j : ℕ) : Prop :=
  (W.charge j).2 = W.Efe (j + 1)

/-- Paper §5: `G ⊆ A₀`, the charged breaks. -/
noncomputable def Gset (W : Walk n) : Set ℕ :=
  {j ∈ W.A0Set | W.Charged j}

/-- Paper §5: `B = A₀ \ G`, the uncharged breaks. -/
noncomputable def Bset (W : Walk n) : Set ℕ :=
  W.A0Set \ W.Gset

/-! ## Window modes (paper Definition `windowmodes`)

For `j ∈ A₀`, with `L = E_j = (α, K)`, `a = τ_j`, `b = τ_{j+1}`: the `L`-window is the
segment of the walk on the times `a ≤ t < b`. -/

/-- Paper Definition (window modes): the `L`-window at break `j` is *fresh* if no vertex
of `V(L)` occurs before time `a = τ_j`. -/
noncomputable def FreshWindow (W : Walk n) (j : ℕ) : Prop :=
  ∀ t < W.tauIdx j, W.vert t ∉ V n (W.Efe j)

/-- Paper Definition (window modes): a *switch* in the `L`-window at break `j` is an
index `i` with `a ≤ i`, `i+1 < b`, `π_i ∈ V(L)`, `wt(π_i, π_{i+1}) = 2`,
`π_{i+1} ≠ ρ(π_i)` (automatic, kept for readability), and `last(π_{i+1}) ≠ α`. -/
noncomputable def IsSwitchAt (W : Walk n) (j i : ℕ) : Prop :=
  W.tauIdx j ≤ i ∧ i + 1 < W.tauIdx (j + 1) ∧ W.vert i ∈ V n (W.Efe j) ∧
    wt n (W.vert i) (W.vert (i + 1)) = 2 ∧ W.vert (i + 1) ≠ rho (W.vert i) ∧
    (W.vert (i + 1)).getLastD 0 ≠ (W.Efe j).1

/-- Paper Definition (window modes): the window is switch-free if it contains no
switch. -/
noncomputable def SwitchFree (W : Walk n) (j : ℕ) : Prop :=
  ∀ i, ¬ W.IsSwitchAt j i

/-- Paper Definition (window modes): the window is *full* if `b − a = n(n−1)` (it has
`n(n−1)` vertices `π_a, …, π_{b−1}`). -/
noncomputable def FullWindow (W : Walk n) (j : ℕ) : Prop :=
  W.tauIdx (j + 1) - W.tauIdx j = n * (n - 1)

/-- Paper Definition (window modes): the window is *short* if `b − a < n(n−1)`. -/
noncomputable def ShortWindow (W : Walk n) (j : ℕ) : Prop :=
  W.tauIdx (j + 1) - W.tauIdx j < n * (n - 1)

/-- Paper Definition (window modes): the window is *long* if `b − a > n(n−1)`. -/
noncomputable def LongWindow (W : Walk n) (j : ℕ) : Prop :=
  n * (n - 1) < W.tauIdx (j + 1) - W.tauIdx j

/-! ## Slots (paper §5, after Lemma `uncharged`) -/

/-- Paper §5: an *incident slot* is a pair `(O, L)` with `O ∈ D` and `O` incident with
the entered marked 2-loop `L`. -/
noncomputable def IncidentSlot (W : Walk n) (s : RotClass × MarkedLoop) : Prop :=
  s.1 ∈ W.Dset ∧ W.Entered s.2 ∧ Incident n s.1 s.2

/-- Paper §5: `G_{O,L}`, the set of charged breaks whose chosen charge is the slot
`(O, L)`. -/
noncomputable def Gfiber (W : Walk n) (s : RotClass × MarkedLoop) : Set ℕ :=
  {j ∈ W.Gset | W.charge j = s}

/-- Paper §5: `C`, the number of noninitial incident slots `(O,L)` (i.e. `L ≠ F(O)`)
with `|G_{O,L}| = 2`. -/
noncomputable def Cstat (W : Walk n) : ℕ :=
  {s | W.IncidentSlot s ∧ s.2 ≠ W.Fowner s.1 ∧ (W.Gfiber s).ncard = 2}.ncard

end Walk

/-- Paper §5 (Proposition "interface"): the seven facts (4), (5), (6a), (6b), (9), (10),
(11), read as constraints on the nine statistics `e, ℓ, |P|, |A|, |A₀|, q, |D|, C, v`. -/
def SystemFacts (n e ℓ P A A0 q D C v : ℕ) : Prop :=
  P ≤ e ∧
  A ≤ A0 + P ∧
  q = ℓ * (n - 1) ∧
  D ≤ ℓ * (n - 1) ∧
  C ≤ q ∧
  A0 ≤ q + D + C + n * P ∧
  v + C * (n - 3) ≤ (A + 1) * (n - 2)

end Coeff2
