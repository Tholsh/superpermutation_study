import Coeff2.CharlieAttachmentReduction
import Coeff2.CharlieClockSlack
import Coeff2.CharlieLiteralCompletions

/-!
# Literal attachment paths, Bellman budgets, and pigeonhole forcing

Reuses the existing literal Arc and Path. A local phase/price extraction must
be supplied and checked for the generator in use. Actual boundary strings
and coverage witnesses are retained; equal costs are never identified as
equal literal states. The capacity theorem works on any integer-weighted
set of ports, including cut indicators.
-/
namespace Coeff2.Charlieplex.AttachmentReduction
open ClockBellman
open scoped BigOperators
variable {α : Type*} {m : ℕ}

theorem literal_clock_lower_bound (C : Model m) (kind : Arc α → Kind)
    (phase : List α → ZMod m) {s t : List α} {as : List (Arc α)}
    (hp : Path s t as)
    (hs : ∀ a ∈ as, phase a.exit = phase a.entry + (C.move (kind a)).shift)
    (hc : ∀ a ∈ as, (C.move (kind a)).cost (phase a.entry) ≤ a.payload.length) :
    wordCost C (as.map kind) (phase s) ≤ (payload as).length := by
  induction hp with
  | nil s => simp [payload]
  | @cons a t as rest ih =>
    have he := hs a (by simp)
    have hcost := hc a (by simp)
    have hh := ih (fun b hb => hs b (by simp [hb]))
      (fun b hb => hc b (by simp [hb]))
    simp only [List.map_cons, wordCost_cons]
    rw [← he]
    simpa [payload] using Nat.add_le_add hcost hh

theorem literal_clock_cost (C : Model m) (kind : Arc α → Kind)
    (phase : List α → ZMod m) {s t : List α} {as : List (Arc α)}
    (hp : Path s t as)
    (hs : ∀ a ∈ as, phase a.exit = phase a.entry + (C.move (kind a)).shift)
    (hc : ∀ a ∈ as, a.payload.length = (C.move (kind a)).cost (phase a.entry)) :
    (payload as).length = wordCost C (as.map kind) (phase s) := by
  induction hp with
  | nil s => simp [payload]
  | @cons a t as rest ih =>
    have he := hs a (by simp)
    have hcost := hc a (by simp)
    have hh := ih (fun b hb => hs b (by simp [hb]))
      (fun b hb => hc b (by simp [hb]))
    simp only [List.map_cons, wordCost_cons]
    rw [← he, ← hcost, ← hh]
    simp [payload]

theorem reject_literal_path [NeZero m] (g base wrap f o b budget : ℕ)
    (kind : Arc α → Kind) (phase : List α → ZMod m)
    {s t : List α} {as : List (Arc α)} (hp : Path s t as)
    (hs : ∀ a ∈ as, phase a.exit = phase a.entry +
      ((clock m g base wrap).move (kind a)).shift)
    (hc : ∀ a ∈ as, ((clock m g base wrap).move (kind a)).cost (phase a.entry)
      ≤ a.payload.length)
    (counts : Schedule f o b (as.map kind))
    (tooSmall : budget < s.length + hybrid g base wrap f o b (phase s)) :
    budget < (s ++ payload as).length := by
  have hh := literal_clock_lower_bound (clock m g base wrap) kind phase hp hs hc
  have hb := optimum_le_every_word (clock m g base wrap) counts (phase s)
  rw [← hybrid_eq_optimum] at hb
  simp only [List.length_append]
  omega

/-- With exact local prices, the excess ledger is an identity about emitted
characters, not merely about the projected clock interpreter. -/
theorem literal_excess_identity (C : Model m) (kind : Arc α → Kind)
    (phase : List α → ZMod m) {s t : List α} {as : List (Arc α)}
    (hp : Path s t as)
    (hs : ∀ a ∈ as, phase a.exit = phase a.entry + (C.move (kind a)).shift)
    (hc : ∀ a ∈ as, a.payload.length = (C.move (kind a)).cost (phase a.entry)) :
    (s ++ payload as).length = s.length + potential C (as.map kind) (phase s) +
      (excesses C (as.map kind) (phase s)).sum := by
  rw [List.length_append, literal_clock_cost C kind phase hp hs hc,
    cost_eq_potential_add_excess]
  omega

/-- The literal edge ledger telescopes at every port or union of ports.
Choose score = indicator of a set of boundary frames for a cut equation. -/
theorem path_port_ledger (score : List α → ℤ)
    {s t : List α} {as : List (Arc α)} (hp : Path s t as) :
    (as.map (fun a => score a.entry - score a.exit)).sum = score s - score t := by
  induction hp with
  | nil s => simp
  | cons a rest ih => simp only [List.map_cons, List.sum_cons, ih]; omega

/-- Tight pigeonhole capacity: if selected contributions sum to the sum of
their individual upper bounds, every contribution attains its upper bound.
This is necessary, not sufficient, for a connected literal attachment. -/
theorem capacity_saturated {ι : Type*} (I : Finset ι) (w upper : ι → ℤ)
    (hbound : ∀ i ∈ I, w i ≤ upper i)
    (htotal : ∑ i ∈ I, w i = ∑ i ∈ I, upper i) :
    ∀ i ∈ I, w i = upper i := by
  have hz : ∑ i ∈ I, (upper i - w i) = 0 := by
    rw [Finset.sum_sub_distrib, htotal, sub_self]
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i hi => sub_nonneg.mpr (hbound i hi))).mp hz
  intro i hi
  have := hzero i hi
  omega

/-- A phase choice below a saturated capacity cannot occur in any completion
of these domains. The chosen option need not be unique. -/
theorem selected_phase_forced {ι β : Type*} (I : Finset ι)
    (domain : ι → Finset β) (contribution : ι → β → ℤ)
    (upper : ι → ℤ) (selected : ι → β)
    (hmem : ∀ i ∈ I, selected i ∈ domain i)
    (hbound : ∀ i ∈ I, ∀ q ∈ domain i, contribution i q ≤ upper i)
    (htotal : ∑ i ∈ I, contribution i (selected i) = ∑ i ∈ I, upper i) :
    ∀ i ∈ I, contribution i (selected i) = upper i :=
  capacity_saturated I (fun i => contribution i (selected i)) upper
    (fun i hi => hbound i hi _ (hmem i hi)) htotal

/-- Two ports of each of two exactly-one modules: the four-term flow law
splits into two equalities. Integrality and the within-module exclusion are
essential. This is not a valid operation on an arbitrary relaxed real flow. -/
theorem two_module_balance (a b c d : ℕ)
    (first : a + c ≤ 1) (second : b + d ≤ 1) :
    a + b = c + d ↔ a = d ∧ b = c := by
  omega

theorem distinct_phases_exclusive {β : Type*} [DecidableEq β]
    (selected q r : β) (distinct : q ≠ r) :
    (if selected = q then 1 else 0) + (if selected = r then 1 else 0) ≤ (1 : ℕ) := by
  split_ifs <;> simp_all

/-- If equality propagation identifies distinct phases in one module,
both phases are forbidden by occupation's exactly-one constraint. -/
theorem equal_exclusive_phases_zero (a c : ℕ) (exclusive : a + c ≤ 1)
    (equal : a = c) : a = 0 ∧ c = 0 := by
  omega

/-- Coverage is still proved from literal arc witnesses. A phase or ledger
test alone is not substituted for occupation. -/
theorem path_occupation {s t : List α} {as : List (Arc α)} (hp : Path s t as)
    (alphabet : List α)
    (covers : ∀ p : List α, p.Perm alphabet → ∃ a ∈ as, p.IsInfix a.word) :
    ∀ p : List α, p.Perm alphabet → p.IsInfix (s ++ payload as) := by
  intro p h
  obtain ⟨a, ha, hi⟩ := covers p h
  exact hi.trans (path_contains hp a ha)

#print axioms literal_clock_lower_bound
#print axioms literal_clock_cost
#print axioms reject_literal_path
#print axioms literal_excess_identity
#print axioms path_port_ledger
#print axioms capacity_saturated
#print axioms selected_phase_forced
#print axioms two_module_balance
#print axioms distinct_phases_exclusive
#print axioms equal_exclusive_phases_zero
#print axioms path_occupation
end Coeff2.Charlieplex.AttachmentReduction
