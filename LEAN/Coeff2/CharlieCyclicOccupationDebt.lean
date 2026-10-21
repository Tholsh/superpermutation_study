import Coeff2.CharlieJayClassCut
import Mathlib.Logic.Equiv.Fin.Rotate

/-! A partial occupation of a finite directed phase clock either fills the
clock or creates an exit. The sum bound is independent of the alphabet n.
This is NOT by itself a lower bound for arbitrary superpermutations: literal
row/header correspondence and paid-entry obligations must also be proved.
-/
namespace Coeff2.Charlieplex.CyclicOccupationDebt
open JayClassCut
variable {X I : Type*} [Fintype X] [DecidableEq X] [DecidableEq I]

def exits (next : X → X) (active : Finset X) : Finset X :=
  active.filter (fun x => next x ∉ active)

def debt (next : X → X) (active : Finset X) : ℕ :=
  if active = Finset.univ then 1 else (exits next active).card

/-- Proper, nonempty occupation cannot have zero boundary debt on one
transitive finite clock. No probability or entropy assumption is used. -/
theorem cycle_debt_bound (h : ℕ) (next : X → X) (active : Finset X)
    (hsize : Fintype.card X ≤ h)
    (hclock : ∀ x y, ∃ k, advance next x k = y) :
    active.card ≤ h * debt next active := by
  classical
  by_cases hall : active = Finset.univ
  · simpa [debt, hall] using hsize
  by_cases hempty : active = ∅
  · simp [hempty]
  obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  have outside : ∃ y, y ∉ active := by
    by_contra hn
    push Not at hn
    apply hall
    ext y
    simp [hn y]
  obtain ⟨y, hy⟩ := outside
  obtain ⟨u, hu, hout⟩ := necessary_exit next (active : Set X) hclock ⟨x, hx⟩ ⟨y, hy⟩
  have hp : (exits next active).Nonempty :=
    ⟨u, Finset.mem_filter.mpr ⟨hu, hout⟩⟩
  have hone : 1 ≤ (exits next active).card :=
    Nat.succ_le_of_lt (Finset.card_pos.mpr hp)
  calc
    active.card ≤ Fintype.card X := Finset.card_le_univ _
    _ ≤ h := hsize
    _ ≤ h * (exits next active).card := by
      simpa using Nat.mul_le_mul_left h hone
    _ = h * debt next active := by simp [debt, hall]

/-- Sum over a clock partition. Literal applications must identify this
sum of active cardinalities with the selected occupation-fiber count. -/
theorem clock_sum_bound (clocks : Finset I) (h : ℕ) (next : X → X)
    (active : I → Finset X) (hsize : Fintype.card X ≤ h)
    (hclock : ∀ x y, ∃ k, advance next x k = y) :
    (∑ i ∈ clocks, (active i).card) ≤ h * (∑ i ∈ clocks, debt next (active i)) := by
  calc
    _ ≤ ∑ i ∈ clocks, h * debt next (active i) := by
      apply Finset.sum_le_sum
      intro i _hi
      exact cycle_debt_bound h next (active i) hsize hclock
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem advance_eq_iterate (next : X → X) (x : X) (k : ℕ) :
    advance next x k = (next^[k]) x := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [advance, ih, Function.iterate_succ_apply']

/-- The standard radix clock reaches every phase; this is proved rather
than left as a transitivity hypothesis of the counting bound. -/
theorem fin_phase_reachable (h : ℕ) (x y : Fin h) :
    ∃ k, advance (finRotate h) x k = y := by
  haveI := x.neZero
  let d : Fin h := y-x
  refine ⟨d.val, ?_⟩
  rw [advance_eq_iterate, ← finCycle_eq_finRotate_iterate]
  change x+d = y
  dsimp [d]
  abel

theorem fin_clock_bound (h : ℕ) (active : Finset (Fin h)) :
    active.card ≤ h * debt (finRotate h) active := by
  exact cycle_debt_bound h (finRotate h) active (by simp) (fin_phase_reachable h)

#print axioms cycle_debt_bound
#print axioms clock_sum_bound
#print axioms fin_phase_reachable
#print axioms fin_clock_bound
end Coeff2.Charlieplex.CyclicOccupationDebt
