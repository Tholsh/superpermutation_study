import Mathlib.GroupTheory.Perm.Closure
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Data.Fintype.Perm

/-!
# Literal cheap-move gauge rigidity

A literal permutation state is a bijection from positions to symbols. Position
permutations act on the right; alphabet relabelings act on the left. Preserving
both the directed R1 and canonical R2 moves forces one global alphabet map.
This is NOT a claim about arbitrary changes of coordinates, word reversal,
or coverage-preserving multi-edge splices.
-/
namespace Coeff2.Charlieplex.LiteralGaugeRigidity
open Equiv Equiv.Perm

abbrev State (n : ℕ) := Equiv.Perm (Fin n)

/-- `p(1),p(2),...,p(n-1),p(0)`. -/
def R1 {n : ℕ} (p : State n) : State n := p * finRotate n

/-- For `n >= 2`: `p(2),...,p(n-1),p(1),p(0)`.
The order is written `k+2` to supply the two literal positions without axioms. -/
def R2 {k : ℕ} (p : State (k+2)) : State (k+2) :=
  p * (swap 0 1 * finRotate (k+2) ^ 2)

theorem R1_at {k : ℕ} (p : State (k+1)) (i : Fin (k+1)) :
    R1 p i = p (i+1) := by
  simp [R1, mul_apply, finRotate_apply]

theorem R2_at {k : ℕ} (p : State (k+2)) (i : Fin (k+2)) :
    R2 p i = p (swap (0 : Fin (k+2)) 1 ((i+1)+1)) := by
  simp [R2, pow_two, mul_apply, finRotate_apply]

theorem recover_first_swap {k : ℕ} (p : State (k+2)) :
    R2 p * (finRotate (k+2) ^ 2)⁻¹ = p * swap 0 1 := by
  simp [R2, mul_assoc]

/-- The right translations with which a state function commutes form a subgroup. -/
def commutingRight {G : Type*} [Group G] (f : G → G) : Subgroup G where
  carrier := {g | ∀ p, f (p*g) = f p*g}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb p
    rw [← mul_assoc, hb, ha, mul_assoc]
  inv_mem' := by
    intro a ha p
    have h := ha (p*a⁻¹)
    simpa [mul_assoc] using congrArg (fun z => z*a⁻¹) h.symm

theorem cheap_generators_span (k : ℕ) :
    Subgroup.closure ({finRotate (k+2),
      swap (0 : Fin (k+2)) 1 * finRotate (k+2)^2} : Set (State (k+2))) = ⊤ := by
  let H := Subgroup.closure ({finRotate (k+2),
    swap (0 : Fin (k+2)) 1 * finRotate (k+2)^2} : Set (State (k+2)))
  have hc : finRotate (k+2) ∈ H := Subgroup.subset_closure (by simp)
  have ht : swap (0 : Fin (k+2)) 1 * finRotate (k+2)^2 ∈ H :=
    Subgroup.subset_closure (by simp)
  have hs : swap (0 : Fin (k+2)) 1 ∈ H := by
    have h := H.mul_mem ht (H.inv_mem (H.pow_mem hc 2))
    simpa using h
  have hgen := closure_cycle_adjacent_swap
    (isCycle_finRotate (n := k)) (support_finRotate (n := k)) (0 : Fin (k+2))
  have hle : Subgroup.closure
      ({finRotate (k+2), swap (0 : Fin (k+2)) 1} : Set (State (k+2))) ≤ H := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hc
    · exact hs
  have he : finRotate (k+2) (0 : Fin (k+2)) = 1 := finRotate_apply_zero
  rw [he] at hgen
  rw [hgen] at hle
  exact top_le_iff.mp hle

/-- No bijectivity assumption on `f` is needed. Even a function preserving
these two moves must be one globally consistent alphabet relabeling. -/
theorem preserves_cheap_iff_relabel {k : ℕ} (f : State (k+2) → State (k+2)) :
    ((∀ p, f (R1 p) = R1 (f p)) ∧ (∀ p, f (R2 p) = R2 (f p))) ↔
      ∃ a : State (k+2), ∀ p, f p = a*p := by
  constructor
  · rintro ⟨h1,h2⟩
    have hle : Subgroup.closure ({finRotate (k+2),
        swap (0 : Fin (k+2)) 1 * finRotate (k+2)^2} : Set (State (k+2))) ≤
        commutingRight f := by
      rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact h1
      · exact h2
    rw [cheap_generators_span] at hle
    refine ⟨f 1, fun p => ?_⟩
    have hp : p ∈ commutingRight f := hle (Subgroup.mem_top p)
    simpa using hp 1
  · rintro ⟨a,ha⟩
    constructor <;> intro p <;> simp [ha, R1, R2, mul_assoc]

theorem relabel_is_unique {k : ℕ} (f : State (k+2) → State (k+2))
    (a b : State (k+2)) (ha : ∀ p, f p = a*p) (hb : ∀ p, f p = b*p) :
    a = b := by
  simpa using (ha 1).symm.trans (hb 1)

/-- Pointwise literal interpretation: the same alphabet map is used at
every position of every permutation state. -/
theorem preserves_cheap_literal {k : ℕ} (f : State (k+2) → State (k+2))
    (h1 : ∀ p, f (R1 p) = R1 (f p)) (h2 : ∀ p, f (R2 p) = R2 (f p)) :
    ∀ p i, f p i = f 1 (p i) := by
  obtain ⟨a,ha⟩ := (preserves_cheap_iff_relabel f).mp ⟨h1,h2⟩
  intro p i
  simp [ha, mul_apply]

def CheapGauge (k : ℕ) :=
  {f : State (k+2) → State (k+2) //
    (∀ p, f (R1 p) = R1 (f p)) ∧ (∀ p, f (R2 p) = R2 (f p))}

/-- Evaluation at the identity is an explicit equivalence, not just an upper
bound on the number of literal cheap-move gauges. -/
def gaugeEquiv (k : ℕ) : CheapGauge k ≃ State (k+2) where
  toFun f := f.val 1
  invFun a := ⟨fun p => a*p, by
    constructor <;> intro p <;> simp [R1, R2, mul_assoc]⟩
  left_inv f := by
    apply Subtype.ext
    funext p
    apply Equiv.ext
    intro i
    exact (preserves_cheap_literal f.val f.property.1 f.property.2 p i).symm
  right_inv a := by simp

theorem number_of_literal_gauges (k : ℕ) :
    Nat.card (CheapGauge k) = (k+2).factorial := by
  rw [Nat.card_congr (gaugeEquiv k)]
  simp [State, Nat.card_eq_fintype_card, Fintype.card_perm]

#print axioms cheap_generators_span
#print axioms preserves_cheap_iff_relabel
#print axioms preserves_cheap_literal
#print axioms number_of_literal_gauges

end Coeff2.Charlieplex.LiteralGaugeRigidity
