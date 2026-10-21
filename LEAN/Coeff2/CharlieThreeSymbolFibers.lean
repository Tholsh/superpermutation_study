import Coeff2.CharlieEganOccupationLift
import Mathlib.Tactic

/-! Exact three-symbol occupation fibers. These are literal permutation
catalogues, NOT claims about cheap ordering or connected realization. -/
namespace Coeff2.Charlieplex.ThreeSymbolFibers
open Finset EganOccupationLift
variable {α : Type*} [DecidableEq α]

def lift3 (a b c : α) (U : Finset (List α)) : Finset (List α) :=
  occupationLift c (occupationLift b (occupationLift a U))

theorem lift_length (a : α) (U : Finset (List α)) (m : ℕ)
    (hl : ∀ p ∈ U, p.length = m) :
    ∀ p ∈ occupationLift a U, p.length = m+1 := by
  intro p hp
  obtain ⟨q, hq, hpq⟩ := mem_biUnion.mp hp
  have h := (insertionFiber_perm hpq).length_eq
  simpa [hl q hq, Nat.add_comm] using h

/-- The exact decoder: membership requires all three actual symbols and
membership of the erased word, not just a matching fiber count. -/
theorem mem_lift3 (a b c : α) (U : Finset (List α)) (w : List α)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : ∀ p ∈ U, a ∉ p) (hb : ∀ p ∈ U, b ∉ p) (hc : ∀ p ∈ U, c ∉ p) :
    w ∈ lift3 a b c U ↔
      c ∈ w ∧ b ∈ w ∧ a ∈ w ∧ ((w.erase c).erase b).erase a ∈ U := by
  have hbA := occupationLift_fresh a b U hab.symm hb
  have hcA := occupationLift_fresh a c U hac.symm hc
  have hcB := occupationLift_fresh b c (occupationLift a U) hbc.symm hcA
  rw [lift3, mem_occupationLift c _ w hcB,
    mem_occupationLift b _ (w.erase c) hbA,
    mem_occupationLift a U ((w.erase c).erase b) ha]
  simp only [List.mem_erase_of_ne hbc, List.mem_erase_of_ne hab,
    List.mem_erase_of_ne hac]

/-- There are exactly (m+1)(m+2)(m+3) distinct extensions per old word.
Freshness and disjoint deletion fibers prevent double-counting. -/
theorem lift3_card (a b c : α) (U : Finset (List α)) (m : ℕ)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : ∀ p ∈ U, a ∉ p) (hb : ∀ p ∈ U, b ∉ p) (hc : ∀ p ∈ U, c ∉ p)
    (hl : ∀ p ∈ U, p.length = m) :
    (lift3 a b c U).card = U.card * (m+1) * (m+2) * (m+3) := by
  have hbA := occupationLift_fresh a b U hab.symm hb
  have hcA := occupationLift_fresh a c U hac.symm hc
  have hcB := occupationLift_fresh b c (occupationLift a U) hbc.symm hcA
  have hlA := lift_length a U m hl
  have hlB := lift_length b (occupationLift a U) (m+1) hlA
  unfold lift3
  rw [occupationLift_card_uniform c _ (m+2) hcB (by simpa [Nat.add_assoc] using hlB),
    occupationLift_card_uniform b _ (m+1) hbA hlA,
    occupationLift_card_uniform a U m ha hl]

theorem lift3_universe (a b c : α) (alphabet : List α)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : a ∉ alphabet) (hb : b ∉ alphabet) (hc : c ∉ alphabet) :
    lift3 a b c alphabet.permutations.toFinset =
      (c :: b :: a :: alphabet).permutations.toFinset := by
  unfold lift3
  rw [occupationLift_permutations a alphabet ha,
    occupationLift_permutations b (a :: alphabet) (by simp [hab.symm, hb]),
    occupationLift_permutations c (b :: a :: alphabet) (by simp [hac.symm, hbc.symm, hc])]

/-- Exact collision preservation, including partial old occupation. -/
theorem lift3_inter (a b c : α) (U V : Finset (List α))
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (haU : ∀ p ∈ U, a ∉ p) (hbU : ∀ p ∈ U, b ∉ p) (hcU : ∀ p ∈ U, c ∉ p)
    (haV : ∀ p ∈ V, a ∉ p) (hbV : ∀ p ∈ V, b ∉ p) (hcV : ∀ p ∈ V, c ∉ p) :
    lift3 a b c (U ∩ V) = lift3 a b c U ∩ lift3 a b c V := by
  have hbAU := occupationLift_fresh a b U hab.symm hbU
  have hbAV := occupationLift_fresh a b V hab.symm hbV
  have hcBU := occupationLift_fresh b c (occupationLift a U) hbc.symm
    (occupationLift_fresh a c U hac.symm hcU)
  have hcBV := occupationLift_fresh b c (occupationLift a V) hbc.symm
    (occupationLift_fresh a c V hac.symm hcV)
  unfold lift3
  rw [occupationLift_inter a U V haU haV,
    occupationLift_inter b _ _ hbAU hbAV,
    occupationLift_inter c _ _ hcBU hcBV]

/-- The whole-fiber occupation map is reversible by actual deletion.
This is NOT a compression theorem for arbitrary partially occupied fibers. -/
theorem decode_lift3 (a b c : α) (U : Finset (List α))
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : ∀ p ∈ U, a ∉ p) (hb : ∀ p ∈ U, b ∉ p) (hc : ∀ p ∈ U, c ∉ p) :
    (lift3 a b c U).image (fun w => ((w.erase c).erase b).erase a) = U := by
  ext p
  simp only [mem_image]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ((mem_lift3 a b c U w hab hac hbc ha hb hc).mp hw).2.2.2
  · intro hp
    refine ⟨c :: b :: a :: p, ?_, ?_⟩
    · apply (mem_lift3 a b c U _ hab hac hbc ha hb hc).mpr
      simp [hp]
    · simp

/-- Summing m(m+1) charge over the (m-1)! rooted lower frames gives
(m+1)! exactly. This is arithmetic, not a universal charge lower bound. -/
theorem layer_charge_factorial (m : ℕ) (hm : 1 ≤ m) :
    (m-1).factorial * m * (m+1) = (m+1).factorial := by
  have h : m.factorial = m * (m-1).factorial := by
    simpa [Nat.sub_add_cancel hm] using Nat.factorial_succ (m-1)
  rw [Nat.factorial_succ, h]
  ring

/-- The same formula acts on the tail of a retained root: if the smaller
order is n, each rooted tail has n(n+1)(n+2) extensions. This counts rooted
frames, not phase choices or cheap attachments. -/
theorem rooted_tail_card (a b c : α) (tail : List α)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : a ∉ tail) (hb : b ∉ tail) (hc : c ∉ tail) :
    (lift3 a b c {tail}).card =
      (tail.length+1)*(tail.length+2)*(tail.length+3) := by
  simpa using lift3_card a b c {tail} tail.length hab hac hbc
    (by simpa) (by simpa) (by simpa) (by simp)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
example : (lift3 6 7 8 ({[2,3,4,5]} : Finset (List ℕ))).card = 210 := by decide
example : (lift3 9 10 11 ({[2,3,4,5,6,7,8]} : Finset (List ℕ))).card = 720 := by
  rw [rooted_tail_card] <;> decide

#print axioms mem_lift3
#print axioms lift3_card
#print axioms lift3_universe
#print axioms lift3_inter
#print axioms decode_lift3
#print axioms layer_charge_factorial
#print axioms rooted_tail_card
end Coeff2.Charlieplex.ThreeSymbolFibers
