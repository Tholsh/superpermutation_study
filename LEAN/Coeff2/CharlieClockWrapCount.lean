import Coeff2.CharlieClockBudget

/-!
# Constant-size arithmetic for the forward wrap count

The finite wrap set is useful for proofs but should not be enumerated in the
solver. This module replaces its cardinality by one comparison and division.
-/
namespace Coeff2.Charlieplex.ClockBudget

def wrapCount (m L j : ℕ) : ℕ :=
  if j < L then 1 + (L - 1 - j) / m else 0

theorem lt_wrapCount_iff (m L j q : ℕ) (hm : 0 < m) :
    q < wrapCount m L j ↔ j + m * q < L := by
  unfold wrapCount
  by_cases hj : j < L
  · rw [if_pos hj, Nat.add_comm 1, Nat.lt_succ_iff, Nat.le_div_iff_mul_le hm]
    rw [Nat.mul_comm q m]
    omega
  · rw [if_neg hj]
    omega

theorem wrapSlots_card {m : ℕ} [NeZero m] (L : ℕ) (j : ZMod m) :
    (wrapSlots L j).card = wrapCount m L j.val := by
  have address (i : Fin L) (hi : i ∈ wrapSlots L j) :
      j.val + m * (i.val / m) = i.val := by
    have he : j = (i.val : ZMod m) := sub_eq_zero.mp (Finset.mem_filter.mp hi).2
    rw [he, ZMod.val_natCast]
    exact Nat.mod_add_div i.val m
  have hc : (wrapSlots L j).card = (Finset.range (wrapCount m L j.val)).card := by
    apply Finset.card_bij (fun i _ => i.val / m)
    · intro i hi
      apply Finset.mem_range.mpr
      rw [lt_wrapCount_iff m L j.val (i.val / m) (NeZero.pos m), address i hi]
      exact i.isLt
    · intro i hi k hk he
      apply Fin.ext
      rw [← address i hi, ← address k hk, he]
    · intro q hq
      have hlt : j.val + m * q < L :=
        (lt_wrapCount_iff m L j.val q (NeZero.pos m)).mp (Finset.mem_range.mp hq)
      let i : Fin L := ⟨j.val + m * q, hlt⟩
      have hi : i ∈ wrapSlots L j := by
        simp [wrapSlots, i, Nat.cast_add, Nat.cast_mul]
      refine ⟨i, hi, ?_⟩
      change (j.val + m * q) / m = q
      simp [Nat.add_mul_div_left, Nat.div_eq_of_lt j.val_lt, NeZero.pos m]
  simpa using hc

/-- This is the arithmetic bound evaluated by the native forward-tail code. -/
theorem closed_lowerBound {m : ℕ} [NeZero m] (L g : ℕ)
    (P : Finset (Fin L)) (j : ZMod m) :
    lowerBound L P.card (wrapCount m L j.val) g ≤
      (ClockMacro.compile (forwardPlan m L g P)).cost j := by
  rw [← wrapSlots_card]
  exact forwardPlan_lowerBound m L g P j

theorem closed_reject_all_orders {m : ℕ} [NeZero m]
    (L g f spent budget : ℕ) (j : ZMod m)
    (h : budget < spent + lowerBound L f (wrapCount m L j.val) g) :
    ∀ P : Finset (Fin L), P.card = f →
      budget < (ClockMacro.run (forwardPlan m L g P) (j, spent)).2 := by
  apply reject_all_forward_orders
  simpa [wrapSlots_card] using h

end Coeff2.Charlieplex.ClockBudget
