import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-!
# Clock transport with a local port turn

This module describes the ordered port permutations of general-deficit
packets. It does NOT assume that a phase word is an available literal kernel,
or prove a cheap global superpermutation. The literal realization is checked
separately. Deficits here are packet surcharges, not bend lengths.
-/
namespace Coeff2.Charlieplex.ClockRefraction

def clock (h k j : ℕ) : ℕ := (j + k) % h

def prefixTurn (k j : ℕ) : ℕ :=
  if j = 0 then k - 1 else if j < k then j - 1 else j

-- k = deficit - 1. The exceptional end of the clock must not be discarded.
def deeperPort (h k j : ℕ) : ℕ :=
  if j < h - k then j + k
  else if j = h - k then k - 1
  else j - (h - k) - 1

theorem port_factorization (h k j : ℕ) (hk : 0 < k) (hkh : k < h)
    (hj : j < h) :
    deeperPort h k j = prefixTurn k (clock h k j) := by
  by_cases hl : j < h - k
  · have hs : j + k < h := by omega
    rw [deeperPort, if_pos hl, clock, Nat.mod_eq_of_lt hs]
    simp only [prefixTurn]
    split_ifs <;> omega
  · have hs : h ≤ j + k := by omega
    have hb : j + k - h < h := by omega
    have hm : (j + k) % h = j + k - h := by
      rw [Nat.mod_eq_sub_mod hs, Nat.mod_eq_of_lt hb]
    rw [clock, hm]
    simp only [deeperPort, if_neg hl, prefixTurn]
    split_ifs <;> omega

def predecessor (h j : ℕ) : ℕ := (j + h - 1) % h

theorem predecessor_zero (h : ℕ) (hh : 0 < h) : predecessor h 0 = h - 1 := by
  simp only [predecessor, zero_add]
  exact Nat.mod_eq_of_lt (by omega)

theorem predecessor_pos (h j : ℕ) (hj : 0 < j) (jh : j < h) :
    predecessor h j = j - 1 := by
  have he : j + h - 1 = (j - 1) + h := by omega
  simp only [predecessor, he, Nat.add_mod, Nat.mod_self, add_zero, Nat.mod_mod]
  exact Nat.mod_eq_of_lt (by omega)

-- Deficit word (0,3,3), in traversal order: rightmost operation acts first.
def refracted (h j : ℕ) : ℕ :=
  deeperPort h 2 (deeperPort h 2 (predecessor h j))

def joinedClock (h j : ℕ) : ℕ :=
  if j = 0 then 2
  else if j = h - 3 then 1
  else if j = h - 2 then 0
  else if j = h - 1 then 3
  else j + 3

theorem refraction_expansion (h j : ℕ) (hh : 6 ≤ h) (jh : j < h) :
    refracted h j = joinedClock h j := by
  by_cases hz : j = 0
  · subst j
    rw [refracted, predecessor_zero h (by omega)]
    simp only [deeperPort, joinedClock]
    split_ifs <;> omega
  · rw [refracted, predecessor_pos h j (by omega) jh]
    simp only [deeperPort, joinedClock]
    split_ifs <;> omega

-- This is an explicit orbit, not an inferred spectrum or merely a cycle count.
def phaseTrace (q t : ℕ) : ℕ :=
  if t = 0 then 0
  else if t ≤ q then 3 * (t - 1) + 2
  else if t < 2 * q then 3 * (t - q)
  else 3 * (t - 2 * q) + 1

theorem phaseTrace_lt (q t : ℕ) (hq : 2 ≤ q) (ht : t < 3 * q) :
    phaseTrace q t < 3 * q := by
  simp only [phaseTrace]
  split_ifs <;> omega

theorem phaseTrace_injective (q : ℕ) (_hq : 2 ≤ q) :
    Function.Injective (fun t : Fin (3 * q) => phaseTrace q t.val) := by
  intro a b he
  have ha := a.isLt
  have hb := b.isLt
  apply Fin.ext
  simp only [phaseTrace] at he
  split_ifs at he <;> omega

theorem phaseTrace_covers (q j : ℕ) (hq : 2 ≤ q) (hj : j < 3 * q) :
    ∃ t, t < 3 * q ∧ phaseTrace q t = j := by
  have hdecomp := Nat.mod_add_div j 3
  by_cases hz : j = 0
  · exact ⟨0, by omega, by simp [phaseTrace, hz]⟩
  · by_cases hr : j % 3 = 2
    · refine ⟨j / 3 + 1, by omega, ?_⟩
      have ht : j / 3 + 1 ≤ q := by omega
      rw [phaseTrace, if_neg (by omega), if_pos ht]
      simp only [Nat.add_sub_cancel]
      omega
    · by_cases hs : j % 3 = 0
      · refine ⟨j / 3 + q, by omega, ?_⟩
        simp only [phaseTrace]
        split_ifs <;> omega
      · refine ⟨j / 3 + 2 * q, by omega, ?_⟩
        simp only [phaseTrace]
        split_ifs <;> omega

theorem phaseTrace_step (q t : ℕ) (hq : 2 ≤ q) (ht : t < 3 * q) :
    joinedClock (3 * q) (phaseTrace q t) =
      phaseTrace q ((t + 1) % (3 * q)) := by
  by_cases hl : t + 1 < 3 * q
  · rw [Nat.mod_eq_of_lt hl]
    simp only [phaseTrace, joinedClock]
    split_ifs <;> omega
  · have he : t + 1 = 3 * q := by omega
    rw [he, Nat.mod_self]
    simp only [phaseTrace, joinedClock]
    split_ifs <;> omega

-- All clock phases occur once, with consecutive literal port maps matching.
theorem refracted_single_cycle (q : ℕ) (hq : 2 ≤ q) :
    Function.Injective (fun t : Fin (3 * q) => phaseTrace q t.val) ∧
    (∀ j < 3 * q, ∃ t, t < 3 * q ∧ phaseTrace q t = j) ∧
    (∀ t < 3 * q, refracted (3 * q) (phaseTrace q t) =
      phaseTrace q ((t + 1) % (3 * q))) := by
  refine ⟨phaseTrace_injective q hq, fun j hj => phaseTrace_covers q j hq hj, ?_⟩
  intro t ht
  rw [refraction_expansion (3 * q) _ (by omega) (phaseTrace_lt q t hq ht)]
  exact phaseTrace_step q t hq ht

-- Both patterns have charge six. This is NOT the final word's repeat count.
theorem equal_packet_charge : 2 + 2 + 2 = (0 + 3 + 3 : ℕ) := by decide

#print axioms port_factorization
#print axioms refraction_expansion
#print axioms refracted_single_cycle

end Coeff2.Charlieplex.ClockRefraction
