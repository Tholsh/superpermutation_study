import Coeff2.CharlieThreeLevelBoundary
import Coeff2.CharlieThreeSymbolFibers

/-! The three-symbol fiber catalogue is exactly the target permutation
universe, and its literal coverage is exactly the original IsSuperperm.
This closes the set-to-word specification bridge, not the construction. -/
namespace Coeff2.Charlieplex.ThreeLevelCoverage
open ThreeSymbolFibers

def catalogue (n : ℕ) : Finset (List ℕ) :=
  lift3 (n+1) (n+2) (n+3) (List.range' 1 n).permutations.toFinset

theorem enlarged_alphabet_valid (n : ℕ) :
    IsPermWord (n+3) ((n+3) :: (n+2) :: (n+1) :: List.range' 1 n) := by
  constructor
  · simp only [List.nodup_cons, List.mem_cons, List.mem_range'_1]
    exact ⟨by omega, by omega, by omega, List.nodup_range'⟩
  · ext x
    simp only [List.mem_toFinset, List.mem_cons, List.mem_range'_1, Finset.mem_Icc]
    omega

theorem mem_catalogue (n : ℕ) (p : List ℕ) :
    p ∈ catalogue n ↔ IsPermWord (n+3) p := by
  have ha : n+1 ∉ List.range' 1 n := by simp only [List.mem_range'_1]; omega
  have hb : n+2 ∉ List.range' 1 n := by simp only [List.mem_range'_1]; omega
  have hc : n+3 ∉ List.range' 1 n := by simp only [List.mem_range'_1]; omega
  rw [catalogue, lift3_universe _ _ _ _ (by omega) (by omega) (by omega) ha hb hc]
  have h := isPermWord_iff_perm_refList.mp (enlarged_alphabet_valid n)
  rw [List.mem_toFinset, List.mem_permutations, isPermWord_iff_perm_refList]
  exact ⟨fun hp => hp.trans h, fun hp => hp.trans h.symm⟩

/-- Full occupation of every literal insertion fiber is necessary AND
sufficient. Incidental seam windows and repeated occurrences remain legal. -/
theorem catalogue_coverage_iff (n : ℕ) (word : List ℕ) :
    catalogue n ⊆ literalOccupation (n+3) word ↔ IsSuperperm (n+3) word := by
  rw [← literalOccupation_covers_iff]
  constructor
  · intro h p hp
    exact h ((mem_catalogue n p).mpr hp)
  · intro h p hp
    exact h p ((mem_catalogue n p).mp hp)

#print axioms enlarged_alphabet_valid
#print axioms mem_catalogue
#print axioms catalogue_coverage_iff
end Coeff2.Charlieplex.ThreeLevelCoverage
