import Coeff2.CharlieThreeLevelBoundary
import Coeff2.CharlieThreeLevelCoverage

/-! Exact internal replacement in arbitrary literal contexts. No no-repeat
hypothesis: occupation means the set of actual permutation windows. -/
namespace Coeff2.Charlieplex.ContextReplacement
open LiteralReservoir ThreeLevelBoundary

theorem lastSymbols_long_append (count : ℕ) (before word : List ℕ)
    (h : count ≤ word.length) :
    lastSymbols count (before ++ word) = lastSymbols count word := by
  induction before with
  | nil => simp
  | cons x xs ih =>
    rw [List.cons_append, lastSymbols_cons count x (xs ++ word) (by
      simp only [List.length_append]; omega), ih]

theorem occupation_append (n : ℕ) (hn : 1 ≤ n) (before word : List ℕ) :
    (literalStateOf n (before ++ word)).occupied =
      (literalStateOf n before).occupied ∪
        (emitted n (lastSymbols (n-1) before) word).toFinset := by
  have h := run_occupation n (literalStateOf n before) word
  rw [literalStateRun_correct n hn] at h
  exact h

/-- Writing a shared full boundary absorbs all earlier context. Its seam
windows are retained in prefix++head, not discarded. -/
theorem occupation_shared_head (n : ℕ) (hn : 1 ≤ n)
    (before head tail : List ℕ) (hh : head.length = n-1) :
    (literalStateOf n (before ++ (head ++ tail))).occupied =
      (literalStateOf n (before ++ head)).occupied ∪
        (literalStateOf n (head ++ tail)).occupied := by
  have hb : lastSymbols (n-1) (before ++ head) = head := by
    rw [lastSymbols_long_append _ _ _ (by omega),
      lastSymbols_of_short _ _ (by omega)]
  have hz : (literalStateOf n head).occupied = ∅ := by
    change (literalPermutationWindows n head).toFinset = ∅
    rw [literalPermutationWindows_eq_nil_of_short n head (by omega)]
    rfl
  rw [← List.append_assoc, occupation_append n hn, hb,
    occupation_append n hn head tail, hz,
    lastSymbols_of_short _ _ (by omega), Finset.empty_union]

/-- Equal first n-1 symbols, equal last n-1 symbols, and equal internal
occupation allow replacement anywhere, not merely at the initial prefix.
The two routes may have different lengths or repeat histories. -/
theorem replace_internal (n : ℕ) (hn : 1 ≤ n)
    (before head leftTail rightTail suffix : List ℕ)
    (hh : head.length = n-1)
    (hb : lastSymbols (n-1) (head ++ leftTail) =
      lastSymbols (n-1) (head ++ rightTail))
    (ho : (literalStateOf n (head ++ leftTail)).occupied =
      (literalStateOf n (head ++ rightTail)).occupied) :
    IsSuperperm n (before ++ (head ++ leftTail) ++ suffix) ↔
      IsSuperperm n (before ++ (head ++ rightTail) ++ suffix) := by
  apply literal_replacement n hn
  · change lastSymbols (n-1) (before ++ (head ++ leftTail)) =
      lastSymbols (n-1) (before ++ (head ++ rightTail))
    rw [lastSymbols_long_append (n-1) before (head ++ leftTail)
        (by simp only [List.length_append]; omega),
      lastSymbols_long_append (n-1) before (head ++ rightTail)
        (by simp only [List.length_append]; omega), hb]
  · rw [occupation_shared_head n hn before head leftTail hh,
      occupation_shared_head n hn before head rightTail hh, ho]

/-- Direct interface for certificates produced by the native checker. -/
theorem replace_words (n : ℕ) (hn : 1 ≤ n)
    (before left right suffix : List ℕ)
    (hl : n-1 ≤ left.length) (hr : n-1 ≤ right.length)
    (hfirst : left.take (n-1) = right.take (n-1))
    (hlast : lastSymbols (n-1) left = lastSymbols (n-1) right)
    (hocc : (literalStateOf n left).occupied = (literalStateOf n right).occupied) :
    IsSuperperm n (before ++ left ++ suffix) ↔
      IsSuperperm n (before ++ right ++ suffix) := by
  have hleft : left.take (n-1) ++ left.drop (n-1) = left :=
    List.take_append_drop _ _
  have hright : left.take (n-1) ++ right.drop (n-1) = right := by
    rw [hfirst]
    exact List.take_append_drop _ _
  have h := replace_internal n hn before (left.take (n-1))
    (left.drop (n-1)) (right.drop (n-1)) suffix
    (by simp only [List.length_take, Nat.min_eq_left hl])
    (by simpa only [hleft, hright] using hlast)
    (by simpa only [hleft, hright] using hocc)
  simpa only [hleft, hright] using h

theorem replace_valid (n : ℕ) (hn : 1 ≤ n)
    (before left right suffix : List ℕ)
    (hl : n-1 ≤ left.length) (hr : n-1 ≤ right.length)
    (hfirst : left.take (n-1) = right.take (n-1))
    (hlast : lastSymbols (n-1) left = lastSymbols (n-1) right)
    (hocc : (literalStateOf n left).occupied = (literalStateOf n right).occupied)
    (halpha : literalAlphabetTest n left = literalAlphabetTest n right) :
    Valid n (before ++ left ++ suffix) ↔ Valid n (before ++ right ++ suffix) := by
  have hc := replace_words n hn before left right suffix hl hr hfirst hlast hocc
  unfold Valid
  have ha : literalAlphabetTest n (before ++ left ++ suffix) =
      literalAlphabetTest n (before ++ right ++ suffix) := by
    simpa only [literalAlphabetTest, List.all_append] using
      congrArg (fun b => (literalAlphabetTest n before && b) &&
        literalAlphabetTest n suffix) halpha
  rw [ha, hc]

theorem replacement_saving (before left right suffix : List ℕ) (saving : ℕ)
    (h : right.length + saving = left.length) :
    (before ++ right ++ suffix).length + saving =
      (before ++ left ++ suffix).length := by
  simp only [List.length_append]
  omega

/-- The fixed outside includes both seam regions. It is not merely the
occupation of the separately scanned prefix and suffix. -/
def outsideOccupation (n : ℕ) (before head tail after : List ℕ) :
    Finset (List ℕ) :=
  (literalStateOf n (before ++ head)).occupied ∪
    (emitted n (lastSymbols (n-1) (head ++ tail)) after).toFinset

theorem occupation_context (n : ℕ) (hn : 1 ≤ n)
    (before head tail after : List ℕ) (hh : head.length = n-1) :
    (literalStateOf n (before ++ (head ++ tail) ++ after)).occupied =
      outsideOccupation n before head tail after ∪
        (literalStateOf n (head ++ tail)).occupied := by
  rw [occupation_append n hn,
    lastSymbols_long_append (n-1) before (head ++ tail)
      (by simp only [List.length_append]; omega),
    occupation_shared_head n hn before head tail hh]
  unfold outsideOccupation
  ext p
  simp only [Finset.mem_union]
  tauto

/-- A strictly more permissive rule: internal footprints may differ on
permutations already covered outside. No assumption of whole-course routes,
injectivity, or equal numbers of occurrences is made. -/
theorem replace_masked (n : ℕ) (hn : 1 ≤ n)
    (before head leftTail rightTail after : List ℕ)
    (hh : head.length = n-1)
    (hb : lastSymbols (n-1) (head ++ leftTail) =
      lastSymbols (n-1) (head ++ rightTail))
    (hm : outsideOccupation n before head leftTail after ∪
        (literalStateOf n (head ++ leftTail)).occupied =
      outsideOccupation n before head leftTail after ∪
        (literalStateOf n (head ++ rightTail)).occupied) :
    IsSuperperm n (before ++ (head ++ leftTail) ++ after) ↔
      IsSuperperm n (before ++ (head ++ rightTail) ++ after) := by
  have hout : outsideOccupation n before head leftTail after =
      outsideOccupation n before head rightTail after := by
    simp only [outsideOccupation, hb]
  have heq : (literalStateOf n (before ++ (head ++ leftTail) ++ after)).occupied =
      (literalStateOf n (before ++ (head ++ rightTail) ++ after)).occupied := by
    rw [occupation_context n hn before head leftTail after hh,
      occupation_context n hn before head rightTail after hh, ← hout, hm]
  rw [← literalOccupation_covers_iff n _, ← literalOccupation_covers_iff n _]
  change (∀ p, IsPermWord n p → p ∈
    (literalStateOf n (before ++ (head ++ leftTail) ++ after)).occupied) ↔ _
  rw [heq]
  rfl

#print axioms replace_internal
 /-- Exact remaining obligation in a fixed context. This does not require
 maintaining internal occupation that the outside has already supplied. -/
theorem completion_residual (n : ℕ) (hn : 1 ≤ n)
    (before head tail after : List ℕ) (hh : head.length = n-1) :
    IsSuperperm n (before ++ (head ++ tail) ++ after) ↔
      ∀ p, IsPermWord n p →
        p ∉ outsideOccupation n before head tail after →
        p ∈ (literalStateOf n (head ++ tail)).occupied := by
  rw [← literalOccupation_covers_iff n _]
  change (∀ p, IsPermWord n p → p ∈
    (literalStateOf n (before ++ (head ++ tail) ++ after)).occupied) ↔ _
  rw [occupation_context n hn before head tail after hh]
  simp only [Finset.mem_union]
  constructor
  · intro h p hp hnC
    exact (h p hp).resolve_left hnC
  · intro h p hp
    by_cases hc : p ∈ outsideOccupation n before head tail after
    · exact Or.inl hc
    · exact Or.inr (h p hp hc)

#print axioms completion_residual

/-- The three-level catalogue minus the fixed seam-aware outside is the
EXACT obligation, not an assumed compression by orbit cardinalities. -/
theorem three_level_residual (n : ℕ) (before head tail after : List ℕ)
    (hh : head.length = n+2) :
    IsSuperperm (n+3) (before ++ (head ++ tail) ++ after) ↔
      ThreeLevelCoverage.catalogue n \
        outsideOccupation (n+3) before head tail after ⊆
          (literalStateOf (n+3) (head ++ tail)).occupied := by
  rw [completion_residual (n+3) (by omega) before head tail after (by omega)]
  constructor
  · intro h p hp
    obtain ⟨hcat, hnot⟩ := Finset.mem_sdiff.mp hp
    exact h p ((ThreeLevelCoverage.mem_catalogue n p).mp hcat) hnot
  · intro h p hp hnot
    exact h (Finset.mem_sdiff.mpr
      ⟨(ThreeLevelCoverage.mem_catalogue n p).mpr hp, hnot⟩)

theorem required_write_bound (n : ℕ) (hn : 1 ≤ n) (head tail : List ℕ)
    (hh : head.length = n-1) (required : Finset (List ℕ))
    (hreq : required ⊆ (literalStateOf n (head ++ tail)).occupied) :
    required.card + (n-1) ≤ (head ++ tail).length := by
  have hz : (literalStateOf n head).occupied = ∅ := by
    change (literalPermutationWindows n head).toFinset = ∅
    rw [literalPermutationWindows_eq_nil_of_short n head (by omega)]
    rfl
  have hc : (literalStateOf n (head ++ tail)).occupied.card ≤ tail.length := by
    rw [occupation_append n hn, hz, Finset.empty_union,
      lastSymbols_of_short _ _ (by omega)]
    exact le_trans (List.toFinset_card_le _) (emitted_length_le n head tail)
  have hr := le_trans (Finset.card_le_card hreq) hc
  simp only [List.length_append]
  omega

#print axioms three_level_residual
#print axioms required_write_bound
#print axioms replace_words
#print axioms replace_valid
#print axioms replacement_saving
#print axioms replace_masked
end Coeff2.Charlieplex.ContextReplacement
