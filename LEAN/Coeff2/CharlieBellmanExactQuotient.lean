import Coeff2.CharlieOccupationConeQuotient

/-! Exact bounded Bellman decisions and their literal occupation bridge.
Repeats are allowed. Horizon, alphabet validity, boundary, and outside
coverage obligations are not silently discarded. No cheap global quotient
or record-length construction is asserted. -/
namespace Coeff2.Charlieplex.BellmanExactQuotient
open LiteralReservoir OccupationConeQuotient

/-- Unit-character Bellman recursion; the horizon also makes waste runs finite. -/
def feasible {S : Type*} (accept : S → Prop) (step : S → ℕ → S)
    (allowed : ℕ → Prop) : ℕ → S → Prop
  | 0, s => accept s
  | h + 1, s => accept s ∨ ∃ a, allowed a ∧ feasible accept step allowed h (step s a)

/-- A local, action-preserving bisimulation preserves every bounded decision.
This sufficient criterion is stronger than mere equality of optimal costs. -/
theorem feasible_bisimulation {S : Type*} (accept : S → Prop)
    (step : S → ℕ → S) (allowed : ℕ → Prop) (R : S → S → Prop)
    (terminal : ∀ s t, R s t → (accept s ↔ accept t))
    (successor : ∀ s t, R s t → ∀ a, allowed a → R (step s a) (step t a))
    (h : ℕ) : ∀ s t, R s t →
      (feasible accept step allowed h s ↔ feasible accept step allowed h t) := by
  induction h with
  | zero => exact terminal
  | succ h ih =>
    intro s t hr
    simp only [feasible]
    apply or_congr (terminal s t hr)
    apply exists_congr
    intro a
    exact and_congr_right (fun ha => ih _ _ (successor s t hr a ha))

def covered (n : ℕ) (s : LiteralSearchState) : Prop :=
  s.alphabetOK = true ∧ ∀ p, IsPermWord n p → p ∈ s.occupied

def canFinish (n h : ℕ) (s : LiteralSearchState) : Prop :=
  feasible (covered n) (literalStateStep n) (fun a => 1 ≤ a ∧ a ≤ n) h s

/-- The recursion returns an actual symbol continuation, not a matrix witness. -/
theorem feasible_word (n h : ℕ) (s : LiteralSearchState) :
    canFinish n h s ↔ ∃ w : List ℕ, w.length ≤ h ∧
      literalAlphabetTest n w = true ∧ covered n (literalStateRun n s w) := by
  induction h generalizing s with
  | zero =>
    simp [canFinish, feasible, literalStateRun, literalAlphabetTest]
  | succ h ih =>
    change covered n s ∨ (∃ a, (1 ≤ a ∧ a ≤ n) ∧ canFinish n h (literalStateStep n s a)) ↔ _
    constructor
    · rintro (hs | ⟨a, ha, hw⟩)
      · exact ⟨[], by simp, by simp [literalAlphabetTest], hs⟩
      · obtain ⟨w, hl, hal, hc⟩ := (ih _).mp hw
        refine ⟨a :: w, by simpa using Nat.succ_le_succ hl, ?_, hc⟩
        simpa only [literalAlphabetTest, List.all_cons, Bool.and_eq_true,
          decide_eq_true_eq] using And.intro ha hal
    · rintro ⟨w, hl, hal, hc⟩
      cases w with
      | nil => exact Or.inl hc
      | cons a w =>
        have ha : (1 ≤ a ∧ a ≤ n) ∧ literalAlphabetTest n w = true := by
          simpa [literalAlphabetTest] using hal
        exact Or.inr ⟨a, ha.1, (ih _).mpr ⟨w, by simpa using hl, ha.2, hc⟩⟩

/-- First-principles bridge: all literal seam windows are scanned, and neither
injectivity nor a rotation-row dictionary is assumed. -/
theorem literal_bellman_bridge (n h : ℕ) (hn : 1 ≤ n) (text : List ℕ) :
    canFinish n h (literalStateOf n text) ↔
      ∃ w : List ℕ, w.length ≤ h ∧
        literalAlphabetTest n (text ++ w) = true ∧ IsSuperperm n (text ++ w) := by
  rw [feasible_word]
  apply exists_congr
  intro w
  rw [literalStateRun_correct n hn]
  simp only [covered, literalStateOf]
  change (w.length ≤ h ∧ literalAlphabetTest n w = true ∧
    literalAlphabetTest n (text ++ w) = true ∧
    ∀ p, IsPermWord n p → p ∈ literalOccupation n (text ++ w)) ↔ _
  rw [literalOccupation_covers_iff]
  by_cases ha : literalAlphabetTest n w = true
  · simp [ha]
  · have hf : literalAlphabetTest n (text ++ w) ≠ true := by
      intro hw
      apply ha
      unfold literalAlphabetTest at hw ⊢
      rw [List.all_append, Bool.and_eq_true] at hw
      exact hw.2
    simp [ha, hf]

/-- An exact moving-horizon memoization key, expressed as an equivalence.
The cone contains EVERY literal continuation of length at most h. -/
def sameSummary (n h : ℕ) (s t : LiteralSearchState) : Prop :=
  s.boundary = t.boundary ∧ s.alphabetOK = t.alphabetOK ∧
  let C := literalCone n h s.boundary
  let target : Set (List ℕ) := {p | IsPermWord n p}
  ({p | p ∈ s.occupied} ∩ C = {p | p ∈ t.occupied} ∩ C) ∧
  ((target \ C ⊆ {p | p ∈ s.occupied}) ↔
    (target \ C ⊆ {p | p ∈ t.occupied}))

theorem summary_same_word (n h : ℕ) (s t : LiteralSearchState)
    (hs : sameSummary n h s t) (w : List ℕ) (hw : w.length ≤ h) :
    covered n (literalStateRun n s w) ↔ covered n (literalStateRun n t w) := by
  obtain ⟨hb, ha, hi, ho⟩ := hs
  have hc := coverage_quotient {p | IsPermWord n p}
    {p | p ∈ s.occupied} {p | p ∈ t.occupied}
    (literalCone n h s.boundary) hi ho
    {p | p ∈ emitted n s.boundary w} (literal_emitted_subset n h _ w hw)
  simp only [covered, run_alphabet, run_occupation, ← hb, ha]
  apply and_congr_right
  intro _
  simpa only [Set.subset_def, Set.mem_setOf_eq, Set.mem_union,
    Finset.mem_union, List.mem_toFinset] using hc

/-- Exact feasible-budget preservation, including constructive witness reuse. -/
theorem summary_same_bellman (n h : ℕ) (s t : LiteralSearchState)
    (hs : sameSummary n h s t) : canFinish n h s ↔ canFinish n h t := by
  rw [feasible_word, feasible_word]
  apply exists_congr
  intro w
  apply and_congr_right
  intro hw
  exact and_congr_right (fun _ => summary_same_word n h s t hs w hw)

/-- Optimality is the first feasible horizon; impossible states have none. -/
def optimalAt (n k : ℕ) (s : LiteralSearchState) : Prop :=
  canFinish n k s ∧ ∀ j < k, ¬canFinish n j s

/-- A horizon-H quotient also preserves every smaller decision. -/
theorem summary_smaller_budget (n H k : ℕ) (s t : LiteralSearchState)
    (hs : sameSummary n H s t) (hk : k ≤ H) :
    canFinish n k s ↔ canFinish n k t := by
  rw [feasible_word, feasible_word]
  apply exists_congr
  intro w
  apply and_congr_right
  intro hw
  exact and_congr_right (fun _ => summary_same_word n H s t hs w (hw.trans hk))

theorem summary_same_optimum (n H k : ℕ) (s t : LiteralSearchState)
    (hs : sameSummary n H s t) (hk : k ≤ H) :
    optimalAt n k s ↔ optimalAt n k t := by
  unfold optimalAt
  rw [summary_smaller_budget n H k s t hs hk]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro j
  apply forall_congr'
  intro hj
  exact not_congr (summary_smaller_budget n H j s t hs (by omega))

/-- An unseen target outside the complete future cone is a certified dead
state. This is not a heuristic based on the corpus. -/
theorem outside_obstruction (n h : ℕ) (s : LiteralSearchState)
    (p : List ℕ) (hp : IsPermWord n p) (hu : p ∉ s.occupied)
    (hc : p ∉ literalCone n h s.boundary) : ¬canFinish n h s := by
  intro hf
  obtain ⟨w, hw, _, hcover⟩ := (feasible_word n h s).mp hf
  have hit := hcover.2 p hp
  rw [run_occupation] at hit
  rcases Finset.mem_union.mp hit with hold | hnew
  · exact hu hold
  · exact hc (literal_emitted_subset n h _ w hw (List.mem_toFinset.mp hnew))

/-- On potentially completable states whose caches contain only targets,
the cone restriction loses no cache information: all outside target bits
must already be set. Thus this projection alone is NOT a live-state
exponential reduction. This identifies the remaining compression obligation. -/
theorem live_cache_reconstruction {X : Type*} (target cone U V : Set X)
    (hU : U ⊆ target) (hV : V ⊆ target)
    (outU : target \ cone ⊆ U) (outV : target \ cone ⊆ V)
    (inside : U ∩ cone = V ∩ cone) : U = V := by
  ext x
  by_cases hx : x ∈ cone
  · constructor
    · intro hu
      have hv : x ∈ V ∩ cone := inside ▸ (show x ∈ U ∩ cone from ⟨hu, hx⟩)
      exact hv.1
    · intro hv
      have hu : x ∈ U ∩ cone := inside.symm ▸ (show x ∈ V ∩ cone from ⟨hv, hx⟩)
      exact hu.1
  · constructor
    · intro hu
      exact outV ⟨hU hu, hx⟩
    · intro hv
      exact outU ⟨hV hv, hx⟩

/-- More coverage at the same literal boundary can only help when repeats
are allowed. This is not valid for a mandatory no-repeat completion rule. -/
theorem cache_dominance (n h : ℕ) (s t : LiteralSearchState)
    (hb : s.boundary = t.boundary) (ha : s.alphabetOK = t.alphabetOK)
    (hu : s.occupied ⊆ t.occupied) : canFinish n h s → canFinish n h t := by
  rw [feasible_word, feasible_word]
  rintro ⟨w, hw, hal, hc⟩
  refine ⟨w, hw, hal, ?_, ?_⟩
  · simpa only [run_alphabet, ← ha] using hc.1
  · intro p hp
    have hit := hc.2 p hp
    rw [run_occupation] at hit ⊢
    rcases Finset.mem_union.mp hit with hold | hnew
    · exact Finset.mem_union_left _ (hu hold)
    · exact Finset.mem_union_right _ (by simpa only [← hb] using hnew)

/-- Literal constructive dominance: reuse the SAME continuation from a
shorter prefix with at least as much coverage. No abstract realization
assumption, row restriction, or greedy attachment hypothesis is involved. -/
theorem prefix_dominance (n : ℕ) (hn : 1 ≤ n) (left right w : List ℕ)
    (hb : (literalStateOf n left).boundary = (literalStateOf n right).boundary)
    (ha : literalAlphabetTest n right = true)
    (hu : (literalStateOf n left).occupied ⊆ (literalStateOf n right).occupied)
    (hl : right.length ≤ left.length)
    (hvalid : literalAlphabetTest n (left ++ w) = true)
    (hcover : IsSuperperm n (left ++ w)) :
    literalAlphabetTest n (right ++ w) = true ∧ IsSuperperm n (right ++ w) ∧
      (right ++ w).length ≤ (left ++ w).length := by
  have hleft : literalAlphabetTest n left = true := by
    unfold literalAlphabetTest at hvalid ⊢
    rw [List.all_append, Bool.and_eq_true] at hvalid
    exact hvalid.1
  -- Use word-level coverage directly so the witness is preserved, not replaced.
  have hc : covered n (literalStateRun n (literalStateOf n left) w) := by
    rw [literalStateRun_correct n hn]
    refine ⟨hvalid, ?_⟩
    exact (literalOccupation_covers_iff n (left ++ w)).mpr hcover
  have hright : covered n (literalStateRun n (literalStateOf n right) w) := by
    constructor
    · rw [run_alphabet]
      have hw := hc.1
      rw [run_alphabet] at hw
      simpa only [literalStateOf, hleft, ha] using hw
    · intro p hp
      have hit := hc.2 p hp
      rw [run_occupation] at hit ⊢
      rcases Finset.mem_union.mp hit with hold | hnew
      · exact Finset.mem_union_left _ (hu hold)
      · exact Finset.mem_union_right _ (by simpa only [← hb] using hnew)
  rw [literalStateRun_correct n hn] at hright
  refine ⟨hright.1, (literalOccupation_covers_iff n (right ++ w)).mp hright.2, ?_⟩
  simp only [List.length_append]
  omega

#print axioms feasible_bisimulation
#print axioms feasible_word
#print axioms literal_bellman_bridge
#print axioms summary_same_word
#print axioms summary_same_bellman
#print axioms summary_smaller_budget
#print axioms summary_same_optimum
#print axioms outside_obstruction
#print axioms live_cache_reconstruction
#print axioms cache_dominance
#print axioms prefix_dominance
end Coeff2.Charlieplex.BellmanExactQuotient
