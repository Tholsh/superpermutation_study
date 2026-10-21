import Coeff2.CharlieBellmanGauge

/-! Two separated repairs share a residual occupation target. These are
exact union/coverage laws, not a global length bound or a proof that a
restricted native path dictionary contains every possible repair.
-/
namespace Coeff2.Charlieplex.BellmanJointFrontier
open LiteralReservoir
variable {X : Type*} [DecidableEq X]

/-- After choosing a first frontier mask, the second must cover exactly
the residual obligation. Extra/overlapping coverage remains permitted. -/
theorem union_residual (target A B : Finset X) :
    target ⊆ A ∪ B ↔ target \ A ⊆ B := by
  constructor
  · intro h x hx
    rcases Finset.mem_union.mp (h (Finset.mem_sdiff.mp hx).1) with ha | hb
    · exact False.elim ((Finset.mem_sdiff.mp hx).2 ha)
    · exact hb
  · intro h x hx
    by_cases ha : x ∈ A
    · exact Finset.mem_union_left B ha
    · exact Finset.mem_union_right A (h (Finset.mem_sdiff.mpr ⟨hx, ha⟩))

/-- An allocation variable need not equal either emitted mask. It specifies
what the first region is responsible for, without forbidding extra writes. -/
theorem union_allocation (target A B : Finset X) :
    target ⊆ A ∪ B ↔ ∃ M : Finset X, M ⊆ target ∧ M ⊆ A ∧ target \ M ⊆ B := by
  constructor
  · intro h
    refine ⟨target ∩ A, Finset.inter_subset_left, Finset.inter_subset_right, ?_⟩
    intro x hx
    have ht := (Finset.mem_sdiff.mp hx).1
    have hna : x ∉ A := fun ha => (Finset.mem_sdiff.mp hx).2 (Finset.mem_inter.mpr ⟨ht, ha⟩)
    exact (union_residual target A B).mp h (Finset.mem_sdiff.mpr ⟨ht, hna⟩)
  · rintro ⟨M, _, hA, hB⟩ x hx
    by_cases hm : x ∈ M
    · exact Finset.mem_union_left B (hA hm)
    · exact Finset.mem_union_right A (hB (Finset.mem_sdiff.mpr ⟨hx, hm⟩))

/-- The finite min-plus covering convolution, in exact decision form.
The native min-over-supersets transform implements the last subset test.
All boundary requirements must already be part of the options' definitions. -/
theorem joint_budget_split {I J : Type*} (target : Finset X)
    (allowedA : I → Prop) (allowedB : J → Prop)
    (footA : I → Finset X) (footB : J → Finset X)
    (costA : I → ℕ) (costB : J → ℕ) (budget : ℕ) :
    (∃ a b, allowedA a ∧ allowedB b ∧ costA a + costB b ≤ budget ∧
      target ⊆ footA a ∪ footB b) ↔
    (∃ M : Finset X, M ⊆ target ∧ ∃ a b, allowedA a ∧ allowedB b ∧
      costA a + costB b ≤ budget ∧ M ⊆ footA a ∧ target \ M ⊆ footB b) := by
  constructor
  · rintro ⟨a, b, ha, hb, hc, ht⟩
    obtain ⟨M, hm, hA, hB⟩ := (union_allocation target (footA a) (footB b)).mp ht
    exact ⟨M, hm, a, b, ha, hb, hc, hA, hB⟩
  · rintro ⟨M, hm, a, b, ha, hb, hc, hA, hB⟩
    exact ⟨a, b, ha, hb, hc, (union_allocation target (footA a) (footB b)).mpr ⟨M, hm, hA, hB⟩⟩

/-- Superset occupation at no greater cost dominates a frontier entry for
EVERY possible partner. No disjointness/no-repeat premise is smuggled in. -/
theorem frontier_dominance (target A bigger B : Finset X)
    (cA cBig cB budget : ℕ) (hsub : A ⊆ bigger) (hcost : cBig ≤ cA)
    (hcover : target ⊆ A ∪ B) (hbudget : cA + cB ≤ budget) :
    target ⊆ bigger ∪ B ∧ cBig + cB ≤ budget := by
  constructor
  · intro x hx
    rcases Finset.mem_union.mp (hcover hx) with ha | hb
    · exact Finset.mem_union_left B (hsub ha)
    · exact Finset.mem_union_right bigger hb
  · omega

/-- All windows crossing the two seams and the retained middle are literal
emissions. This is the bridge from union masks back to symbol concatenation.
The middle is NOT ignored just because it was unchanged as a text string. -/
theorem emitted_three (n : ℕ) (boundary A middle B : List ℕ) :
    emitted n boundary (A ++ middle ++ B) =
      emitted n boundary A ++ emitted n (endBoundary n boundary A) middle ++
        emitted n (endBoundary n (endBoundary n boundary A) middle) B := by
  rw [emitted_append, emitted_append, endBoundary_append]

/-- The full literal cache update for a coordinated repair, with seam
occurrences retained and repeated permutations allowed. -/
theorem occupation_three (n : ℕ) (s : LiteralSearchState) (A middle B : List ℕ) :
    (literalStateRun n s (A ++ middle ++ B)).occupied =
      s.occupied ∪ (emitted n s.boundary A).toFinset ∪
        (emitted n (endBoundary n s.boundary A) middle).toFinset ∪
        (emitted n (endBoundary n (endBoundary n s.boundary A) middle) B).toFinset := by
  rw [run_occupation, emitted_three]
  simp only [List.toFinset_append, Finset.union_assoc]

#print axioms union_residual
#print axioms union_allocation
#print axioms joint_budget_split
#print axioms frontier_dominance
#print axioms emitted_three
#print axioms occupation_three
end Coeff2.Charlieplex.BellmanJointFrontier
