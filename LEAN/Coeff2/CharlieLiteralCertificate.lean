import Coeff2.CharlieLiteralBridge

/-!
# Executable literal certificates and occurrence-by-occurrence cache replay

Inputs are actual finite symbol lists, not abstract cells or supplied
realization predicates.  All tests below use finite enumeration.  Acceptance
is equivalent to the project's original `IsSuperperm` definition and the
actual list length.  No-repeat is a separate optional test.

The cache adapter here handles occupation only: its phase deltas are zero.
It does not identify crown gauges with permutation parity or physical moves.
Each occurrence produces its own singleton write, so an internal duplicate
cannot be hidden by first replacing a fragment with its underlying set.
-/

namespace Coeff2
namespace Charlieplex

/-- Inspect every strict interior offset of the actual overlap string. -/
def literalProperEdgeTest (n : ℕ) (source target : List ℕ) : Bool :=
  let gap := literalOverlapCost n source target
  let text := source ++ target.drop (n - gap)
  (List.range gap).all fun offset =>
    decide (offset = 0) || !(literalPermTest n ((text.drop offset).take n))

/-- The finite edge checker is exactly the original proper-edge predicate. -/
theorem literalProperEdgeTest_eq_true (n : ℕ) (hn : 1 ≤ n)
    (source target : List ℕ) (hsource : source.length ≤ n) :
    literalProperEdgeTest n source target = true ↔ ProperStep n source target := by
  rw [literalProperEdgeTest, literalOverlapCost_eq_wt n hn source target hsource]
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq,
    Bool.not_eq_true', Bool.eq_false_iff, ne_eq, literalPermTest_eq_true]
  change (∀ offset < wt n source target,
    offset = 0 ∨ ¬ IsPermWord n (((overlapWord n source target).drop offset).take n)) ↔ _
  constructor
  · intro hall ⟨offset, hpos, hlt, hperm⟩
    rcases hall offset hlt with hzero | hnot
    · omega
    · exact hnot hperm
  · intro hproper offset hlt
    by_cases hzero : offset = 0
    · exact Or.inl hzero
    · exact Or.inr (fun hperm => hproper ⟨offset, by omega, hlt, hperm⟩)

/-- Check the actual directed overlap edges of a finite vertex ledger. -/
def literalProperChainTest (n : ℕ) : List (List ℕ) → Bool
  | [] => true
  | [_] => true
  | source :: target :: rest =>
      literalProperEdgeTest n source target &&
        literalProperChainTest n (target :: rest)

theorem literalProperChainTest_eq_true (n : ℕ) (hn : 1 ≤ n)
    (vertices : List (List ℕ))
    (hperms : ∀ vertex ∈ vertices, IsPermWord n vertex) :
    literalProperChainTest n vertices = true ↔ vertices.IsChain (ProperStep n) := by
  induction vertices with
  | nil => simp [literalProperChainTest]
  | cons source rest ih =>
      cases rest with
      | nil => simp [literalProperChainTest]
      | cons target rest =>
          rw [literalProperChainTest, Bool.and_eq_true,
            literalProperEdgeTest_eq_true n hn source target
              (le_of_eq (hperms source List.mem_cons_self).length),
            ih (fun vertex hvertex => hperms vertex
              (List.mem_cons_of_mem source hvertex))]
          exact List.isChain_cons_cons.symm

/-- Full finite path validation: nonempty ledger, genuine permutation words,
and no unrecorded intermediate permutation windows on any edge. -/
def literalWalkTest (n : ℕ) (vertices : List (List ℕ)) : Bool :=
  decide (vertices ≠ []) && vertices.all (literalPermTest n) &&
    literalProperChainTest n vertices

theorem literalWalkTest_eq_true (n : ℕ) (hn : 1 ≤ n)
    (vertices : List (List ℕ)) :
    literalWalkTest n vertices = true ↔
      vertices ≠ [] ∧ (∀ vertex ∈ vertices, IsPermWord n vertex) ∧
        vertices.IsChain (ProperStep n) := by
  simp only [literalWalkTest, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, literalPermTest_eq_true]
  constructor
  · rintro ⟨⟨hne, hperms⟩, hchecked⟩
    exact ⟨hne, hperms, (literalProperChainTest_eq_true n hn vertices hperms).mp hchecked⟩
  · rintro ⟨hne, hperms, hchain⟩
    exact ⟨⟨hne, hperms⟩, (literalProperChainTest_eq_true n hn vertices hperms).mpr hchain⟩

/-- Every condition needed by the spelling theorem is discharged by one
computable test of the literal ledger. -/
theorem checkedLiteralSpelling_correct {n : ℕ} (hn : 1 ≤ n)
    (vertices : List (List ℕ)) (hchecked : literalWalkTest n vertices = true) :
    let text := literalSpelling n vertices
    text.length = n + (vertices.zipWith (wt n) vertices.tail).sum ∧
    literalPermutationWindows n text = vertices ∧
    (IsSuperperm n text ↔ ∀ vertex, IsPermWord n vertex → vertex ∈ vertices) := by
  obtain ⟨hne, hperms, hproper⟩ := (literalWalkTest_eq_true n hn vertices).mp hchecked
  let walk : Walk n := ⟨vertices, hne, hperms, hproper⟩
  have hcontract := literalSpelling_correct hn walk
  exact ⟨hcontract.1, hcontract.2.1, hcontract.2.2.1⟩

/-- Finite literal permutation catalogue.  Both alphabet construction and
permutation generation use structural recursion and reduce in the kernel. -/
def literalPermutationCatalogue (n : ℕ) : List (List ℕ) :=
  (List.range' 1 n).permutations'

@[simp] theorem mem_literalPermutationCatalogue (n : ℕ) (word : List ℕ) :
    word ∈ literalPermutationCatalogue n ↔ IsPermWord n word := by
  have hbase : IsPermWord n (List.range' 1 n) := by
    constructor
    · exact List.nodup_range'
    · ext symbol
      simp only [List.mem_toFinset, List.mem_range'_1, Finset.mem_Icc]
      omega
  have hbasePerm := isPermWord_iff_perm_refList.mp hbase
  rw [literalPermutationCatalogue, List.mem_permutations', isPermWord_iff_perm_refList]
  exact ⟨fun hperm => hperm.trans hbasePerm,
    fun hperm => hperm.trans hbasePerm.symm⟩

/-- Accept precisely the actual words with the requested length and coverage.
Repeated permutation windows are allowed, as in `IsSuperperm`. -/
def literalCompletionTest (n budget : ℕ) (text : List ℕ) : Bool :=
  let windows := literalPermutationWindows n text
  decide (text.length = budget) &&
    (literalPermutationCatalogue n).all fun permutation =>
      windows.contains permutation

/-- Both soundness and completeness, for every order (including zero). -/
theorem literalCompletionTest_eq_true (n budget : ℕ) (text : List ℕ) :
    literalCompletionTest n budget text = true ↔
      text.length = budget ∧ IsSuperperm n text := by
  simp only [literalCompletionTest, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, mem_literalPermutationCatalogue, List.contains_iff_mem]
  have hcover := literalOccupation_covers_iff n text
  simp only [literalOccupation, List.mem_toFinset] at hcover
  rw [hcover]

/-- The original `IsSuperperm` predicate is a coverage predicate and does not
forbid extra symbols elsewhere in the text.  Check the alphabet separately
when certifying a word over exactly `[n]`. -/
def literalAlphabetTest (n : ℕ) (text : List ℕ) : Bool :=
  text.all fun symbol => decide (1 ≤ symbol ∧ symbol ≤ n)

@[simp] theorem literalAlphabetTest_eq_true (n : ℕ) (text : List ℕ) :
    literalAlphabetTest n text = true ↔
      ∀ symbol ∈ text, 1 ≤ symbol ∧ symbol ≤ n := by
  simp [literalAlphabetTest]

/-- Strict output gate: legal alphabet, exact length, and literal coverage. -/
def literalWordCompletionTest (n budget : ℕ) (text : List ℕ) : Bool :=
  literalAlphabetTest n text && literalCompletionTest n budget text

theorem literalWordCompletionTest_eq_true (n budget : ℕ) (text : List ℕ) :
    literalWordCompletionTest n budget text = true ↔
      (∀ symbol ∈ text, 1 ≤ symbol ∧ symbol ≤ n) ∧
        text.length = budget ∧ IsSuperperm n text := by
  rw [literalWordCompletionTest, Bool.and_eq_true, literalAlphabetTest_eq_true,
    literalCompletionTest_eq_true]

/-- Optional single-use restriction, distinct from superpermutation coverage. -/
def literalNoRepeatTest (n : ℕ) (text : List ℕ) : Bool :=
  decide (literalPermutationWindows n text).Nodup

@[simp] theorem literalNoRepeatTest_eq_true (n : ℕ) (text : List ℕ) :
    literalNoRepeatTest n text = true ↔ (literalPermutationWindows n text).Nodup := by
  simp [literalNoRepeatTest]

/-! ## Literal occurrence cache (occupation coordinate only) -/

/-- One actual occurrence is one write, never a pre-collapsed fragment mask. -/
def literalVisitInput (permutation : List ℕ) : CacheInput (List ℕ) where
  phaseDelta := 0
  writes := {permutation}

def literalEmptyCache : CacheState (List ℕ) where
  phase := 0
  occupied := ∅

def literalVisitInputs (n : ℕ) (text : List ℕ) : List (CacheInput (List ℕ)) :=
  (literalPermutationWindows n text).map literalVisitInput

theorem literalVisitWriteUnion (vertices : List (List ℕ)) :
    cacheWriteUnion (vertices.map literalVisitInput) = vertices.toFinset := by
  induction vertices with
  | nil => rfl
  | cons vertex vertices ih => simp [literalVisitInput, ih]

/-- The final cache is exactly the set of literal windows, even in a run
with collisions.  Coverage and legality must not be conflated. -/
theorem literalCache_occupation (n : ℕ) (text : List ℕ) :
    (cacheRun literalEmptyCache (literalVisitInputs n text)).occupied =
      literalOccupation n text := by
  rw [cacheRun_occupied, literalVisitInputs, literalVisitWriteUnion]
  simp [literalEmptyCache, literalOccupation]

theorem literalVisitLegal_iff (state : CacheState (List ℕ)) (vertex : List ℕ) :
    CacheLegal state (literalVisitInput vertex) ↔ vertex ∉ state.occupied := by
  rw [cacheLegal_iff_disjoint]
  simp [literalVisitInput]

/-- Exact prefix-sensitive legality; the evolving occupied set is not
replaced by a static degree or a parity-only condition. -/
theorem literalVisitRun_legal_iff (vertices : List (List ℕ))
    (state : CacheState (List ℕ)) :
    CacheLegalRun state (vertices.map literalVisitInput) ↔
      vertices.Nodup ∧ ∀ vertex ∈ vertices, vertex ∉ state.occupied := by
  induction vertices generalizing state with
  | nil => simp
  | cons vertex vertices ih =>
      rw [List.map_cons, cacheLegalRun_cons, literalVisitLegal_iff, ih]
      simp only [
        List.nodup_cons, List.mem_cons, forall_eq_or_imp, cacheStep_occupied,
        literalVisitInput, Finset.mem_union, Finset.mem_singleton, not_or]
      constructor
      · rintro ⟨hhead, hnodup, htail⟩
        refine ⟨⟨?_, hnodup⟩, hhead, fun other hother => (htail other hother).1⟩
        intro hmem
        exact (htail vertex hmem).2 rfl
      · rintro ⟨⟨hnot, hnodup⟩, hhead, htail⟩
        refine ⟨hhead, hnodup, fun other hother => ⟨htail other hother, ?_⟩⟩
        intro heq
        exact hnot (heq ▸ hother)

/-- Cache legality is equivalent to no repeated actual permutation window. -/
theorem literalCache_legal_iff (n : ℕ) (text : List ℕ) :
    CacheLegalRun literalEmptyCache (literalVisitInputs n text) ↔
      (literalPermutationWindows n text).Nodup := by
  rw [literalVisitInputs, literalVisitRun_legal_iff]
  simp [literalEmptyCache]

/-- Cache coverage is equivalent to literal superpermutation coverage,
without assuming collision freedom. -/
theorem literalCache_covers_iff (n : ℕ) (text : List ℕ) :
    (∀ permutation, IsPermWord n permutation →
      permutation ∈ (cacheRun literalEmptyCache (literalVisitInputs n text)).occupied) ↔
      IsSuperperm n text := by
  rw [literalCache_occupation, literalOccupation_covers_iff]

/-- Literal gluing law.  The *concatenated vertex ledger* is checked,
including its seam.  The theorem spells that ledger; it does not concatenate
two already-spelled strings and silently ignore their boundary windows.
Repeated terminal occurrences remain repetitions unless the caller removes
the shared terminal from one side before supplying the ledgers. -/
theorem checkedLiteralGlue_occupation {n : ℕ} (hn : 1 ≤ n)
    (left right : List (List ℕ))
    (hchecked : literalWalkTest n (left ++ right) = true) :
    let text := literalSpelling n (left ++ right)
    literalPermutationWindows n text = left ++ right ∧
    (cacheRun literalEmptyCache (literalVisitInputs n text)).occupied =
      left.toFinset ∪ right.toFinset ∧
    (CacheLegalRun literalEmptyCache (literalVisitInputs n text) ↔
      left.Nodup ∧ right.Nodup ∧ Disjoint left.toFinset right.toFinset) := by
  dsimp only
  have hledger := (checkedLiteralSpelling_correct hn (left ++ right) hchecked).2.1
  refine ⟨hledger, ?_, ?_⟩
  · rw [literalCache_occupation, literalOccupation, hledger, List.toFinset_append]
  · rw [literalCache_legal_iff, hledger, List.nodup_append']
    simp only [Finset.disjoint_left, List.mem_toFinset, List.disjoint_left]

/-- Use the bridge as a module: one finite edge test connects the concrete
Cayley trace, its spelled string, and the actual singleton-write cache. -/
theorem checkedCayley_literalCache_correct {n : ℕ} (hn : 1 ≤ n)
    (start : Equiv.Perm (Fin n)) (actions : List (Equiv.Perm (Fin n)))
    (hchecked : literalProperChainTest n (cayleyLiteralVertices start actions) = true) :
    let vertices := cayleyLiteralVertices start actions
    let text := literalSpelling n vertices
    text.length = n + (vertices.zipWith (wt n) vertices.tail).sum ∧
    literalPermutationWindows n text = vertices ∧
    (IsSuperperm n text ↔ ∀ state, state ∈ cayleyOccupationStates start actions) ∧
    (CacheLegalRun literalEmptyCache (literalVisitInputs n text) ↔
      CayleyOccupationLegal start actions) := by
  have hproper := (literalProperChainTest_eq_true n hn _
    (cayleyLiteralVertices_isPerm start actions)).mp hchecked
  have hcontract := cayleyLiteralSpelling_correct hn start actions hproper
  refine ⟨hcontract.1, hcontract.2.1, hcontract.2.2.1, ?_⟩
  exact (literalCache_legal_iff _ _).trans hcontract.2.2.2

end Charlieplex
end Coeff2
