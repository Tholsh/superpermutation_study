import Coeff2.CharlieCycleCompression

/-!
# One literal occupation write changes one fragment/bend gate

The gate asks whether an immediate fresh permutation is available at a literal
boundary. It is not inferred from dirty-run length or the reduced codec's depth.
The operator update is an outer product at exactly one boundary address. This
does not assert that future completion costs depend on only that address.
-/
namespace Coeff2.Charlieplex.FragmentBendGate

def FreshAvailable (n : ℕ) (occupied : Finset (List ℕ)) (boundary : List ℕ) : Prop :=
  ∃ symbol, IsPermWord n (boundary ++ [symbol]) ∧ boundary ++ [symbol] ∉ occupied

noncomputable def availability (n : ℕ) (occupied : Finset (List ℕ))
    (boundary : List ℕ) : ℤ := by
  classical
  exact if FreshAvailable n occupied boundary then 1 else 0

theorem fresh_at_write {n symbol : ℕ} {occupied : Finset (List ℕ)}
    {boundary : List ℕ} (valid : IsPermWord n (boundary ++ [symbol]))
    (fresh : boundary ++ [symbol] ∉ occupied) :
    FreshAvailable n occupied boundary := ⟨symbol, valid, fresh⟩

/-- A new occupied permutation removes exactly its own prefix from the fresh
gate. The uniqueness premise comes from literal permutation validity itself. -/
theorem freshAvailable_insert_iff {n symbol : ℕ} {occupied : Finset (List ℕ)}
    {boundary query : List ℕ} (valid : IsPermWord n (boundary ++ [symbol])) :
    FreshAvailable n (insert (boundary ++ [symbol]) occupied) query ↔
      FreshAvailable n occupied query ∧ query ≠ boundary := by
  classical
  constructor
  · rintro ⟨other, hvalid, hnew⟩
    have old : query ++ [other] ∉ occupied := by
      intro hmem
      exact hnew (Finset.mem_insert_of_mem hmem)
    refine ⟨⟨other, hvalid, old⟩, ?_⟩
    intro same
    subst query
    have eq := clean_append_unique hvalid valid
    subst other
    exact hnew (Finset.mem_insert_self _ _)
  · rintro ⟨⟨other, hvalid, hold⟩, different⟩
    refine ⟨other, hvalid, ?_⟩
    intro hmem
    rcases Finset.mem_insert.mp hmem with same | old
    · have sameBoundary : query = boundary := by
        simpa using congrArg List.dropLast same
      exact different sameBoundary
    · exact hold old

theorem availability_insert {n symbol : ℕ} {occupied : Finset (List ℕ)}
    {boundary : List ℕ} (valid : IsPermWord n (boundary ++ [symbol]))
    (fresh : boundary ++ [symbol] ∉ occupied) (query : List ℕ) :
    availability n (insert (boundary ++ [symbol]) occupied) query =
      availability n occupied query - if query = boundary then 1 else 0 := by
  classical
  have hw := fresh_at_write valid fresh
  by_cases same : query = boundary
  · subst query
    simp [availability, freshAvailable_insert_iff valid, hw]
  · simp [availability, freshAvailable_insert_iff valid, same]

/-- Pointwise diagonal gate on integer-valued boundary vectors. -/
noncomputable def gate (n : ℕ) (occupied : Finset (List ℕ))
    (v : List ℕ → ℤ) (query : List ℕ) : ℤ :=
  availability n occupied query * v query

/-- The outer product |boundary><boundary|, without a dense matrix. -/
def writeResponse (boundary : List ℕ) (v : List ℕ → ℤ) (query : List ℕ) : ℤ :=
  if query = boundary then v boundary else 0

theorem writeResponse_idempotent (boundary : List ℕ) (v : List ℕ → ℤ) :
    writeResponse boundary (writeResponse boundary v) = writeResponse boundary v := by
  funext query
  by_cases same : query = boundary <;> simp [writeResponse, same]

/-- Exact rank-one-form operator downdate. No claim of a global occupation
quotient, simultaneous diagonalization, or a completed superpermutation. -/
theorem gate_insert {n symbol : ℕ} {occupied : Finset (List ℕ)}
    {boundary : List ℕ} (valid : IsPermWord n (boundary ++ [symbol]))
    (fresh : boundary ++ [symbol] ∉ occupied) (v : List ℕ → ℤ) :
    gate n (insert (boundary ++ [symbol]) occupied) v =
      gate n occupied v - writeResponse boundary v := by
  classical
  funext query
  unfold gate
  rw [availability_insert valid fresh query]
  by_cases same : query = boundary
  · subst query
    simp [writeResponse, sub_mul]
  · simp [writeResponse, same]

noncomputable def dirtyIndicator (n : ℕ) (boundary : List ℕ) (symbol : ℕ) : ℤ := by
  classical
  exact if IsPermWord n (boundary ++ [symbol]) then 0 else 1

noncomputable def fragmentWeight (n : ℕ) (occupied : Finset (List ℕ))
    (boundary : List ℕ) (symbol : ℕ) : ℤ :=
  dirtyIndicator n boundary symbol * availability n occupied boundary

noncomputable def forcedBendWeight (n : ℕ) (occupied : Finset (List ℕ))
    (boundary : List ℕ) (symbol : ℕ) : ℤ :=
  dirtyIndicator n boundary symbol * (1 - availability n occupied boundary)

theorem fragment_plus_forced (n : ℕ) (occupied : Finset (List ℕ))
    (boundary : List ℕ) (symbol : ℕ) :
    fragmentWeight n occupied boundary symbol + forcedBendWeight n occupied boundary symbol =
      dirtyIndicator n boundary symbol := by
  unfold fragmentWeight forcedBendWeight
  ring

/-- At the newly occupied prefix, each dirty alternative is reclassified
from voluntary fragmentation to forced waste. All other prefixes are unchanged. -/
theorem fragmentWeight_insert {n symbol : ℕ} {occupied : Finset (List ℕ)}
    {boundary : List ℕ} (valid : IsPermWord n (boundary ++ [symbol]))
    (fresh : boundary ++ [symbol] ∉ occupied) (query : List ℕ) (other : ℕ) :
    fragmentWeight n (insert (boundary ++ [symbol]) occupied) query other =
      fragmentWeight n occupied query other -
        dirtyIndicator n query other * (if query = boundary then 1 else 0) := by
  unfold fragmentWeight
  rw [availability_insert valid fresh query]
  ring

theorem forcedBendWeight_insert {n symbol : ℕ} {occupied : Finset (List ℕ)}
    {boundary : List ℕ} (valid : IsPermWord n (boundary ++ [symbol]))
    (fresh : boundary ++ [symbol] ∉ occupied) (query : List ℕ) (other : ℕ) :
    forcedBendWeight n (insert (boundary ++ [symbol]) occupied) query other =
      forcedBendWeight n occupied query other +
        dirtyIndicator n query other * (if query = boundary then 1 else 0) := by
  unfold forcedBendWeight
  rw [availability_insert valid fresh query]
  ring

end Coeff2.Charlieplex.FragmentBendGate
