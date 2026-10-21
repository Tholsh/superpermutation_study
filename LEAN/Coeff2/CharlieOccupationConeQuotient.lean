import Coeff2.CharlieLiteralReservoir

/-! Exact restriction of an occupation cache to an observable continuation
cone. The cone hypothesis is essential. Global uncovered obligations outside
the cone are retained, rather than silently discarded. -/
namespace Coeff2.Charlieplex.OccupationConeQuotient
variable {X : Type*}

/-- Completion splits into an outside obligation and an inside obligation.
This applies to all alphabets and all literal window-footprint sets. -/
theorem coverage_restriction (target occupied cone emitted : Set X)
    (hcone : emitted ⊆ cone) :
    target ⊆ occupied ∪ emitted ↔
      target \ cone ⊆ occupied ∧
        target ∩ cone ⊆ (occupied ∩ cone) ∪ emitted := by
  constructor
  · intro h
    constructor
    · intro x hx
      rcases h hx.1 with ho | he
      · exact ho
      · exact False.elim (hx.2 (hcone he))
    · intro x hx
      rcases h hx.1 with ho | he
      · exact Or.inl ⟨ho, hx.2⟩
      · exact Or.inr he
  · rintro ⟨hout, hin⟩ x hx
    by_cases hc : x ∈ cone
    · rcases hin ⟨hx, hc⟩ with ho | he
      · exact Or.inl ho.1
      · exact Or.inr he
    · exact Or.inl (hout ⟨hx, hc⟩)

/-- Equal restricted caches give exactly the same new/repeated partition
for every continuation footprint in the cone. -/
theorem writes_restriction (occupied cone emitted : Set X)
    (hcone : emitted ⊆ cone) :
    emitted \ occupied = emitted \ (occupied ∩ cone) ∧
      emitted ∩ occupied = emitted ∩ (occupied ∩ cone) := by
  constructor <;> ext x <;> constructor
  · rintro ⟨he, ho⟩
    exact ⟨he, fun hc => ho hc.1⟩
  · rintro ⟨he, ho⟩
    exact ⟨he, fun hc => ho ⟨hc, hcone he⟩⟩
  · rintro ⟨he, ho⟩
    exact ⟨he, ho, hcone he⟩
  · rintro ⟨he, ho⟩
    exact ⟨he, ho.1⟩

/-- Restriction also commutes with every actual write update inside the
cone. It is not only a terminal-set identity. -/
theorem update_restriction (occupied cone emitted : Set X)
    (hcone : emitted ⊆ cone) :
    (occupied ∪ emitted) ∩ cone = (occupied ∩ cone) ∪ emitted := by
  ext x
  constructor
  · rintro ⟨ho | he, hc⟩
    · exact Or.inl ⟨ho, hc⟩
    · exact Or.inr he
  · rintro (⟨ho, hc⟩ | he)
    · exact ⟨Or.inl ho, hc⟩
    · exact ⟨Or.inr he, hcone he⟩

/-- Two caches with the same observable part and same outside obligation
truth value have identical completion verdicts for EVERY footprint in the
cone, not merely footprints occurring in a corpus. -/
theorem coverage_quotient (target occupied₁ occupied₂ cone : Set X)
    (hinside : occupied₁ ∩ cone = occupied₂ ∩ cone)
    (houtside : (target \ cone ⊆ occupied₁) ↔ (target \ cone ⊆ occupied₂))
    (emitted : Set X) (hcone : emitted ⊆ cone) :
    (target ⊆ occupied₁ ∪ emitted) ↔ (target ⊆ occupied₂ ∪ emitted) := by
  rw [coverage_restriction target occupied₁ cone emitted hcone,
    coverage_restriction target occupied₂ cone emitted hcone, hinside, houtside]

/-- When the remaining cone shrinks, the new outside obligation is
computable from the old outside obligation and the retained inside cache. -/
theorem shrinking_outside_obligation (target occupied parent child : Set X)
    (hsub : child ⊆ parent) :
    target \ child ⊆ occupied ↔
      target \ parent ⊆ occupied ∧
        (target ∩ parent) \ child ⊆ occupied ∩ parent := by
  constructor
  · intro h
    constructor
    · intro x hx
      exact h ⟨hx.1, fun hc => hx.2 (hsub hc)⟩
    · intro x hx
      exact ⟨h ⟨hx.1.1, hx.2⟩, hx.1.2⟩
  · rintro ⟨hout, hin⟩ x hx
    by_cases hp : x ∈ parent
    · exact (hin ⟨⟨hx.1, hp⟩, hx.2⟩).1
    · exact hout ⟨hx.1, hp⟩

open LiteralReservoir

/-- Before one full window has elapsed, the surviving old suffix fixes
the beginning of every new window. This is the literal origin of the small
short-horizon cone, not a phase-only assumption. -/
theorem surviving_suffix (n : ℕ) (seed word : List ℕ)
    (hs : seed.length = n) (hw : word.length ≤ n) :
    lastSymbols n (seed ++ word) = seed.drop word.length ++ word := by
  unfold lastSymbols
  simp only [List.length_append, hs, Nat.add_sub_cancel_left]
  rw [List.drop_append_of_le_length (by omega : word.length ≤ seed.length)]

/-- Once n symbols are appended, the old boundary disappears completely.
Consequently an unrestricted long-horizon cone cannot stay nine-dimensional. -/
theorem complete_window_forgets_seed (n : ℕ) (seed word : List ℕ)
    (hw : word.length = n) :
    lastSymbols n (seed ++ word) = word := by
  unfold lastSymbols
  simp only [List.length_append, hw, Nat.add_sub_cancel]
  simp

/-- An observable cone defined from actual emitted windows, retaining all
literal symbol continuations within the character horizon. -/
def literalCone (n horizon : ℕ) (boundary : List ℕ) : Set (List ℕ) :=
  {p | ∃ word : List ℕ, word.length ≤ horizon ∧ p ∈ emitted n boundary word}

theorem literal_emitted_subset (n horizon : ℕ) (boundary word : List ℕ)
    (h : word.length ≤ horizon) :
    {p | p ∈ emitted n boundary word} ⊆ literalCone n horizon boundary := by
  intro p hp
  exact ⟨word, h, hp⟩

/-- Literal child cones are nested in their parent cone. Together with
update_restriction and shrinking_outside_obligation, this permits an exact
moving cache restriction, not only a fixed terminal projection. -/
theorem literalCone_step_subset (n horizon : ℕ) (boundary : List ℕ) (symbol : ℕ) :
    literalCone n horizon (lastSymbols (n-1) (boundary ++ [symbol])) ⊆
      literalCone n (horizon+1) boundary := by
  rintro p ⟨word, hw, hp⟩
  refine ⟨symbol :: word, ?_, ?_⟩
  · simp only [List.length_cons]
    omega
  · simp only [emitted]
    exact List.mem_append_right _ hp

/-- This restriction concerns the original literal IsSuperperm predicate,
not a supplied abstract realization test. It includes seam windows and
permits repeats. General n and horizon; no cheap length is asserted. -/
theorem literal_completion_restriction (n horizon : ℕ) (hn : 1 ≤ n)
    (text word : List ℕ) (h : word.length ≤ horizon) :
    let occupied : Set (List ℕ) := {p | p ∈ (literalStateOf n text).occupied}
    let cone := literalCone n horizon (literalStateOf n text).boundary
    let target : Set (List ℕ) := {p | IsPermWord n p}
    IsSuperperm n (text ++ word) ↔
      target \ cone ⊆ occupied ∧
        target ∩ cone ⊆ (occupied ∩ cone) ∪
          {p | p ∈ emitted n (literalStateOf n text).boundary word} := by
  dsimp only
  have hocc := run_occupation n (literalStateOf n text) word
  rw [literalStateRun_correct n hn] at hocc
  rw [← literalOccupation_covers_iff n (text ++ word)]
  change (∀ p, IsPermWord n p →
    p ∈ (literalStateOf n (text ++ word)).occupied) ↔ _
  rw [hocc]
  simpa only [Set.subset_def, Set.mem_setOf_eq, Set.mem_union,
    Finset.mem_union, List.mem_toFinset] using
    coverage_restriction {p | IsPermWord n p}
      {p | p ∈ (literalStateOf n text).occupied}
      (literalCone n horizon (literalStateOf n text).boundary)
      {p | p ∈ emitted n (literalStateOf n text).boundary word}
      (literal_emitted_subset n horizon _ word h)

#print axioms coverage_restriction
#print axioms writes_restriction
#print axioms update_restriction
#print axioms coverage_quotient
#print axioms literal_completion_restriction
#print axioms surviving_suffix
#print axioms complete_window_forgets_seed
#print axioms shrinking_outside_obligation
#print axioms literalCone_step_subset
end Coeff2.Charlieplex.OccupationConeQuotient
