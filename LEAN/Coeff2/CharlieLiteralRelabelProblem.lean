import Mathlib.Tactic

/-! Lossless relabeling of literal substring obligations and overlap seams.
These identities justify quotienting equivalent local problems, not their
solvability or a global superpermutation length formula. -/
namespace Coeff2.Charlieplex.LiteralRelabelProblem
variable {A B : Type*}

def contains (needle word : List A) : Prop :=
  ∃ pre suffix, word=pre++needle++suffix

theorem contains_relabel (e : A ≃ B) (needle word : List A) :
    contains (needle.map e) (word.map e) ↔ contains needle word := by
  constructor
  · rintro ⟨pre, suffix, he⟩
    refine ⟨pre.map e.symm, suffix.map e.symm, ?_⟩
    have h := congrArg (List.map e.symm) he
    simpa [List.map_append, List.map_map] using h
  · rintro ⟨pre, suffix, he⟩
    refine ⟨pre.map e, suffix.map e, ?_⟩
    simp [he, List.map_append]

theorem prefix_relabel (e : A ≃ B) (head word : List A) :
    (∃ suffix, word.map e=head.map e++suffix) ↔
      ∃ suffix, word=head++suffix := by
  constructor
  · rintro ⟨suffix, he⟩
    refine ⟨suffix.map e.symm, ?_⟩
    simpa [List.map_append, List.map_map] using congrArg (List.map e.symm) he
  · rintro ⟨suffix, he⟩
    exact ⟨suffix.map e, by simp [he, List.map_append]⟩

theorem suffix_relabel (e : A ≃ B) (tail word : List A) :
    (∃ pre, word.map e=pre++tail.map e) ↔
      ∃ pre, word=pre++tail := by
  constructor
  · rintro ⟨pre, he⟩
    refine ⟨pre.map e.symm, ?_⟩
    simpa [List.map_append, List.map_map] using congrArg (List.map e.symm) he
  · rintro ⟨pre, he⟩
    exact ⟨pre.map e, by simp [he, List.map_append]⟩

def feasible (head tail : List A) (required : List (List A)) (word : List A) : Prop :=
  (∃ suffix, word=head++suffix) ∧ (∃ pre, word=pre++tail) ∧
    ∀ needle ∈ required, contains needle word

/-- Fixed literal interfaces and the entire residual set are all retained.
The same relabeling preserves word length, so every length decision agrees. -/
theorem feasible_relabel (e : A ≃ B) (head tail word : List A)
    (required : List (List A)) :
    feasible (head.map e) (tail.map e) (required.map (List.map e)) (word.map e) ↔
      feasible head tail required word := by
  simp only [feasible, prefix_relabel, suffix_relabel, List.mem_map,
    forall_exists_index, and_imp]
  constructor
  · rintro ⟨hh, ht, hr⟩
    refine ⟨hh, ht, ?_⟩
    intro needle hn
    exact (contains_relabel e needle word).mp (hr _ needle hn rfl)
  · rintro ⟨hh, ht, hr⟩
    refine ⟨hh, ht, ?_⟩
    intro mapped needle hn he
    subst mapped
    exact (contains_relabel e needle word).mpr (hr needle hn)

#print axioms feasible_relabel
end Coeff2.Charlieplex.LiteralRelabelProblem
