import Coeff2.CharlieOccupationSuperoperator

/-! Exact, literal-character context quotient and deterministic next-symbol
transport. This is not a learned transformer or an efficient global solver.
Prefix closure supplies a proved all-alphabet continuation congruence.
The C++ trie compiler and region extractor remain native implementations. -/
namespace Coeff2.Charlieplex.ExactSymbolTransformer

variable {α : Type*} [DecidableEq α]

def PrefixClosed (D : Finset (List α)) : Prop :=
  ∀ p ∈ D, ∀ t, t.IsPrefix p → t ∈ D

def SameContext (D : Finset (List α)) (u v : List α) : Prop :=
  ∀ p ∈ D, p.IsSuffix u ↔ p.IsSuffix v

/-- No literal history outside the pattern-prefix context can change the
next pattern match. Unlike rank histograms, this is a continuation congruence. -/
theorem context_step (D : Finset (List α)) (closed : PrefixClosed D)
    (u v : List α) (same : SameContext D u v) (a : α) :
    SameContext D (u ++ [a]) (v ++ [a]) := by
  intro p hp
  simp only [List.suffix_concat_iff]
  apply or_congr_right
  constructor
  · rintro ⟨t, ht, hs⟩
    have hm : t ∈ D := closed p hp t (ht ▸ List.prefix_append t [a])
    exact ⟨t, ht, (same t hm).mp hs⟩
  · rintro ⟨t, ht, hs⟩
    have hm : t ∈ D := closed p hp t (ht ▸ List.prefix_append t [a])
    exact ⟨t, ht, (same t hm).mpr hs⟩

theorem context_continuation (D : Finset (List α)) (closed : PrefixClosed D)
    (u v w : List α) (same : SameContext D u v) :
    SameContext D (u ++ w) (v ++ w) := by
  induction w using List.reverseRecOn with
  | nil => simpa using same
  | append_singleton w a ih =>
      simpa [List.append_assoc] using context_step D closed (u ++ w) (v ++ w) ih a

/-- Alphabet gauge acts on the literal patterns and histories TOGETHER.
It cannot identify two different occupation masks by their cardinality. -/
theorem suffix_relabel {β : Type*} (e : α ≃ β) (p u : List α) :
    (p.map e).IsSuffix (u.map e) ↔ p.IsSuffix u := by
  constructor
  · intro h
    have hi := h.map e.symm
    simpa [List.map_map, Function.comp_def] using hi
  · intro h
    exact h.map e

theorem context_relabel {β : Type*} [DecidableEq β] (e : α ≃ β)
    (D : Finset (List α)) (u v : List α) (same : SameContext D u v) :
    SameContext (D.image (List.map e)) (u.map e) (v.map e) := by
  intro p hp
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hp
  simpa only [suffix_relabel] using same t ht

def writeMissing (M : Finset (List α)) (history : List α) : Finset (List α) :=
  M.filter (fun p => ¬ p.IsSuffix history)

theorem occupation_write_same (D M : Finset (List α)) (inside : M ⊆ D)
    (u v : List α) (same : SameContext D u v) :
    writeMissing M u = writeMissing M v := by
  ext p
  by_cases hp : p ∈ M
  · simp only [writeMissing, Finset.mem_filter, hp, true_and]
    exact not_congr (same p (inside hp))
  · simp [writeMissing, hp]

/-- Match outputs can repeat; the missing-set write is idempotent.
Dirty frames are simply frames matching no required pattern. -/
theorem occupation_write_idempotent (M : Finset (List α)) (u : List α) :
    writeMissing (writeMissing M u) u = writeMissing M u := by
  ext p
  simp [writeMissing]

def finishMissing (M : Finset (List α)) (u : List α) : List α → Finset (List α)
  | [] => M
  | a :: w => finishMissing (writeMissing M (u ++ [a])) (u ++ [a]) w

/-- This preserves every future literal occupation write, not just the
next clean/dirty bit. Include all target and terminal-pattern prefixes in D. -/
theorem continuation_occupation_same (D M : Finset (List α))
    (closed : PrefixClosed D) (inside : M ⊆ D) (u v w : List α)
    (same : SameContext D u v) : finishMissing M u w = finishMissing M v w := by
  induction w generalizing M u v with
  | nil => rfl
  | cons a w ih =>
      have hs := context_step D closed u v same a
      have hw := occupation_write_same D M inside (u ++ [a]) (v ++ [a]) hs
      simp only [finishMissing]
      rw [← hw]
      apply ih
      · intro p hp
        exact inside (Finset.mem_filter.mp hp).1
      · exact hs

section Generator
variable {S A : Type*}

def run (step : A → S → S) (s : S) : List A → S
  | [] => s
  | a :: w => run step (step a s) w

def reachable (step : A → S → S) (accept : S → Prop) : ℕ → S → Prop
  | 0, s => accept s
  | h + 1, s => accept s ∨ ∃ a, reachable step accept h (step a s)

/-- The exact generator has explicit literal-word witnesses. Computing the
predicate efficiently is a separate issue; no oracle is disguised as a gain. -/
theorem reachable_iff_word (step : A → S → S) (accept : S → Prop) (h : ℕ) (s : S) :
    reachable step accept h s ↔ ∃ w, w.length ≤ h ∧ accept (run step s w) := by
  induction h generalizing s with
  | zero =>
      simp [reachable, run]
  | succ h ih =>
      constructor
      · rintro (ha | ⟨a, hr⟩)
        · exact ⟨[], by simp, ha⟩
        · obtain ⟨w, hl, hw⟩ := (ih (step a s)).mp hr
          exact ⟨a :: w, by simpa using Nat.succ_le_succ hl, hw⟩
      · rintro ⟨w, hl, hw⟩
        cases w with
        | nil => exact Or.inl hw
        | cons a w =>
            exact Or.inr ⟨a, (ih (step a s)).mpr
              ⟨w, by simpa using hl, hw⟩⟩

/-- Exhaustion can prove a local minimum only when ALL shorter literal
continuations have actually been ruled out, not when a bounded run times out. -/
theorem scoped_minimum (step : A → S → S) (accept : S → Prop) (s : S)
    (w : List A) (positive : 0 < w.length)
    (noShorter : ¬ reachable step accept (w.length - 1) s)
    (v : List A) (hv : accept (run step s v)) : w.length ≤ v.length := by
  by_contra hn
  have hl : v.length ≤ w.length - 1 := by omega
  exact noShorter ((reachable_iff_word step accept _ s).mpr ⟨v, hl, hv⟩)

end Generator

/-- A capacity bound for theoretical attention weights: distinct obligations
need distinct emission times. If r of them cannot arrive before d, the last
must arrive at least at d+r-1. Application must prove its release distances. -/
theorem release_capacity {O : Type*} [DecidableEq O] (targets : Finset O)
    (times : O → ℕ) (distinct : Set.InjOn times targets) (d B : ℕ)
    (nonempty : targets.Nonempty)
    (early : ∀ p ∈ targets, d ≤ times p) (late : ∀ p ∈ targets, times p ≤ B) :
    d + targets.card ≤ B + 1 := by
  obtain ⟨p, hp⟩ := nonempty
  have hd : d ≤ B := (early p hp).trans (late p hp)
  have hsub : targets.image times ⊆ Finset.Icc d B := by
    intro t ht
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp ht
    exact Finset.mem_Icc.mpr ⟨early q hq, late q hq⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn distinct, Nat.card_Icc] at hc
  omega

section Superoperator
variable {S R : Type*} [Fintype S] [DecidableEq S] [CommSemiring R]

def symbolMatrix (step : S → S) : Matrix S S R :=
  fun i j => if i = step j then 1 else 0

theorem symbol_column (step : S → S) (s i j : S) (hne : i ≠ j) :
    symbolMatrix (R := R) step i s * symbolMatrix step j s = 0 := by
  simp only [symbolMatrix]
  split_ifs <;> simp_all

theorem symbol_classical (step : S → S) :
    OccupationSuperoperator.classicalTransfer (symbolMatrix (R := R) step) = symbolMatrix step := by
  ext i j
  by_cases h : i = step j <;>
    simp [OccupationSuperoperator.classicalTransfer, symbolMatrix, h]

/-- Our existing superoperator now acts on deterministic symbol transitions.
No commutation, spectral diagonalization, or occupation averaging is used. -/
theorem symbol_diagonal (step : S → S) (x : S → R) :
    OccupationSuperoperator.act (symbolMatrix step) (Matrix.diagonal x) =
      Matrix.diagonal ((symbolMatrix step).mulVec x) := by
  rw [OccupationSuperoperator.diagonal_sector _ x (symbol_column step),
    symbol_classical]

theorem symbol_pullback (step : S → S) (v : S → R) (s : S) :
    (symbolMatrix step).transpose.mulVec v s = v (step s) := by
  simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply, symbolMatrix]

end Superoperator

/-- Concrete min-plus specialization: zero is infinity and multiplication
adds costs. The same exact symbol operator pulls back continuation costs. -/
theorem tropical_symbol_pullback {S : Type*} [Fintype S] [DecidableEq S]
    (step : S → S) (v : S → Tropical (WithTop ℕ)) (s : S) :
    (symbolMatrix (R := Tropical (WithTop ℕ)) step).transpose.mulVec v s =
      v (step s) := symbol_pullback step v s

#print axioms context_continuation
#print axioms continuation_occupation_same
#print axioms reachable_iff_word
#print axioms scoped_minimum
#print axioms symbol_diagonal
#print axioms symbol_pullback
#print axioms release_capacity
#print axioms context_relabel
#print axioms tropical_symbol_pullback
end Coeff2.Charlieplex.ExactSymbolTransformer
