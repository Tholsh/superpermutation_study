import Coeff2.CharliePhaseOrder

/-!
# Independent row phases and literal overlap assembly

This extends the existing PhaseOrder construction, not an isolated new model.
Phase choices are per ROW, not shared by all rows of a parent. Repeats,
containment, zero seams, and variable overlaps remain legal. No balanced
boundary graph, fixed header, or single Euler circuit is hypothesized.

The native two-clock catalog still has to supply literal infix invariance;
this file does not formally verify that executable or prove a shorter word.
-/
namespace Coeff2.Charlieplex.FreeRowCoverage

open PhaseOrder
open PacketAssembly
variable {α : Type*} [DecidableEq α]

/-- Every crossing has occupation, so one clock family's SUPPORT is whole.
The individual rows need not be whole, share phases, or be disjoint.
The native I+J incidence calculation supplies this premise for its family. -/
theorem complete_crossing_support {ι κ : Type*} (A : ι → Prop) (B : κ → Prop)
    (cover : ∀ i j, A i ∨ B j) : (∀ i, A i) ∨ (∀ j, B j) := by
  classical
  by_cases ha : ∀ i, A i
  · exact Or.inl ha
  · obtain ⟨i, hi⟩ := not_forall.mp ha
    exact Or.inr (fun j => (cover i j).resolve_left hi)

/-- Duplicate row indices are allowed. Each occurrence receives its own
choice after occurrence indices have been made distinct if needed. -/
def rowCatalog {ι κ : Type*} (rows : List ι)
    (realize : ι → κ → List α) (phase : ι → κ) : List (List α) :=
  rows.map (fun i => realize i (phase i))

/-- Literal occupation is the invariant. A row's new phase need not agree
with any other row, and the order is unrestricted. -/
theorem independent_phases_cover {ι κ : Type*} (rows : List ι)
    (realize : ι → κ → List α) (oldPhase newPhase : ι → κ)
    (alphabet : List α) (ordered : List (List α))
    (oldCover : ∀ p : List α, p.Perm alphabet →
      ∃ i ∈ rows, p.IsInfix (realize i (oldPhase i)))
    (invariant : ∀ i ∈ rows, ∀ p : List α, p.Perm alphabet →
      (p.IsInfix (realize i (oldPhase i)) ↔
       p.IsInfix (realize i (newPhase i))))
    (order : ordered.Perm (rowCatalog rows realize newPhase)) :
    ∀ p : List α, p.Perm alphabet → p.IsInfix (word ordered) := by
  apply reordered_covers _ ordered order alphabet
  intro p hp
  obtain ⟨i, hi, hpi⟩ := oldCover p hp
  refine ⟨realize i (newPhase i), ?_, (invariant i hi p hp).mp hpi⟩
  exact List.mem_map.mpr ⟨i, hi, rfl⟩

/-- Remove a chosen occupation set from every old row, then put that set
back through another clock. This is a UNION identity, not a disjointness
assumption or a guarantee that the new attachment is cheap. -/
theorem transfer_union {β : Type*} (occupied transferred : Set β)
    (inside : transferred ⊆ occupied) :
    (occupied \ transferred) ∪ transferred = occupied := by
  ext p
  constructor
  · intro hp
    rcases hp with hp | hp
    · exact hp.1
    · exact inside hp
  · intro hp
    by_cases ht : p ∈ transferred
    · exact Or.inr ht
    · exact Or.inl ⟨hp, ht⟩

omit [DecidableEq α] in
theorem row_length_sum (n : ℕ) (ps : List (List α))
    (visible : List α → ℕ)
    (lengths : ∀ p ∈ ps, p.length = (n+1)*visible p+(n-2)) :
    (ps.map List.length).sum =
      (n+1)*(ps.map visible).sum+(n-2)*ps.length := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    rw [lengths p (List.mem_cons_self),
      ih (fun q hq => lengths q (List.mem_cons_of_mem p hq))]
    ring

/-- The real price, valid for every n and arbitrary literal row overlaps.
In particular, overlaps longer than n-3 may repay repeated occupation.
Neither row count nor repetition count alone is a shortening certificate. -/
theorem arbitrary_overlap_ledger (n : ℕ) (ps : List (List α))
    (visible : List α → ℕ)
    (lengths : ∀ p ∈ ps, p.length = (n+1)*visible p+(n-2)) :
    ((word ps).length : ℤ) =
      (n+1 : ℕ)*(ps.map visible).sum + (n-2 : ℕ)*ps.length - seamSum ps := by
  have h := word_length ps
  rw [row_length_sum n ps visible lengths] at h
  have hz := congrArg (fun a : ℕ => (a : ℤ)) h
  simp only [Nat.cast_add, Nat.cast_mul] at hz
  omega

/-- The native assembler is LEFT-to-right and may overlap more than the
previous piece's length. This trace records the actual chosen seam lengths,
rather than silently equating them with pairwise adjacent overlaps. -/
def appendTrace (built : List α) : List (List α × ℕ) → List α
  | [] => built
  | (p,k) :: tail => appendTrace (glue built p k) tail

def legalTrace (built : List α) : List (List α × ℕ) → Prop
  | [] => True
  | (p,k) :: tail => IsSeam built p k ∧ legalTrace (glue built p k) tail

omit [DecidableEq α] in
theorem trace_length (built : List α) (steps : List (List α × ℕ))
    (legal : legalTrace built steps) :
    (appendTrace built steps).length + (steps.map Prod.snd).sum =
      built.length + (steps.map (fun s => s.1.length)).sum := by
  induction steps generalizing built with
  | nil => simp [appendTrace]
  | cons s tail ih =>
    obtain ⟨p,k⟩ := s
    obtain ⟨seam,rest⟩ := legal
    have hg := glue_length built p k seam
    have ht := ih (glue built p k) rest
    simp only [appendTrace, List.map_cons, List.sum_cons] at *
    omega

omit [DecidableEq α] in
theorem trace_retains_prefix (built : List α) (steps : List (List α × ℕ))
    (legal : legalTrace built steps) : built.IsInfix (appendTrace built steps) := by
  induction steps generalizing built with
  | nil => exact ⟨[],[],by simp [appendTrace]⟩
  | cons s tail ih =>
    obtain ⟨p,k⟩ := s
    obtain ⟨_,rest⟩ := legal
    exact (glue_left built p k).trans (ih (glue built p k) rest)

omit [DecidableEq α] in
theorem trace_retains_row (built : List α) (steps : List (List α × ℕ))
    (legal : legalTrace built steps) (s : List α × ℕ) (member : s ∈ steps) :
    s.1.IsInfix (appendTrace built steps) := by
  induction steps generalizing built with
  | nil => simp at member
  | cons t tail ih =>
    obtain ⟨p,k⟩ := t
    obtain ⟨seam,rest⟩ := legal
    rcases List.mem_cons.mp member with he | hm
    · subst s
      exact (glue_right built p k seam).trans
        (trace_retains_prefix (glue built p k) tail rest)
    · exact ih (glue built p k) rest hm

omit [DecidableEq α] in
theorem trace_covers (steps : List (List α × ℕ)) (alphabet : List α)
    (legal : legalTrace [] steps)
    (cover : ∀ p : List α, p.Perm alphabet →
      ∃ s ∈ steps, p.IsInfix s.1) :
    ∀ p : List α, p.Perm alphabet → p.IsInfix (appendTrace [] steps) := by
  intro p hp
  obtain ⟨s,hs,hpi⟩ := cover p hp
  exact hpi.trans (trace_retains_row [] steps legal s hs)

omit [DecidableEq α] in
theorem literal_trace_ledger (n : ℕ) (steps : List (List α × ℕ))
    (visible : List α → ℕ) (legal : legalTrace [] steps)
    (lengths : ∀ s ∈ steps, s.1.length = (n+1)*visible s.1+(n-2)) :
    ((appendTrace [] steps).length : ℤ) =
      (n+1 : ℕ)*(steps.map (fun s => visible s.1)).sum +
      (n-2 : ℕ)*steps.length - (steps.map Prod.snd).sum := by
  have cost := row_length_sum n (steps.map Prod.fst) visible (by
    intro p hp
    obtain ⟨s, hs, he⟩ := List.mem_map.mp hp
    exact he ▸ lengths s hs)
  simp only [List.map_map, List.length_map] at cost
  change (steps.map (fun s => s.1.length)).sum =
    (n+1)*(steps.map (fun s => visible s.1)).sum+(n-2)*steps.length at cost
  have h := trace_length [] steps legal
  simp only [List.length_nil, Nat.zero_add] at h
  rw [cost] at h
  have hz := congrArg (fun a : ℕ => (a : ℤ)) h
  simp only [Nat.cast_add, Nat.cast_mul] at hz
  omega

#print axioms complete_crossing_support
#print axioms independent_phases_cover
#print axioms transfer_union
#print axioms row_length_sum
#print axioms arbitrary_overlap_ledger
#print axioms trace_length
#print axioms trace_retains_prefix
#print axioms trace_retains_row
#print axioms trace_covers
#print axioms literal_trace_ledger
end Coeff2.Charlieplex.FreeRowCoverage
