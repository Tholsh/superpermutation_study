import Coeff2.CharlieOccupationBinomial

/-!
# An exact frozen-cache Pascal window

The old cache is never discarded. Only writes made inside a bounded lookahead
are omitted, and only when the no-short-return hypothesis proves that the
future endpoints cannot repeat. There is no assumption that move operators
commute. Numeric girth values of the C++ frame are not axioms of this module.
-/

namespace Coeff2.Charlieplex

section Writes
variable {α : Type*} [DecidableEq α]

def occupationWriteDefect (occupied : Finset α) : List α → ℕ
  | [] => 0
  | address :: rest => (if address ∈ occupied then 1 else 0) +
      occupationWriteDefect (insert address occupied) rest

def frozenWriteHits (occupied : Finset α) (writes : List α) : ℕ :=
  (writes.filter fun address => decide (address ∈ occupied)).length

theorem occupationWriteDefect_add_final_card (occupied : Finset α) (writes : List α) :
    occupationWriteDefect occupied writes + (occupied ∪ writes.toFinset).card =
      writes.length + occupied.card := by
  induction writes generalizing occupied with
  | nil => simp [occupationWriteDefect]
  | cons address rest ih =>
      have h := ih (insert address occupied)
      have hunion : insert address occupied ∪ rest.toFinset =
          occupied ∪ (address :: rest).toFinset := by
        ext x
        simp
      rw [hunion] at h
      simp only [occupationWriteDefect, List.length_cons]
      by_cases hmem : address ∈ occupied
      · rw [if_pos hmem, Finset.insert_eq_of_mem hmem]
        rw [Finset.insert_eq_of_mem hmem] at h
        omega
      · rw [if_neg hmem]
        rw [Finset.card_insert_of_notMem hmem] at h
        omega

/-- Exact collision count from the distinct footprint and number of writes. -/
theorem occupationWriteDefect_eq_footprint (occupied : Finset α) (writes : List α) :
    occupationWriteDefect occupied writes =
      writes.length - (writes.toFinset \ occupied).card := by
  have h := occupationWriteDefect_add_final_card occupied writes
  have hcard := Finset.card_sdiff_add_card writes.toFinset occupied
  rw [Finset.union_comm] at hcard
  omega

theorem occupationWriteDefect_same_footprint (occupied : Finset α) (left right : List α)
    (hlen : left.length = right.length) (hset : left.toFinset = right.toFinset) :
    occupationWriteDefect occupied left = occupationWriteDefect occupied right := by
  simp only [occupationWriteDefect_eq_footprint, hlen, hset]

/-- With no internal duplicate, querying the old cache is already exact. -/
theorem occupationWriteDefect_eq_frozen_of_nodup (occupied : Finset α) (writes : List α)
    (h : writes.Nodup) : occupationWriteDefect occupied writes = frozenWriteHits occupied writes := by
  have hlen := List.toFinset_card_of_nodup h
  have hsplit := Finset.card_sdiff_add_card_inter writes.toFinset occupied
  have hfilter : writes.toFinset ∩ occupied =
      (writes.filter fun address => decide (address ∈ occupied)).toFinset := by
    ext address
    simp
  have hfilterlen := List.toFinset_card_of_nodup
    (List.Nodup.filter (fun address => decide (address ∈ occupied)) h)
  rw [hfilter] at hsplit
  unfold frozenWriteHits
  rw [occupationWriteDefect_eq_footprint]
  omega

/-- The Pascal coefficient update for one fixed-cache membership bit. -/
theorem frozenWriteHits_pascal (occupied : Finset α) (address : α) (rest : List α) (k : ℕ) :
    (frozenWriteHits occupied (address :: rest)).choose (k + 1) =
      (frozenWriteHits occupied rest).choose (k + 1) +
        if address ∈ occupied then (frozenWriteHits occupied rest).choose k else 0 := by
  by_cases hmem : address ∈ occupied
  · simp [frozenWriteHits, hmem, Nat.choose_succ_succ']
    omega
  · simp [frozenWriteHits, hmem]

/-- A duplicate-free prefix can introduce only one additional collision at
its last write. This is the exact one-cycle correction, not a union bound. -/
theorem occupationWriteDefect_append_of_nodup (occupied : Finset α)
    (writes : List α) (last : α) (h : writes.Nodup) :
    occupationWriteDefect occupied (writes ++ [last]) =
      frozenWriteHits occupied (writes ++ [last]) +
        if last ∈ writes ∧ last ∉ occupied then 1 else 0 := by
  by_cases hlast : last ∈ writes
  · have hset : (writes ++ [last]).toFinset = writes.toFinset := by
      ext x
      simp only [List.mem_toFinset, List.mem_append, List.mem_singleton]
      constructor
      · rintro (hx | rfl)
        · exact hx
        · exact hlast
      · exact Or.inl
    have hbefore := occupationWriteDefect_add_final_card occupied writes
    have hafter := occupationWriteDefect_add_final_card occupied (writes ++ [last])
    rw [hset] at hafter
    rw [occupationWriteDefect_eq_frozen_of_nodup occupied writes h] at hbefore
    have hfrozen : frozenWriteHits occupied (writes ++ [last]) =
        frozenWriteHits occupied writes + if last ∈ occupied then 1 else 0 := by
      by_cases hmem : last ∈ occupied <;> simp [frozenWriteHits, hmem]
    rw [hfrozen]
    simp only [List.length_append, List.length_singleton] at hafter
    by_cases hmem : last ∈ occupied <;> simp only [hlast, hmem, not_true_eq_false,
      not_false_eq_true, and_true, and_false, if_true, if_false] <;> omega
  · have hfull : (writes ++ [last]).Nodup := by
      simp only [List.nodup_append, h, List.nodup_singleton, true_and,
        List.mem_singleton, forall_eq]
      intro a ha heq
      exact hlast (heq ▸ ha)
    rw [occupationWriteDefect_eq_frozen_of_nodup occupied _ hfull]
    simp [hlast]

end Writes

section Girth
variable {G : Type*} [Group G]

/-- A graph-theoretic condition on the complete specified generator frame. -/
def NoGeneratorReturnsBelow (generators : Finset G) (g : ℕ) : Prop :=
  ∀ word : List G, (∀ a ∈ word, a ∈ generators) →
    0 < word.length → word.length < g → word.prod ≠ 1

theorem cayley_legal_of_short_return_free (generators : Finset G) (g : ℕ)
    (hreturn : NoGeneratorReturnsBelow generators g) (start : G) (word : List G)
    (hletters : ∀ a ∈ word, a ∈ generators) (hlen : word.length < g) :
    CayleyOccupationLegal start word := by
  apply (cayleyOccupationLegal_iff_identityFactorFree start word).mpr
  intro endpoint hend begin hbegin
  have hlength : ((word.take endpoint).drop begin).length = endpoint - begin := by
    simp [List.length_drop, List.length_take, Nat.min_eq_left hend]
  apply hreturn ((word.take endpoint).drop begin)
  · intro a ha
    exact hletters a (List.mem_of_mem_take (List.mem_of_mem_drop ha))
  · omega
  · omega

def cayleyFutureStates (start : G) (word : List G) : List G :=
  (cayleyOccupationStates start word).tail

/-- There are h future endpoints, so their pairwise gaps are at most h-1.
This is why the exact horizon includes g, not only g-1. -/
theorem cayleyFutureStates_nodup_of_horizon_le (generators : Finset G) (g : ℕ)
    (hreturn : NoGeneratorReturnsBelow generators g) (start : G) (word : List G)
    (hletters : ∀ a ∈ word, a ∈ generators) (hlen : word.length ≤ g) :
    (cayleyFutureStates start word).Nodup := by
  cases word with
  | nil => simp [cayleyFutureStates, cayleyOccupationStates]
  | cons a rest =>
      have hrest : rest.length < g := by simp only [List.length_cons] at hlen; omega
      have hlegal := cayley_legal_of_short_return_free generators g hreturn (start * a) rest
        (fun b hb => hletters b (List.mem_cons_of_mem a hb)) hrest
      simpa [CayleyOccupationLegal, cayleyFutureStates, cayleyOccupationStates] using hlegal

variable [DecidableEq G]

/-- Pointwise equality preserves every collision coefficient, not just legality.
The occupied set may be any accumulated history and is still queried exactly. -/
theorem frozen_cayley_defect_exact (generators : Finset G) (g : ℕ)
    (hreturn : NoGeneratorReturnsBelow generators g) (occupied : Finset G)
    (start : G) (word : List G) (hletters : ∀ a ∈ word, a ∈ generators)
    (hlen : word.length ≤ g) :
    occupationWriteDefect occupied (cayleyFutureStates start word) =
      frozenWriteHits occupied (cayleyFutureStates start word) := by
  apply occupationWriteDefect_eq_frozen_of_nodup
  exact cayleyFutureStates_nodup_of_horizon_le generators g hreturn start word hletters hlen

theorem frozen_cayley_pascal_coefficient_exact (generators : Finset G) (g : ℕ)
    (hreturn : NoGeneratorReturnsBelow generators g) (occupied : Finset G)
    (start : G) (word : List G) (hletters : ∀ a ∈ word, a ∈ generators)
    (hlen : word.length ≤ g) (k : ℕ) :
    (occupationWriteDefect occupied (cayleyFutureStates start word)).choose k =
      (frozenWriteHits occupied (cayleyFutureStates start word)).choose k := by
  rw [frozen_cayley_defect_exact generators g hreturn occupied start word hletters hlen]

omit [DecidableEq G] in
/-- At a shortest-return boundary, a new endpoint can revisit only the
initial endpoint of this short block, not one of its interior endpoints. -/
theorem girth_boundary_membership (generators : Finset G) (g : ℕ)
    (hreturn : NoGeneratorReturnsBelow generators g) (start : G) (word : List G)
    (last : G) (hletters : ∀ a ∈ word, a ∈ generators) (hlast : last ∈ generators)
    (hlen : word.length + 1 ≤ g) :
    cayleyOccupationEndpoint start word * last ∈ cayleyOccupationStates start word ↔
      cayleyOccupationEndpoint start word * last = start := by
  constructor
  · intro hmem
    obtain ⟨i, hi, hclosed⟩ :=
      (next_mem_occupation_iff_exists_suffix_return start word last).mp hmem
    have hizero : i = 0 := by
      by_contra hne
      have hno := hreturn (word.drop i ++ [last])
      have hmembers : ∀ a ∈ word.drop i ++ [last], a ∈ generators := by
        intro a ha
        rcases List.mem_append.mp ha with ha | ha
        · exact hletters a (List.mem_of_mem_drop ha)
        · simpa using (List.mem_singleton.mp ha ▸ hlast)
      have hpositive : 0 < (word.drop i ++ [last]).length := by simp
      have hshort : (word.drop i ++ [last]).length < g := by
        simp only [List.length_append, List.length_drop, List.length_singleton]
        omega
      apply hno hmembers hpositive hshort
      simpa [List.prod_append] using hclosed
    subst i
    simp only [List.drop_zero] at hclosed
    rw [cayleyOccupationEndpoint_eq_mul_prod, mul_assoc, hclosed, mul_one]
  · intro heq
    rw [heq]
    cases word <;> simp [cayleyOccupationStates]

/-- One step beyond the frozen-cache window is still exact after the single
shortest-cycle correction. Here `first` is the first new endpoint. -/
theorem frozen_cayley_one_cycle_correction (generators : Finset G) (g : ℕ)
    (hreturn : NoGeneratorReturnsBelow generators g) (occupied : Finset G)
    (first : G) (middle : List G) (last : G)
    (hletters : ∀ a ∈ middle, a ∈ generators) (hlast : last ∈ generators)
    (hlen : middle.length + 1 ≤ g) :
    occupationWriteDefect occupied (cayleyOccupationStates first (middle ++ [last])) =
      frozenWriteHits occupied (cayleyOccupationStates first (middle ++ [last])) +
        if cayleyOccupationEndpoint first middle * last = first ∧
          cayleyOccupationEndpoint first middle * last ∉ occupied then 1 else 0 := by
  rw [cayleyOccupationStates_append_singleton]
  have hnodup : (cayleyOccupationStates first middle).Nodup :=
    cayley_legal_of_short_return_free generators g hreturn first middle hletters (by omega)
  rw [occupationWriteDefect_append_of_nodup occupied _ _ hnodup]
  simp only [girth_boundary_membership generators g hreturn first middle last hletters hlast hlen]

end Girth
end Coeff2.Charlieplex
