import Coeff2.CharlieContextReplacement
import Coeff2.CharlieCoordinatedExchange
import Coeff2.CharliePacketAssembly
import Coeff2.CharlieOccupationWriteTransport

/-!
# Labelled occupation fronts and literal shared-waste gluing

All footprints below are calculated by the existing literal scanner. Repeats,
dirty boundary frames, partial courses and arbitrary orders are permitted.
The sign criterion proves a property of a REALIZED seam, not the existence of
a cheap seam or a universal short construction. No no-repeat premise occurs.
-/
namespace Coeff2.Charlieplex.SharedWasteResponse
open LiteralReservoir ThreeLevelBoundary PacketAssembly

section Fronts
variable {X : Type*} [DecidableEq X]

def bit (U : Finset X) (x : X) : ℤ := if x ∈ U then 1 else 0

def diff (next : X → X) (d : X → ℤ) (x : X) : ℤ := d (next x) - d x

theorem bit_union (U H : Finset X) (x : X) :
    bit (U ∪ H) x = bit U x + bit H x - bit U x * bit H x := by
  classical
  by_cases hu : x ∈ U <;> by_cases hh : x ∈ H <;> simp [bit, hu, hh]

omit [DecidableEq X] in
/-- Exact discrete product rule, including its shift. -/
theorem diff_mul (next : X → X) (d h : X → ℤ) (x : X) :
    diff next (fun y => d y * h y) x =
      diff next d x * h x + d (next x) * diff next h x := by
  simp only [diff]
  ring

/-- The coupled response of actual labelled occupation fronts. -/
theorem front_union (next : X → X) (U H : Finset X) (x : X) :
    diff next (bit (U ∪ H)) x =
      (1 - bit H x) * diff next (bit U) x +
      (1 - bit U (next x)) * diff next (bit H) x := by
  simp only [diff, bit_union]
  ring

end Fronts

abbrev footprint (n : ℕ) (word : List ℕ) : Finset (List ℕ) :=
  literalOccupation n word

def appendCharge (n : ℕ) (boundary : List ℕ) (U : Finset (List ℕ))
    (word : List ℕ) : ℤ :=
  (word.length : ℤ) - ((emitted n boundary word).toFinset \ U).card

def charge (n : ℕ) (U : Finset (List ℕ)) (word : List ℕ) : ℤ :=
  (word.length : ℤ) - (n - 1 : ℕ) - (footprint n word \ U).card

theorem literal_front_update (n : ℕ) (state : LiteralSearchState)
    (word : List ℕ) (next : List ℕ → List ℕ) (p : List ℕ) :
    diff next (bit (literalStateRun n state word).occupied) p =
      (1 - bit (emitted n state.boundary word).toFinset p) *
        diff next (bit state.occupied) p +
      (1 - bit state.occupied (next p)) *
        diff next (bit (emitted n state.boundary word).toFinset) p := by
  rw [run_occupation]
  exact front_union next _ _ p

theorem appendCharge_nonnegative (n : ℕ) (boundary : List ℕ)
    (U : Finset (List ℕ)) (word : List ℕ) :
    0 ≤ appendCharge n boundary U word := by
  have h1 := Finset.card_le_card (Finset.sdiff_subset :
    (emitted n boundary word).toFinset \ U ⊆ (emitted n boundary word).toFinset)
  have h2 := List.toFinset_card_le (emitted n boundary word)
  have h3 := emitted_length_le n boundary word
  unfold appendCharge
  omega

/-- For a complete initial boundary, the normalized charge is actual
nonnegative waste: fresh distinct labels cannot outnumber appended symbols. -/
theorem charge_nonnegative (n : ℕ) (hn : 1 ≤ n)
    (U : Finset (List ℕ)) (word : List ℕ) (hw : n-1 ≤ word.length) :
    0 ≤ charge n U word := by
  have hh : (word.take (n-1)).length = n-1 := by
    simp only [List.length_take, Nat.min_eq_left hw]
  have hc : footprint n word \ U ⊆ (literalStateOf n word).occupied :=
    Finset.sdiff_subset
  have h := ContextReplacement.required_write_bound n hn
    (word.take (n-1)) (word.drop (n-1)) hh (footprint n word \ U)
    (by simpa only [List.take_append_drop] using hc)
  rw [List.take_append_drop] at h
  unfold charge
  omega

section Sets
variable {X : Type*} [DecidableEq X]

/-- Fresh occupation partitions into previously selected and incoming parts. -/
theorem fresh_partition (U C A : Finset X) (hc : C ⊆ A) :
    (A \ U).card = (C \ U).card + (A \ (U ∪ C)).card := by
  have he : A \ U = (C \ U) ∪ (A \ (U ∪ C)) := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · intro hx
      by_cases h : x ∈ C
      · exact Or.inl ⟨h, hx.2⟩
      · exact Or.inr ⟨hx.1, by tauto⟩
    · rintro (hx | hx)
      · exact ⟨hc hx.1, hx.2⟩
      · exact ⟨hx.1, by tauto⟩
  have hd : Disjoint (C \ U) (A \ (U ∪ C)) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    simp only [Finset.mem_sdiff, Finset.mem_union] at hx hy
    tauto
  rw [he, Finset.card_union_of_disjoint hd]

theorem fresh_union_card (U A B : Finset X) :
    ((A ∪ B) \ U).card + ((A ∩ B) \ U).card =
      (A \ U).card + (B \ U).card := by
  have hu : (A ∪ B) \ U = (A \ U) ∪ (B \ U) := by
    ext x; simp only [Finset.mem_sdiff, Finset.mem_union]; tauto
  have hi : (A ∩ B) \ U = (A \ U) ∩ (B \ U) := by
    ext x; simp only [Finset.mem_sdiff, Finset.mem_inter]; tauto
  rw [hu, hi]
  exact Finset.card_union_add_card_inter _ _

end Sets

/-- True telescoping: the second response receives the UPDATED occupation. -/
theorem appendCharge_append (n : ℕ) (boundary : List ℕ)
    (U : Finset (List ℕ)) (left right : List ℕ) :
    appendCharge n boundary U (left ++ right) =
      appendCharge n boundary U left +
      appendCharge n (endBoundary n boundary left)
        (U ∪ (emitted n boundary left).toFinset) right := by
  let A := (emitted n boundary left).toFinset
  let B := (emitted n (endBoundary n boundary left) right).toFinset
  have h := fresh_partition U A (A ∪ B) Finset.subset_union_left
  have he : (A ∪ B) \ (U ∪ A) = B \ (U ∪ A) := by
    ext x; simp only [Finset.mem_sdiff, Finset.mem_union]; tauto
  rw [he] at h
  simp only [appendCharge, emitted_append, List.toFinset_append, List.length_append]
  dsimp only [A, B] at h
  omega

theorem footprint_mono (n : ℕ) {a b : List ℕ} (h : a.IsInfix b) :
    footprint n a ⊆ footprint n b := by
  intro p hp
  obtain ⟨hperm, hi⟩ := (mem_literalPermutationWindows_iff n a p).mp
    (List.mem_toFinset.mp hp)
  exact List.mem_toFinset.mpr ((mem_literalPermutationWindows_iff n b p).mpr
    ⟨hperm, hi.trans h⟩)

/-- An overlap of n-1 or more symbols leaves no unaccounted seam windows. -/
theorem footprint_long_shared (n : ℕ) (hn : 1 ≤ n)
    (before common after : List ℕ) (hc : n - 1 ≤ common.length) :
    footprint n ((before ++ common) ++ after) =
      footprint n (before ++ common) ∪ footprint n (common ++ after) := by
  have h1 := ContextReplacement.occupation_append n hn (before ++ common) after
  have h2 := ContextReplacement.occupation_append n hn common after
  have hb := ContextReplacement.lastSymbols_long_append (n-1) before common hc
  have hm : footprint n common ⊆ footprint n (before ++ common) :=
    footprint_mono n List.infix_append_right
  change footprint n ((before ++ common) ++ after) =
    footprint n (before ++ common) ∪
      (emitted n (lastSymbols (n-1) (before ++ common)) after).toFinset at h1
  change footprint n (common ++ after) = footprint n common ∪
    (emitted n (lastSymbols (n-1) common) after).toFinset at h2
  rw [h1, hb, h2, ← Finset.union_assoc, Finset.union_eq_left.mpr hm]

theorem footprint_glue (n : ℕ) (hn : 1 ≤ n) (a b : List ℕ) (k : ℕ)
    (hs : IsSeam a b k) (hk : n-1 ≤ k) :
    footprint n (glue a b k) = footprint n a ∪ footprint n b := by
  have ha : a = a.take (a.length-k) ++ b.take k := by
    rw [← hs.2.2, List.take_append_drop]
  have hc : n-1 ≤ (b.take k).length := by
    simp only [List.length_take, Nat.min_eq_left hs.2.1]
    exact hk
  have h := footprint_long_shared n hn (a.take (a.length-k)) (b.take k) (b.drop k) hc
  rw [← ha, List.take_append_drop] at h
  exact h

def extraShared (n : ℕ) (U : Finset (List ℕ)) (a b common : List ℕ) :
    Finset (List ℕ) :=
  (footprint n a ∩ footprint n b) \ (U ∪ footprint n common)

def interaction (n : ℕ) (U : Finset (List ℕ)) (a b : List ℕ) (k : ℕ) : ℤ :=
  charge n U (glue a b k) - charge n U a - charge n U b

def bridgeFresh (n : ℕ) (U : Finset (List ℕ)) (a b : List ℕ) (k : ℕ) :
    Finset (List ℕ) :=
  footprint n (glue a b k) \ (U ∪ (footprint n a ∪ footprint n b))

/-- Any seam, including short overlaps: crossing labels are scanned literally. -/
theorem interaction_general (n : ℕ) (U : Finset (List ℕ))
    (a b : List ℕ) (k : ℕ) (hs : IsSeam a b k) :
    interaction n U a b k = (n-1 : ℕ) - (k : ℤ) +
      (((footprint n a ∩ footprint n b) \ U).card : ℤ) -
      (bridgeFresh n U a b k).card := by
  have hsub : footprint n a ∪ footprint n b ⊆ footprint n (glue a b k) :=
    Finset.union_subset (footprint_mono n (glue_left a b k))
      (footprint_mono n (glue_right a b k hs))
  have hp := fresh_partition U (footprint n a ∪ footprint n b)
    (footprint n (glue a b k)) hsub
  have hu := fresh_union_card U (footprint n a) (footprint n b)
  have hl := glue_length a b k hs
  unfold interaction charge bridgeFresh
  omega

/-- The unavoidable occupation is removed exactly, rather than by a bound. -/
theorem appendCharge_potential (n : ℕ) (state : LiteralSearchState)
    (word : List ℕ) :
    appendCharge n state.boundary state.occupied word =
      (word.length : ℤ) + state.occupied.card -
        (literalStateRun n state word).occupied.card := by
  have h := Finset.card_sdiff_add_card (emitted n state.boundary word).toFinset
    state.occupied
  rw [Finset.union_comm] at h
  rw [run_occupation]
  unfold appendCharge
  omega

/-- The sign comes from shared waste, not a squared spectral norm. -/
theorem interaction_factor (n : ℕ) (hn : 1 ≤ n) (U : Finset (List ℕ))
    (a b : List ℕ) (k : ℕ) (hs : IsSeam a b k) (hk : n-1 ≤ k) :
    interaction n U a b k = (extraShared n U a b (b.take k)).card -
      charge n U (b.take k) := by
  have hcA : footprint n (b.take k) ⊆ footprint n a := by
    rw [← hs.2.2]
    exact footprint_mono n (List.drop_suffix _ _).isInfix
  have hcB : footprint n (b.take k) ⊆ footprint n b :=
    footprint_mono n (List.take_prefix _ _).isInfix
  have hc : footprint n (b.take k) ⊆ footprint n a ∩ footprint n b :=
    Finset.subset_inter hcA hcB
  have hp := fresh_partition U (footprint n (b.take k))
    (footprint n a ∩ footprint n b) hc
  have hu := fresh_union_card U (footprint n a) (footprint n b)
  have hl := glue_length a b k hs
  have hcLen : (b.take k).length = k := by simp [List.length_take, Nat.min_eq_left hs.2.1]
  unfold interaction charge extraShared
  rw [footprint_glue n hn a b k hs hk]
  omega

theorem negative_interaction_iff (n : ℕ) (hn : 1 ≤ n)
    (U : Finset (List ℕ)) (a b : List ℕ) (k : ℕ)
    (hs : IsSeam a b k) (hk : n-1 ≤ k) :
    interaction n U a b k < 0 ↔
      ((extraShared n U a b (b.take k)).card : ℤ) < charge n U (b.take k) := by
  rw [interaction_factor n hn U a b k hs hk]
  omega

end Coeff2.Charlieplex.SharedWasteResponse
