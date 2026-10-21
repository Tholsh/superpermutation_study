import Coeff2.CharlieDegenerationSets
import Coeff2.CharlieKernelPositive

/-!
# Cycle compression preserves literal occupation and completion sets

Clean symbol appends are deterministic rotations. Full rotation orbits can be
stored as single flags; only the residual partial-orbit addresses need masks.
This proves exactness, not a bound on the number of partial orbits in a search.
Unlike the earlier CharlieOrbitPushdown module, this representation does not
require last-in-first-out revisits. The byte codec is checked separately in C++.
-/
namespace Coeff2.Charlieplex
open KernelPositive

/-- The omitted clean symbol in the reduced codec is unique. -/
theorem clean_append_unique {n : ℕ} {boundary : List ℕ} {a b : ℕ}
    (ha : IsPermWord n (boundary ++ [a])) (hb : IsPermWord n (boundary ++ [b])) :
    a = b := by
  have hnot : a ∉ boundary := by
    intro hmem
    exact ((List.nodup_append.mp ha.nodup).2.2 a hmem a (by simp)) rfl
  have hmem : a ∈ (boundary ++ [b]).toFinset := by
    rw [hb.toFinset_eq, ← ha.toFinset_eq]
    simp
  have hcases : a ∈ boundary ∨ a = b := by simpa [or_comm] using hmem
  exact hcases.resolve_left hnot

/-- At a permutation window, the codec's next clean append is precisely the
rotation move: a::rest becomes rest++[a]. No occupation assumption is made. -/
theorem clean_append_is_rotation {n first symbol : ℕ} {rest : List ℕ}
    (h : IsPermWord n (first :: rest)) :
    literalPermTest n (rest ++ [symbol]) = true ↔ symbol = first := by
  have hrot : IsPermWord n (rest ++ [first]) := by
    simpa [List.rotate_cons_succ] using isPermWord_rotate h 1
  rw [literalPermTest_eq_true]
  constructor
  · intro hs
    exact clean_append_unique hs hrot
  · rintro rfl
    exact hrot

/-- A macro can be expanded in pieces without losing seam windows or writes. -/
theorem literalFutureWrites_append (n : ℕ) (state : LiteralSearchState)
    (left right : List ℕ) :
    literalFutureWrites n state (left ++ right) = literalFutureWrites n state left ++
      literalFutureWrites n (literalStateRun n state left) right := by
  induction left generalizing state with
  | nil => simp [literalFutureWrites, literalStateRun]
  | cons symbol rest ih => simp [literalFutureWrites, literalStateRun, ih, List.append_assoc]

def rotationFootprint (marker : ℕ) (reduced : List ℕ) : Finset (List ℕ) :=
  (orbitWords marker reduced).toFinset

theorem rotationFootprint_card (marker : ℕ) (reduced : List ℕ)
    (h : (reduced ++ [marker]).Nodup) :
    (rotationFootprint marker reduced).card = reduced.length + 1 := by
  rw [rotationFootprint, List.toFinset_card_of_nodup (orbitWords_nodup marker reduced h)]
  simp [orbitWords]

/-- Marker-last representatives distinguish disjoint literal rotation orbits. -/
theorem rotationFootprint_disjoint (marker : ℕ) (left right : List ℕ)
    (hleft : (left ++ [marker]).Nodup) (hne : left ≠ right) :
    Disjoint (rotationFootprint marker left) (rotationFootprint marker right) := by
  apply Finset.disjoint_left.mpr
  intro address hl hr
  exact orbitWords_disjoint marker left right hleft hne
    (List.mem_toFinset.mp hl) (List.mem_toFinset.mp hr)

/-- The trace includes the entry permutation. If entry is already processed,
use the remaining arc instead; charging a full orbit would count entry twice. -/
theorem wholeOrbit_repeat_cost (marker : ℕ) (reduced : List ℕ)
    (h : (reduced ++ [marker]).Nodup) (occupied : Finset (List ℕ)) :
    occupationWriteDefect occupied (orbitWords marker reduced) =
      (rotationFootprint marker reduced ∩ occupied).card := by
  rw [occupationWriteDefect_split]
  have hz : occupationWriteDefect ∅ (orbitWords marker reduced) = 0 := by
    rw [occupationWriteDefect_zero_iff]
    exact ⟨orbitWords_nodup marker reduced h, by simp⟩
  simp [hz, rotationFootprint]

def fullOrbitUnion (marker : ℕ) (full : Finset (List ℕ)) : Finset (List ℕ) :=
  full.biUnion (rotationFootprint marker)

/-- With full flags, orbit membership is all-or-none. -/
theorem rotationFootprint_inter_full (marker : ℕ) (reduced : List ℕ)
    (h : (reduced ++ [marker]).Nodup) (full : Finset (List ℕ)) :
    rotationFootprint marker reduced ∩ fullOrbitUnion marker full =
      if reduced ∈ full then rotationFootprint marker reduced else ∅ := by
  by_cases hp : reduced ∈ full
  · rw [if_pos hp]
    apply Finset.inter_eq_left.mpr
    intro address ha
    exact Finset.mem_biUnion.mpr ⟨reduced, hp, ha⟩
  · rw [if_neg hp]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro address ha
    obtain ⟨hl, hr⟩ := Finset.mem_inter.mp ha
    obtain ⟨other, ho, hother⟩ := Finset.mem_biUnion.mp hr
    have hne : reduced ≠ other := by rintro rfl; exact hp ho
    exact Finset.disjoint_left.mp (rotationFootprint_disjoint marker reduced other h hne) hl hother

/-- Exact collision cost against compressed occupation: a full flag costs an
entire orbit; otherwise query only its residual phase mask. -/
theorem wholeOrbit_compressed_cost (marker : ℕ) (reduced : List ℕ)
    (h : (reduced ++ [marker]).Nodup) (full : Finset (List ℕ))
    (residual : Finset (List ℕ)) :
    occupationWriteDefect (fullOrbitUnion marker full ∪ residual) (orbitWords marker reduced) =
      if reduced ∈ full then reduced.length + 1
      else (rotationFootprint marker reduced ∩ residual).card := by
  rw [wholeOrbit_repeat_cost marker reduced h, Finset.inter_union_distrib_left,
    rotationFootprint_inter_full marker reduced h]
  by_cases hp : reduced ∈ full
  · simp [hp, Finset.union_eq_left.mpr (Finset.inter_subset_left), rotationFootprint_card marker reduced h]
  · simp [hp]

/-- Promote only genuinely completed cycles; retain every other address. -/
def completedOrbitFlags (marker : ℕ) (catalogue : Finset (List ℕ))
    (occupied : Finset (List ℕ)) : Finset (List ℕ) :=
  catalogue.filter fun reduced => rotationFootprint marker reduced ⊆ occupied

theorem promotedOrbitUnion_subset (marker : ℕ) (catalogue : Finset (List ℕ))
    (occupied : Finset (List ℕ)) :
    fullOrbitUnion marker (completedOrbitFlags marker catalogue occupied) ⊆ occupied := by
  intro address ha
  obtain ⟨reduced, hr, haddr⟩ := Finset.mem_biUnion.mp ha
  exact (Finset.mem_filter.mp hr).2 haddr

/-- Lossless occupation compression for any finite cache and catalogue.
An incomplete catalogue affects compression ratio, never correctness. -/
theorem cycleOccupation_roundtrip (marker : ℕ) (catalogue : Finset (List ℕ))
    (occupied : Finset (List ℕ)) :
    fullOrbitUnion marker (completedOrbitFlags marker catalogue occupied) ∪
      (occupied \ fullOrbitUnion marker (completedOrbitFlags marker catalogue occupied)) =
        occupied := by
  rw [Finset.union_comm]
  exact Finset.sdiff_union_of_subset (promotedOrbitUnion_subset marker catalogue occupied)

def cycleDecodedState (marker : ℕ) (catalogue : Finset (List ℕ))
    (state : LiteralSearchState) : LiteralSearchState :=
  let full := fullOrbitUnion marker (completedOrbitFlags marker catalogue state.occupied)
  {state with occupied := full ∪ (state.occupied \ full)}

theorem cycleDecodedState_eq (marker : ℕ) (catalogue : Finset (List ℕ))
    (state : LiteralSearchState) : cycleDecodedState marker catalogue state = state := by
  simp only [cycleDecodedState, cycleOccupation_roundtrip]

/-- Not merely cardinality preservation: every genuine literal completion is
unchanged by replacing occupation with full-cycle flags and residual phases. -/
theorem cycleCompression_preserves_completions (n budget horizon marker : ℕ)
    (catalogue : Finset (List ℕ)) (state : LiteralSearchState) :
    literalSuccessfulSuffixes n budget horizon (cycleDecodedState marker catalogue state) =
      literalSuccessfulSuffixes n budget horizon state := by
  rw [cycleDecodedState_eq]

end Coeff2.Charlieplex
