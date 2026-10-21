/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Coeff2.CharlieGauge
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Finset.Lattice.Lemmas

/-!
# A finite Boolean cache machine

This file separates the stateful cache layer from the combinational
half-adder analogy.  A state consists of a phase bit and a finite set of
occupied addresses.  An input consists of a phase delta and a finite write
mask; masks are set-semantic, so one atomic input cannot contain an internal
duplicate.  One transition

* adds the phase delta in `GaugeBit = ZMod 2` (XOR);
* intersects occupancy with the write mask to detect collisions (AND); and
* unions occupancy with the write mask to update the cache (OR).

The address type is arbitrary.  Finiteness is carried by `Finset`, so the
results apply in particular to every finite Boolean address cube without
choosing a radix or a distinguished number of addresses.

The main run theorems compute both state coordinates for an arbitrary input
list.  The legality theorem is exact: a run is legal precisely when every
write mask misses the initial occupancy and the write masks are pairwise
disjoint.  No correspondence with superpermutation fragments or walks is
assumed here.
-/

namespace Coeff2

namespace Charlieplex

/-! ## States and one-step transitions -/

/-- A phase bit together with the finite set of addresses already occupied. -/
structure CacheState (Address : Type*) where
  phase : GaugeBit
  occupied : Finset Address
deriving DecidableEq

/-- A phase increment together with the finite mask written by one step. -/
structure CacheInput (Address : Type*) where
  phaseDelta : GaugeBit
  writes : Finset Address
deriving DecidableEq

variable {Address : Type*} [DecidableEq Address]

/-- The collision mask.  Membership is the Boolean AND of old occupancy and
the proposed write mask. -/
def cacheCollision (state : CacheState Address) (input : CacheInput Address) :
    Finset Address :=
  state.occupied ∩ input.writes

/-- A transition is legal exactly when its collision mask is empty. -/
def CacheLegal (state : CacheState Address) (input : CacheInput Address) : Prop :=
  cacheCollision state input = ∅

/-- Update phase by XOR and occupancy by OR.  This total transition is useful
independently of legality; `CacheLegalRun` records when it may be taken. -/
def cacheStep (state : CacheState Address) (input : CacheInput Address) :
    CacheState Address where
  phase := state.phase + input.phaseDelta
  occupied := state.occupied ∪ input.writes

@[simp]
theorem mem_cacheCollision (address : Address) (state : CacheState Address)
    (input : CacheInput Address) :
    address ∈ cacheCollision state input ↔
      address ∈ state.occupied ∧ address ∈ input.writes := by
  simp [cacheCollision]

theorem cacheLegal_iff_disjoint (state : CacheState Address)
    (input : CacheInput Address) :
    CacheLegal state input ↔ Disjoint state.occupied input.writes := by
  simpa [CacheLegal, cacheCollision] using
    (Finset.disjoint_iff_inter_eq_empty
      (s := state.occupied) (t := input.writes)).symm

@[simp]
theorem cacheStep_phase (state : CacheState Address)
    (input : CacheInput Address) :
    (cacheStep state input).phase = state.phase + input.phaseDelta := rfl

@[simp]
theorem cacheStep_occupied (state : CacheState Address)
    (input : CacheInput Address) :
    (cacheStep state input).occupied = state.occupied ∪ input.writes := rfl

@[simp]
theorem mem_cacheStep_occupied (address : Address) (state : CacheState Address)
    (input : CacheInput Address) :
    address ∈ (cacheStep state input).occupied ↔
      address ∈ state.occupied ∨ address ∈ input.writes := by
  simp [cacheStep]

/-! ## Arbitrary runs -/

/-- XOR of all phase deltas in an input list, written as the additive sum in
`GaugeBit`. -/
def cachePhaseSum (inputs : List (CacheInput Address)) : GaugeBit :=
  (inputs.map (fun input => input.phaseDelta)).sum

/-- Union of all write masks in an input list. -/
def cacheWriteUnion : List (CacheInput Address) → Finset Address
  | [] => ∅
  | input :: inputs => input.writes ∪ cacheWriteUnion inputs

/-- Execute a list of inputs from left to right. -/
def cacheRun (state : CacheState Address) :
    List (CacheInput Address) → CacheState Address
  | [] => state
  | input :: inputs => cacheRun (cacheStep state input) inputs

@[simp]
theorem cachePhaseSum_nil :
    cachePhaseSum ([] : List (CacheInput Address)) = 0 := by
  simp [cachePhaseSum]

@[simp]
theorem cachePhaseSum_cons (input : CacheInput Address)
    (inputs : List (CacheInput Address)) :
    cachePhaseSum (input :: inputs) =
      input.phaseDelta + cachePhaseSum inputs := by
  simp [cachePhaseSum]

@[simp]
theorem cacheWriteUnion_nil :
    cacheWriteUnion ([] : List (CacheInput Address)) = ∅ := rfl

@[simp]
theorem cacheWriteUnion_cons (input : CacheInput Address)
    (inputs : List (CacheInput Address)) :
    cacheWriteUnion (input :: inputs) =
      input.writes ∪ cacheWriteUnion inputs := rfl

/-- Membership in the accumulated write mask is witnessed by one input in
the run. -/
@[simp]
theorem mem_cacheWriteUnion (address : Address)
    (inputs : List (CacheInput Address)) :
    address ∈ cacheWriteUnion inputs ↔
      ∃ input ∈ inputs, address ∈ input.writes := by
  induction inputs with
  | nil => simp
  | cons input inputs ih =>
      simp [cacheWriteUnion, ih]

@[simp]
theorem cacheRun_nil (state : CacheState Address) :
    cacheRun state [] = state := rfl

@[simp]
theorem cacheRun_cons (state : CacheState Address) (input : CacheInput Address)
    (inputs : List (CacheInput Address)) :
    cacheRun state (input :: inputs) =
      cacheRun (cacheStep state input) inputs := rfl

/-- The phase after a run is the initial phase XOR all input deltas. -/
theorem cacheRun_phase (state : CacheState Address)
    (inputs : List (CacheInput Address)) :
    (cacheRun state inputs).phase =
      state.phase + cachePhaseSum inputs := by
  induction inputs generalizing state with
  | nil => simp
  | cons input inputs ih =>
      rw [cacheRun_cons, ih]
      simp only [cacheStep_phase, cachePhaseSum_cons]
      exact add_assoc _ _ _

/-- The final occupancy is the initial occupancy union every write mask. -/
theorem cacheRun_occupied (state : CacheState Address)
    (inputs : List (CacheInput Address)) :
    (cacheRun state inputs).occupied =
      state.occupied ∪ cacheWriteUnion inputs := by
  induction inputs generalizing state with
  | nil => simp
  | cons input inputs ih =>
      rw [cacheRun_cons, ih]
      simp only [cacheStep_occupied, cacheWriteUnion_cons]
      exact Finset.union_assoc _ _ _

/-! ## Legal runs and global collision freedom -/

/-- Legality checked against the evolving cache after every prefix. -/
def CacheLegalRun (state : CacheState Address) :
    List (CacheInput Address) → Prop
  | [] => True
  | input :: inputs =>
      CacheLegal state input ∧ CacheLegalRun (cacheStep state input) inputs

@[simp]
theorem cacheLegalRun_nil (state : CacheState Address) :
    CacheLegalRun state [] := by
  trivial

@[simp]
theorem cacheLegalRun_cons (state : CacheState Address)
    (input : CacheInput Address) (inputs : List (CacheInput Address)) :
    CacheLegalRun state (input :: inputs) ↔
      CacheLegal state input ∧
        CacheLegalRun (cacheStep state input) inputs :=
  Iff.rfl

/-- Every input mask in the list is disjoint from a fixed occupied set. -/
def WritesDisjointFrom (occupied : Finset Address)
    (inputs : List (CacheInput Address)) : Prop :=
  ∀ input ∈ inputs, Disjoint occupied input.writes

/-- Distinct positions in the input list carry disjoint write masks. -/
def PairwiseDisjointWrites (inputs : List (CacheInput Address)) : Prop :=
  inputs.Pairwise
    (fun left right => Disjoint left.writes right.writes)

@[simp]
theorem writesDisjointFrom_nil (occupied : Finset Address) :
    WritesDisjointFrom occupied [] := by
  simp [WritesDisjointFrom]

@[simp]
theorem writesDisjointFrom_cons (occupied : Finset Address)
    (input : CacheInput Address) (inputs : List (CacheInput Address)) :
    WritesDisjointFrom occupied (input :: inputs) ↔
      Disjoint occupied input.writes ∧
        WritesDisjointFrom occupied inputs := by
  simp [WritesDisjointFrom]

/-- Disjointness from a union is disjointness from each of its two parts,
uniformly over every input mask. -/
theorem writesDisjointFrom_union (left right : Finset Address)
    (inputs : List (CacheInput Address)) :
    WritesDisjointFrom (left ∪ right) inputs ↔
      WritesDisjointFrom left inputs ∧
        WritesDisjointFrom right inputs := by
  constructor
  · intro hall
    constructor
    · intro input hmem
      exact (Finset.disjoint_union_left.mp (hall input hmem)).1
    · intro input hmem
      exact (Finset.disjoint_union_left.mp (hall input hmem)).2
  · rintro ⟨hleft, hright⟩ input hmem
    exact Finset.disjoint_union_left.mpr
      ⟨hleft input hmem, hright input hmem⟩

@[simp]
theorem pairwiseDisjointWrites_nil :
    PairwiseDisjointWrites ([] : List (CacheInput Address)) := by
  simp [PairwiseDisjointWrites]

@[simp]
theorem pairwiseDisjointWrites_cons (input : CacheInput Address)
    (inputs : List (CacheInput Address)) :
    PairwiseDisjointWrites (input :: inputs) ↔
      WritesDisjointFrom input.writes inputs ∧
        PairwiseDisjointWrites inputs := by
  simp [PairwiseDisjointWrites, WritesDisjointFrom, List.pairwise_cons]

/-- Exact global form of prefix-by-prefix legality.  Thus the stateful test
loses no information: it is equivalent to avoiding the initial cache and to
pairwise disjointness of all write masks. -/
theorem cacheLegalRun_iff_disjointness (state : CacheState Address)
    (inputs : List (CacheInput Address)) :
    CacheLegalRun state inputs ↔
      WritesDisjointFrom state.occupied inputs ∧
        PairwiseDisjointWrites inputs := by
  induction inputs generalizing state with
  | nil => simp
  | cons input inputs ih =>
      constructor
      · intro hrun
        rw [cacheLegalRun_cons] at hrun
        rcases hrun with ⟨hhead, htail⟩
        have htailData :=
          (ih (state := cacheStep state input)).mp htail
        rcases htailData with ⟨htailInitial, htailPairwise⟩
        have htailUnion :
            WritesDisjointFrom
              (state.occupied ∪ input.writes) inputs := by
          change WritesDisjointFrom
            (state.occupied ∪ input.writes) inputs at htailInitial
          exact htailInitial
        rcases
            (writesDisjointFrom_union
              state.occupied input.writes inputs).mp htailUnion with
          ⟨htailFromInitial, htailFromHead⟩
        constructor
        · exact (writesDisjointFrom_cons
            state.occupied input inputs).mpr
            ⟨(cacheLegal_iff_disjoint state input).mp hhead,
              htailFromInitial⟩
        · exact (pairwiseDisjointWrites_cons input inputs).mpr
            ⟨htailFromHead, htailPairwise⟩
      · rintro ⟨hinitial, hpairwise⟩
        rcases (writesDisjointFrom_cons
            state.occupied input inputs).mp hinitial with
          ⟨hhead, htailFromInitial⟩
        rcases (pairwiseDisjointWrites_cons input inputs).mp hpairwise with
          ⟨htailFromHead, htailPairwise⟩
        have htailUnion :
            WritesDisjointFrom
              (state.occupied ∪ input.writes) inputs :=
          (writesDisjointFrom_union
            state.occupied input.writes inputs).mpr
            ⟨htailFromInitial, htailFromHead⟩
        rw [cacheLegalRun_cons]
        constructor
        · exact (cacheLegal_iff_disjoint state input).mpr hhead
        · apply (ih (state := cacheStep state input)).mpr
          constructor
          · change WritesDisjointFrom
              (state.occupied ∪ input.writes) inputs
            exact htailUnion
          · exact htailPairwise

/-- In a legal run no proposed write hits the initially occupied cache. -/
theorem cacheLegalRun_disjoint_initial (state : CacheState Address)
    (inputs : List (CacheInput Address)) (hrun : CacheLegalRun state inputs) :
    WritesDisjointFrom state.occupied inputs :=
  (cacheLegalRun_iff_disjointness state inputs).mp hrun |>.1

/-- Write masks at distinct run positions are disjoint in every legal run. -/
theorem cacheLegalRun_pairwise (state : CacheState Address)
    (inputs : List (CacheInput Address)) (hrun : CacheLegalRun state inputs) :
    PairwiseDisjointWrites inputs :=
  (cacheLegalRun_iff_disjointness state inputs).mp hrun |>.2

end Charlieplex

end Coeff2
