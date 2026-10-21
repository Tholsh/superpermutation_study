import Coeff2.CharlieEganProcedure

/-!
# Literal intersections in Egan's component graph

Pointing every outer rotation at a common fresh symbol reduces a marked
component to an ordinary insertion fiber. No graph-shape hypothesis is
used to derive the possible intersections.
-/

namespace Coeff2.Charlieplex.EganComponentGraph
open EganOccupationLift Finset
variable {α : Type*} [DecidableEq α]

def rootedOrbits (z : α) (U : Finset (List α)) : Finset (List α) :=
  U.biUnion (fun p => rotationOrbit (z :: p))

theorem component_rooted (z h : α) (t : List α)
    (ht : (z :: t).Nodup) (hh : h ∉ z :: t) :
    markedCycle h (z :: t) = rootedOrbits z (insertionFiber h t) :=
  rotationOrbit_lift_refinement h z t ht hh

theorem rootedOrbits_inter (z : α) (U V : Finset (List α))
    (hU : ∀ p ∈ U, (z :: p).Nodup) :
    rootedOrbits z U ∩ rootedOrbits z V = rootedOrbits z (U ∩ V) := by
  ext w
  simp only [rootedOrbits, mem_inter, mem_biUnion]
  constructor
  · rintro ⟨⟨p, hp, hwp⟩, ⟨q, hq, hwq⟩⟩
    have he : p = q := pointed_cycle_unique (hU p hp)
      ((mem_rotationOrbit.mp hwp).symm.trans (mem_rotationOrbit.mp hwq))
    subst q
    exact ⟨p, ⟨hp, hq⟩, hwp⟩
  · rintro ⟨p, ⟨hp, hq⟩, hw⟩
    exact ⟨⟨p, hp, hw⟩, ⟨p, hq, hw⟩⟩

theorem component_intersection (z h k : α) (t u : List α)
    (ht : (z :: t).Nodup) (hu : (z :: u).Nodup)
    (hh : h ∉ z :: t) (hk : k ∉ z :: u) :
    markedCycle h (z :: t) ∩ markedCycle k (z :: u) =
      rootedOrbits z (insertionFiber h t ∩ insertionFiber k u) := by
  rw [component_rooted z h t ht hh, component_rooted z k u hu hk]
  apply rootedOrbits_inter
  intro p hp
  have hzt := (List.nodup_cons.mp ht).1
  have hhz : h ≠ z := fun he => hh (by simp [he])
  have hht : h ∉ t := fun he => hh (by simp [he])
  exact ((insertionFiber_perm hp).cons z).nodup_iff.mpr (by
    simp only [List.nodup_cons]
    exact ⟨by simp [hhz.symm, hzt], hht, (List.nodup_cons.mp ht).2⟩)

/-- With unequal surviving first symbols, every common literal root must
start with one of the two deleted markers. -/
theorem common_root_two_candidates (h k r s : α) (t u w : List α)
    (hh : h ∉ r :: t) (hk : k ∉ s :: u) (hrs : r ≠ s)
    (hw : w ∈ insertionFiber h (r :: t) ∩ insertionFiber k (s :: u)) :
    w = h :: r :: t ∨ w = k :: s :: u := by
  obtain ⟨hw1, hw2⟩ := mem_inter.mp hw
  obtain ⟨_, he1⟩ := (mem_insertionFiber_iff h _ w hh).mp hw1
  obtain ⟨_, he2⟩ := (mem_insertionFiber_iff k _ w hk).mp hw2
  cases w with
  | nil => simp at he1
  | cons a w =>
    by_cases hah : a = h
    · subst a; simp only [List.erase_cons_head] at he1
      exact Or.inl (congrArg (List.cons h) he1)
    by_cases hak : a = k
    · subst a; simp only [List.erase_cons_head] at he2
      exact Or.inr (congrArg (List.cons k) he2)
    rw [List.erase_cons_tail (by simpa using hah)] at he1
    rw [List.erase_cons_tail (by simpa using hak)] at he2
    exact False.elim (hrs ((List.cons.inj he1).1.symm.trans (List.cons.inj he2).1))

/-- Exact finite intersection, with at most two explicitly named roots. -/
theorem fiber_intersection_two_candidates (h k r s : α) (t u : List α)
    (hh : h ∉ r :: t) (hk : k ∉ s :: u) (hrs : r ≠ s) :
    insertionFiber h (r :: t) ∩ insertionFiber k (s :: u) =
      ({h :: r :: t, k :: s :: u} : Finset (List α)).filter
        (fun w => w ∈ insertionFiber h (r :: t) ∩ insertionFiber k (s :: u)) := by
  ext w
  simp only [mem_filter, mem_insert, mem_singleton]
  exact ⟨fun hw => ⟨common_root_two_candidates h k r s t u w hh hk hrs hw, hw⟩,
    fun hw => hw.2⟩

/-- Moving the new held symbol to the front is the literal parent update. -/
def promote (k : α) (p : List α) : List α := k :: p.erase k

theorem promote_perm (k : α) (p : List α) (hk : k ∈ p) :
    (promote k p).Perm p := (List.perm_cons_erase hk).symm

theorem first_candidate_iff (h k : α) (t u : List α)
    (hh : h ∉ t) (hk : k ∉ u) (hhk : h ≠ k) :
    h :: t ∈ insertionFiber h t ∩ insertionFiber k u ↔
      k ∈ t ∧ promote k (h :: t) = k :: u := by
  rw [mem_inter, mem_insertionFiber_iff h t _ hh,
    mem_insertionFiber_iff k u _ hk]
  simp [promote, hhk, Ne.symm hhk]

/-- A candidate intersection forces the parent marker's predecessor. -/
theorem first_candidate_predecessor (h k r s : α) (t u : List α)
    (hk : k ∉ s :: u) (hhk : h ≠ k)
    (hw : h :: r :: t ∈ insertionFiber k (s :: u)) : s = h := by
  have he := ((mem_insertionFiber_iff k _ _ hk).mp hw).2
  rw [List.erase_cons_tail (by simpa using hhk)] at he
  exact (List.cons.inj he).1.symm

/-- Excluding a predecessor 2-cycle rules out two common rotation roots. -/
theorem fiber_intersection_at_most_one (h k r s : α) (t u : List α)
    (hh : h ∉ r :: t) (hk : k ∉ s :: u) (hhk : h ≠ k)
    (hrs : r ≠ s) (hno : ¬ (r = k ∧ s = h)) :
    (insertionFiber h (r :: t) ∩ insertionFiber k (s :: u)).card ≤ 1 := by
  apply card_le_one.mpr
  intro p hp q hq
  rcases common_root_two_candidates h k r s t u p hh hk hrs hp with rfl | rfl
  · rcases common_root_two_candidates h k r s t u q hh hk hrs hq with rfl | rfl
    · rfl
    · exact False.elim (hno ⟨first_candidate_predecessor k h s r u t hh hhk.symm (mem_inter.mp hq).1,
        first_candidate_predecessor h k r s t u hk hhk (mem_inter.mp hp).2⟩)
  · rcases common_root_two_candidates h k r s t u q hh hk hrs hq with rfl | rfl
    · exact False.elim (hno ⟨first_candidate_predecessor k h s r u t hh hhk.symm (mem_inter.mp hp).1,
        first_candidate_predecessor h k r s t u hk hhk (mem_inter.mp hq).2⟩)
    · rfl

theorem rootedOrbits_nonempty (z : α) (U : Finset (List α)) :
    (rootedOrbits z U).Nonempty ↔ U.Nonempty := by
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨p, hp, _⟩ := mem_biUnion.mp hw
    exact ⟨p, hp⟩
  · rintro ⟨p, hp⟩
    exact ⟨z :: p, mem_biUnion.mpr ⟨p, hp, mem_rotationOrbit.mpr (List.IsRotated.refl _)⟩⟩

theorem fiber_adjacent_iff_promote (h k r s : α) (t u : List α)
    (hh : h ∉ r :: t) (hk : k ∉ s :: u) (hhk : h ≠ k) (hrs : r ≠ s) :
    (insertionFiber h (r :: t) ∩ insertionFiber k (s :: u)).Nonempty ↔
      (k ∈ r :: t ∧ promote k (h :: r :: t) = k :: s :: u) ∨
      (h ∈ s :: u ∧ promote h (k :: s :: u) = h :: r :: t) := by
  constructor
  · rintro ⟨w, hw⟩
    rcases common_root_two_candidates h k r s t u w hh hk hrs hw with rfl | rfl
    · exact Or.inl ((first_candidate_iff h k _ _ hh hk hhk).mp hw)
    · exact Or.inr ((first_candidate_iff k h _ _ hk hh hhk.symm).mp (mem_inter.mpr
        ⟨(mem_inter.mp hw).2, (mem_inter.mp hw).1⟩))
  · rintro (hleft | hright)
    · exact ⟨h :: r :: t, (first_candidate_iff h k _ _ hh hk hhk).mpr hleft⟩
    · have hw := (first_candidate_iff k h _ _ hk hh hhk.symm).mpr hright
      exact ⟨k :: s :: u, mem_inter.mpr ⟨(mem_inter.mp hw).2, (mem_inter.mp hw).1⟩⟩

def oldPred (M h : ℕ) : ℕ := if h = 1 then M else h-1
def oldNext (M h : ℕ) : ℕ := if h = M then 1 else h+1

theorem oldPred_eq_egan (M h : ℕ) : oldPred M h = EganProcedure.predecessor (M+1) h := by
  simp [oldPred, EganProcedure.predecessor]

theorem oldPred_injective (M h k : ℕ) (hh : 1 ≤ h ∧ h ≤ M)
    (hk : 1 ≤ k ∧ k ≤ M) (he : oldPred M h = oldPred M k) : h = k := by
  unfold oldPred at he
  split at he <;> split at he <;> omega

theorem oldPred_no_two_cycle (M h k : ℕ) (hM : 3 ≤ M)
    (hh : 1 ≤ h ∧ h ≤ M) (hk : 1 ≤ k ∧ k ≤ M) :
    ¬ (oldPred M h = k ∧ oldPred M k = h) := by
  unfold oldPred
  split <;> split <;> omega

theorem oldPred_eq_iff_next (M h k : ℕ) (hh : 1 ≤ h ∧ h ≤ M)
    (hk : 1 ≤ k ∧ k ≤ M) : oldPred M k = h ↔ k = oldNext M h := by
  unfold oldPred oldNext
  split <;> split <;> omega

/-- The old-letter representation of a selected Egan component. The
largest symbol M+1 is understood to sit immediately after the held symbol. -/
def IsNode (M h : ℕ) (t : List ℕ) : Prop :=
  (h :: oldPred M h :: t).Perm (List.range' 1 M)

theorem node_bounds (M h : ℕ) (t : List ℕ) (hp : IsNode M h t) : 1 ≤ h ∧ h ≤ M := by
  have hh := List.mem_range'_1.mp (hp.mem_iff.mp (by simp : h ∈ h :: oldPred M h :: t))
  omega

theorem node_nodup (M h : ℕ) (t : List ℕ) (hp : IsNode M h t) :
    (h :: oldPred M h :: t).Nodup := hp.nodup_iff.mpr List.nodup_range'

theorem node_fresh (M h : ℕ) (t : List ℕ) (hp : IsNode M h t) :
    M+1 ∉ h :: oldPred M h :: t := by
  intro hm
  have hh := List.mem_range'_1.mp (hp.mem_iff.mp hm)
  omega

def parentWord (M : ℕ) : List ℕ → List ℕ
  | [] => []
  | h :: t => promote (oldNext M h) (h :: t)

/-- All literal component intersections are precisely parent/child edges.
No extra graph edge is discarded or declared inadmissible. -/
theorem egan_component_adjacent_iff_parent (M h k : ℕ) (t u : List ℕ)
    (hp : IsNode M h t) (hq : IsNode M k u) (hhk : h ≠ k) :
    (markedCycle h ((M+1) :: oldPred M h :: t) ∩
      markedCycle k ((M+1) :: oldPred M k :: u)).Nonempty ↔
      parentWord M (h :: oldPred M h :: t) = k :: oldPred M k :: u ∨
      parentWord M (k :: oldPred M k :: u) = h :: oldPred M h :: t := by
  have hn1 := node_nodup M h t hp
  have hn2 := node_nodup M k u hq
  have hb1 := node_bounds M h t hp
  have hb2 := node_bounds M k u hq
  have hf1 := node_fresh M h t hp
  have hf2 := node_fresh M k u hq
  have hh := (List.nodup_cons.mp hn1).1
  have hk := (List.nodup_cons.mp hn2).1
  have hz1 : ((M+1) :: oldPred M h :: t).Nodup :=
    List.nodup_cons.mpr ⟨fun hm => hf1 (by simp [hm]), (List.nodup_cons.mp hn1).2⟩
  have hz2 : ((M+1) :: oldPred M k :: u).Nodup :=
    List.nodup_cons.mpr ⟨fun hm => hf2 (by simp [hm]), (List.nodup_cons.mp hn2).2⟩
  have hh' : h ∉ (M+1) :: oldPred M h :: t := by
    simp only [List.mem_cons, not_or]
    exact ⟨by omega, by simpa using hh⟩
  have hk' : k ∉ (M+1) :: oldPred M k :: u := by
    simp only [List.mem_cons, not_or]
    exact ⟨by omega, by simpa using hk⟩
  rw [component_intersection (M+1) h k _ _ hz1 hz2 hh' hk', rootedOrbits_nonempty,
    fiber_adjacent_iff_promote h k _ _ t u hh hk hhk
      (fun he => hhk (oldPred_injective M h k hb1 hb2 he))]
  constructor
  · rintro (⟨hm, he⟩ | ⟨hm, he⟩)
    · have hc := (first_candidate_iff h k _ _ hh hk hhk).mpr ⟨hm, he⟩
      have hr := first_candidate_predecessor h k _ _ t u hk hhk (mem_inter.mp hc).2
      have hn := (oldPred_eq_iff_next M h k hb1 hb2).mp hr
      exact Or.inl (by simpa only [parentWord, ← hn] using he)
    · have hc := (first_candidate_iff k h _ _ hk hh hhk.symm).mpr ⟨hm, he⟩
      have hr := first_candidate_predecessor k h _ _ u t hh hhk.symm (mem_inter.mp hc).2
      have hn := (oldPred_eq_iff_next M k h hb2 hb1).mp hr
      exact Or.inr (by simpa only [parentWord, ← hn] using he)
  · rintro (he | he)
    · have hn : oldNext M h = k := (List.cons.inj he).1
      have hm : k ∈ oldPred M h :: t := by
        have hm := hp.mem_iff.mpr (List.mem_range'_1.mpr (by omega : 1 ≤ k ∧ k < 1+M))
        exact (List.mem_cons.mp hm).resolve_left (Ne.symm hhk)
      exact Or.inl ⟨hm, by simpa only [parentWord, hn] using he⟩
    · have hn : oldNext M k = h := (List.cons.inj he).1
      have hm : h ∈ oldPred M k :: u := by
        have hm := hq.mem_iff.mpr (List.mem_range'_1.mpr (by omega : 1 ≤ h ∧ h < 1+M))
        exact (List.mem_cons.mp hm).resolve_left hhk
      exact Or.inr ⟨hm, by simpa only [parentWord, hn] using he⟩

theorem oldNext_bounds (M h : ℕ) (hh : 1 ≤ h ∧ h ≤ M) :
    1 ≤ oldNext M h ∧ oldNext M h ≤ M := by
  unfold oldNext
  split <;> omega

theorem oldNext_ne (M h : ℕ) (hM : 2 ≤ M) (_hh : 1 ≤ h ∧ h ≤ M) :
    oldNext M h ≠ h := by
  unfold oldNext
  split <;> omega

theorem parent_node (M h : ℕ) (t : List ℕ) (hM : 2 ≤ M) (hp : IsNode M h t) :
    IsNode M (oldNext M h) ((oldPred M h :: t).erase (oldNext M h)) ∧
      parentWord M (h :: oldPred M h :: t) =
        oldNext M h :: oldPred M (oldNext M h) :: ((oldPred M h :: t).erase (oldNext M h)) := by
  have hb := node_bounds M h t hp
  have hn := oldNext_bounds M h hb
  have hne := oldNext_ne M h hM hb
  have hpred := (oldPred_eq_iff_next M h (oldNext M h) hb hn).mpr rfl
  have hm : oldNext M h ∈ h :: oldPred M h :: t :=
    hp.mem_iff.mpr (List.mem_range'_1.mpr (by omega))
  have he : parentWord M (h :: oldPred M h :: t) =
      oldNext M h :: oldPred M (oldNext M h) :: ((oldPred M h :: t).erase (oldNext M h)) := by
    simp [parentWord, promote, hpred, hne.symm]
  refine ⟨?_, he⟩
  have hperm := (promote_perm (oldNext M h) _ hm).trans hp
  unfold IsNode
  rw [← he]
  exact hperm

theorem rootedOrbits_card (z : α) (U : Finset (List α))
    (hU : ∀ p ∈ U, (z :: p).Nodup) :
    (rootedOrbits z U).card = ∑ p ∈ U, (p.length+1) := by
  rw [rootedOrbits, card_biUnion]
  · apply sum_congr rfl
    intro p hp
    simpa using rotationOrbit_card (z :: p) (hU p hp) (by simp)
  · intro p hp q _ hpq
    apply disjoint_left.mpr
    intro w hwp hwq
    exact hpq (pointed_cycle_unique (hU p hp)
      ((mem_rotationOrbit.mp hwp).symm.trans (mem_rotationOrbit.mp hwq)))

/-- A selected contact is exactly one full outer rotation orbit, never a
fractional overlap or two shared orbits (N=M+1 >= 4). -/
theorem selected_overlap_card (M h k : ℕ) (t u : List ℕ) (hM : 3 ≤ M)
    (hp : IsNode M h t) (hq : IsNode M k u) (hhk : h ≠ k) :
    (markedCycle h ((M+1) :: oldPred M h :: t) ∩
      markedCycle k ((M+1) :: oldPred M k :: u)).card = 0 ∨
    (markedCycle h ((M+1) :: oldPred M h :: t) ∩
      markedCycle k ((M+1) :: oldPred M k :: u)).card = M+1 := by
  have hn1 := node_nodup M h t hp
  have hn2 := node_nodup M k u hq
  have hb1 := node_bounds M h t hp
  have hb2 := node_bounds M k u hq
  have hf1 := node_fresh M h t hp
  have hf2 := node_fresh M k u hq
  have hh := (List.nodup_cons.mp hn1).1
  have hk := (List.nodup_cons.mp hn2).1
  have hz1 : ((M+1) :: oldPred M h :: t).Nodup :=
    List.nodup_cons.mpr ⟨fun hm => hf1 (by simp [hm]), (List.nodup_cons.mp hn1).2⟩
  have hz2 : ((M+1) :: oldPred M k :: u).Nodup :=
    List.nodup_cons.mpr ⟨fun hm => hf2 (by simp [hm]), (List.nodup_cons.mp hn2).2⟩
  have hh' : h ∉ (M+1) :: oldPred M h :: t := by simp only [List.mem_cons, not_or]; exact ⟨by omega, by simpa using hh⟩
  have hk' : k ∉ (M+1) :: oldPred M k :: u := by simp only [List.mem_cons, not_or]; exact ⟨by omega, by simpa using hk⟩
  rw [component_intersection (M+1) h k _ _ hz1 hz2 hh' hk']
  let S := insertionFiber h (oldPred M h :: t) ∩ insertionFiber k (oldPred M k :: u)
  have hcard : S.card ≤ 1 := fiber_intersection_at_most_one h k _ _ t u hh hk hhk
    (fun he => hhk (oldPred_injective M h k hb1 hb2 he)) (oldPred_no_two_cycle M h k hM hb1 hb2)
  have huniform : ∀ p ∈ S, p.length+1 = M+1 := by
    intro p hpS
    have hhperm := (insertionFiber_perm (mem_inter.mp hpS).1).trans hp
    simpa using hhperm.length_eq
  have hnd : ∀ p ∈ S, ((M+1) :: p).Nodup := by
    intro p hpS
    have hhperm := (insertionFiber_perm (mem_inter.mp hpS).1).trans hp
    apply List.nodup_cons.mpr
    refine ⟨?_, hhperm.nodup_iff.mpr List.nodup_range'⟩
    intro hm
    have hb := List.mem_range'_1.mp (hhperm.mem_iff.mp hm)
    omega
  change (rootedOrbits (M+1) S).card = 0 ∨ (rootedOrbits (M+1) S).card = M+1
  rw [rootedOrbits_card _ _ hnd, sum_const_nat huniform]
  have hs : S.card = 0 ∨ S.card = 1 := by omega
  rcases hs with hs | hs <;> simp [hs]

theorem same_held_components_disjoint (z h : α) (t u : List α)
    (ht : (z :: t).Nodup) (hu : (z :: u).Nodup)
    (hh : h ∉ z :: t) (hk : h ∉ z :: u) (hne : t ≠ u) :
    Disjoint (markedCycle h (z :: t)) (markedCycle h (z :: u)) := by
  apply disjoint_iff_inter_eq_empty.mpr
  rw [component_intersection z h h t u ht hu hh hk]
  have hf := insertionFiber_disjoint h (fun hm => hh (by simp [hm]))
    (fun hm => hk (by simp [hm])) hne
  rw [disjoint_iff_inter_eq_empty.mp hf]
  simp [rootedOrbits]

end Coeff2.Charlieplex.EganComponentGraph
