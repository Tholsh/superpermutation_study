import Coeff2.CharliePacketPorts

/-!
# Actual course-program occupation of the non-whole two-marker packet

The goal is the union of the rotation courses executed by the short and long
programs, with all order parameters symbolic. This is a local occupation
bridge, not an assertion of a cheap global attachment or a new record.
-/
namespace Coeff2.Charlieplex.PacketOccupationBridge
open Finset EganOccupationLift EganComponentGraph PacketPorts TwoMarkerPartition
variable {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
theorem insert_append (a : α) (u v : List α) (i : ℕ) (hi : i ≤ u.length) :
    (u ++ v).insertIdx i a = u.insertIdx i a ++ v := by
  induction u generalizing i with
  | nil =>
    have : i = 0 := by simpa using hi
    subst i
    rfl
  | cons x u ih =>
    cases i with
    | zero => rfl
    | succ i => simpa using congrArg (List.cons x) (ih i (by simpa using hi))

omit [DecidableEq α] in
theorem insert_end (a : α) (s : List α) : s.insertIdx s.length a = s ++ [a] := by
  induction s with
  | nil => rfl
  | cons x s ih => simp [ih]

theorem insertion_snoc (a z : α) (s : List α) :
    insertionFiber a (s ++ [z]) =
      (insertionFiber a s).image (fun q => q ++ [z]) ∪ {s ++ [z,a]} := by
  unfold insertionFiber
  simp only [List.length_append, List.length_singleton]
  rw [range_add_one, image_insert, image_image]
  have he : (range (s.length+1)).image (fun i => (s ++ [z]).insertIdx i a) =
      (range (s.length+1)).image (fun i => s.insertIdx i a ++ [z]) := by
    apply image_congr
    intro i hi
    exact insert_append a s [z] i (by have := mem_range.mp hi; omega)
  rw [he]
  have hs : (s ++ [z]).insertIdx (s.length+1) a = s ++ [z,a] := by
    simpa only [List.length_append, List.length_singleton, List.append_assoc,
      List.singleton_append] using insert_end a (s ++ [z])
  rw [hs]
  simp [Function.comp_def, union_comm]

theorem lift_union (a : α) (U V : Finset (List α)) :
    occupationLift a (U ∪ V) = occupationLift a U ∪ occupationLift a V := by
  simp [occupationLift, union_biUnion]

theorem lift_snoc (b z : α) (U : Finset (List α)) :
    occupationLift b (U.image (fun q => q ++ [z])) =
      (occupationLift b U).image (fun q => q ++ [z]) ∪
      U.image (fun q => q ++ [z,b]) := by
  unfold occupationLift
  rw [image_biUnion]
  simp only [insertion_snoc, biUnion_union]
  ext w
  simp only [mem_biUnion, mem_image, mem_union, mem_singleton]
  aesop

theorem rooted_union (y : α) (U V : Finset (List α)) :
    rootedOrbits y (U ∪ V) = rootedOrbits y U ∪ rootedOrbits y V := by
  simp [rootedOrbits, union_biUnion]

theorem prefix_segment (u v : List α) (y a : α) :
    segmentOccupation (((u ++ v) ++ [y]) ++ [a]) (u.length+1) =
      rootedOrbits y ((insertionFiber a u).image (fun q => q ++ v)) := by
  rw [segment_occupation _ y a _ (by simp)]
  unfold insertionFiber
  rw [image_image]
  congr 1
  apply image_congr
  intro i hi
  exact insert_append a u v i (by have := mem_range.mp hi; omega)

theorem segment_succ (p : List α) (k : ℕ) :
    segmentOccupation p (k+1) = rotationOrbit p ∪ segmentOccupation (nextCourse p 0) k := by
  ext w
  simp only [segmentOccupation, mem_biUnion, mem_range, mem_union]
  constructor
  · rintro ⟨i, hi, hw⟩
    cases i with
    | zero => exact Or.inl (by simpa [advance] using hw)
    | succ i => exact Or.inr ⟨i, by omega, by simpa [advance, Function.iterate_succ_apply] using hw⟩
  · rintro (hw | ⟨i, hi, hw⟩)
    · exact ⟨0, by omega, by simpa [advance] using hw⟩
    · exact ⟨i+1, by omega, by simpa [advance, Function.iterate_succ_apply] using hw⟩

theorem phase_front_segment (u : List α) (y b : α) (k : ℕ) :
    segmentOccupation ((y :: u) ++ [b]) (k+1) =
      rotationOrbit (y :: (u ++ [b])) ∪
      segmentOccupation ((u ++ [y]) ++ [b]) k := by
  rw [segment_succ, next_ordinary _ b (by simp)]
  simp [List.rotate_cons_succ, List.rotate_zero]

theorem insertion_last (a : α) (s : List α) :
    insertionFiber a s = (range s.length).image (fun i => s.insertIdx i a) ∪ {s ++ [a]} := by
  unfold insertionFiber
  rw [range_add_one, image_insert]
  simp [union_comm]

theorem front_full_segment (u : List α) (y b : α) :
    segmentOccupation ((y :: u) ++ [b]) (u.length+1) =
      rootedOrbits y (insertionFiber b u) := by
  rw [phase_front_segment, segment_occupation u y b _ (by omega), insertion_last,
    rooted_union]
  simp [rootedOrbits, union_comm]

theorem insertion_two (a z x : α) (s : List α) :
    insertionFiber a (s ++ [z,x]) =
      (insertionFiber a s).image (fun q => q ++ [z,x]) ∪
        {s ++ [z,a,x]} ∪ {s ++ [z,x,a]} := by
  rw [show s ++ [z,x] = (s ++ [z]) ++ [x] by simp,
    insertion_snoc, insertion_snoc, image_union, image_image]
  simp [List.append_assoc, Function.comp_def]

theorem catalog_two (a b z x : α) (s : List α) (hab : a ≠ b)
    (ha : a ∉ s ++ [z,x]) (hb : b ∉ s ++ [z,x]) :
    catalog a b (s ++ [z,x]) =
      (catalog a b s).image (fun q => q ++ [z,x]) ∪
      (insertionFiber a s).image (fun q => q ++ [z,b,x]) ∪
      (insertionFiber a s).image (fun q => q ++ [z,x,b]) ∪
      insertionFiber b (s ++ [z,a,x]) ∪ insertionFiber b (s ++ [z,x,a]) := by
  have has : a ∉ s := fun h => ha (by simp [h])
  have hbs : b ∉ s := fun h => hb (by simp [h])
  rw [catalog_comm a b _ hab ha hb, catalog_eq_lift, insertion_two,
    lift_union, lift_union]
  have he : (insertionFiber a s).image (fun q => q ++ [z,x]) =
      ((insertionFiber a s).image (fun q => q ++ [z])).image (fun q => q ++ [x]) := by
    simp [image_image, Function.comp_def, List.append_assoc]
  rw [he, lift_snoc, lift_snoc, image_union, image_image, image_image, image_image]
  rw [← catalog_eq_lift, catalog_comm b a s hab.symm hbs has]
  simp [occupationLift, Function.comp_def, List.append_assoc, union_assoc]

def shortCourses (s : List α) (z x y a b : α) : Finset (List α) :=
  (range (s.length+1)).biUnion (fun i =>
    segmentOccupation (s.insertIdx i b ++ [z,x,y,a]) (s.length+2))

def longACourses (s : List α) (z x y a b : α) : Finset (List α) :=
  segmentOccupation (s ++ [z,b,x,y,a]) (s.length+2) ∪
    segmentOccupation (nextCourse (advance (s ++ [z,b,x,y,a]) (s.length+1)) 1) (s.length+3)

def longBCourses (s : List α) (z x y a b : α) : Finset (List α) :=
  segmentOccupation (y :: (s ++ [z,x,a,b])) (s.length+4) ∪
    segmentOccupation (nextCourse (advance (y :: (s ++ [z,x,a,b])) (s.length+3)) 1) (s.length+1)

def packetCourses (s : List α) (z x y a b : α) : Finset (List α) :=
  shortCourses s z x y a b ∪ longACourses s z x y a b ∪ longBCourses s z x y a b

omit [DecidableEq α] in
theorem longA_restart (s : List α) (z x y a b : α) :
    nextCourse (advance (s ++ [z,b,x,y,a]) (s.length+1)) 1 =
      (y :: (s ++ [z,a,x])) ++ [b] := by
  have he : s ++ [z,b,x,y,a] = ((s ++ [z]) ++ [b,x,y]) ++ [a] := by simp
  rw [he, advance_ordinary _ a (by simp)]
  rw [show s.length+1 = (s ++ [z]).length by simp, List.rotate_append_length_eq]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [extra_bridge]
  simp

omit [DecidableEq α] in
theorem longB_restart (s : List α) (z x y a b : α) :
    nextCourse (advance (y :: (s ++ [z,x,a,b])) (s.length+3)) 1 =
      (s ++ [z,x,b,y]) ++ [a] := by
  have he : y :: (s ++ [z,x,a,b]) = ((y :: (s ++ [z,x])) ++ [a]) ++ [b] := by simp
  rw [he, advance_ordinary _ b (by simp)]
  rw [show s.length+3 = (y :: (s ++ [z,x])).length by simp, List.rotate_append_length_eq]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [extra_bridge]
  simp

theorem short_courses_roots (s : List α) (z x y a b : α) :
    shortCourses s z x y a b =
      rootedOrbits y ((catalog a b s).image (fun q => q ++ [z,x])) := by
  have hs : ∀ i ∈ range (s.length+1),
      segmentOccupation (s.insertIdx i b ++ [z,x,y,a]) (s.length+2) =
        rootedOrbits y ((insertionFiber a (s.insertIdx i b)).image (fun q => q ++ [z,x])) := by
    intro i hi
    have hl := List.length_insertIdx_of_le_length (a := b) (by have := mem_range.mp hi; omega : i ≤ s.length)
    simpa [hl, List.append_assoc] using prefix_segment (s.insertIdx i b) [z,x] y a
  unfold shortCourses
  rw [biUnion_congr rfl hs]
  ext w
  simp only [catalog, row, rootedOrbits, mem_biUnion, mem_image]
  aesop

theorem longA_courses_roots (s : List α) (z x y a b : α) :
    longACourses s z x y a b = rootedOrbits y
      ((insertionFiber a s).image (fun q => q ++ [z,b,x]) ∪
        insertionFiber b (s ++ [z,a,x])) := by
  unfold longACourses
  rw [longA_restart]
  have hp : segmentOccupation (s ++ [z,b,x,y,a]) (s.length+2) =
      rootedOrbits y ((insertionFiber a (s ++ [z])).image (fun q => q ++ [b,x])) := by
    simpa [List.append_assoc, Nat.add_assoc] using prefix_segment (s ++ [z]) [b,x] y a
  have hq : segmentOccupation ((s ++ [z,a,x]) ++ [y] ++ [b]) (s.length+2) =
      rootedOrbits y ((insertionFiber b (s ++ [z])).image (fun q => q ++ [a,x])) := by
    simpa [List.append_assoc, Nat.add_assoc] using prefix_segment (s ++ [z]) [a,x] y b
  rw [hp, show s.length+3 = (s.length+2)+1 by omega, phase_front_segment]
  rw [hq]
  have ha : (insertionFiber a (s ++ [z])).image (fun q => q ++ [b,x]) =
      (insertionFiber a s).image (fun q => q ++ [z,b,x]) ∪ {s ++ [z,a,b,x]} := by
    rw [insertion_snoc, image_union, image_image]
    simp [Function.comp_def, List.append_assoc]
  have hc : insertionFiber b (s ++ [z,a,x]) =
      (insertionFiber b (s ++ [z])).image (fun q => q ++ [a,x]) ∪
        {s ++ [z,a,b,x]} ∪ {s ++ [z,a,x,b]} := by
    simpa [List.append_assoc] using insertion_two b a x (s ++ [z])
  rw [ha, hc]
  simp only [rooted_union]
  simp only [rootedOrbits, singleton_biUnion]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  ac_rfl

theorem longB_courses_roots (s : List α) (z x y a b : α) :
    longBCourses s z x y a b = rootedOrbits y
      (insertionFiber b (s ++ [z,x,a]) ∪
        (insertionFiber a s).image (fun q => q ++ [z,x,b])) := by
  unfold longBCourses
  rw [longB_restart]
  have hp : segmentOccupation (y :: (s ++ [z,x,a,b])) (s.length+4) =
      rootedOrbits y (insertionFiber b (s ++ [z,x,a])) := by
    simpa [List.append_assoc, Nat.add_assoc] using front_full_segment (s ++ [z,x,a]) y b
  have hq : segmentOccupation ((s ++ [z,x,b,y]) ++ [a]) (s.length+1) =
      rootedOrbits y ((insertionFiber a s).image (fun q => q ++ [z,x,b])) := by
    simpa [List.append_assoc] using prefix_segment s [z,x,b] y a
  rw [hp, hq, rooted_union]

/-- The actual short/long course programs cover exactly the ordinary catalog,
not merely the same number of cycles. All prefix lengths are symbolic. -/
theorem packet_courses_catalog (s : List α) (z x y a b : α) (hab : a ≠ b)
    (ha : a ∉ s ++ [z,x]) (hb : b ∉ s ++ [z,x]) :
    packetCourses s z x y a b = rootedOrbits y (catalog a b (s ++ [z,x])) := by
  rw [packetCourses, short_courses_roots, longA_courses_roots, longB_courses_roots,
    ← rooted_union, ← rooted_union, catalog_two a b z x s hab ha hb]
  congr 1
  ac_rfl

/-- Complete local occupation of the literal double-insertion fiber. This
connects the executed course programs to the pre-existing all-order partition. -/
theorem packet_courses_fiber (s : List α) (z x y a b : α)
    (ht : (y :: (s ++ [z,x])).Nodup)
    (ha : a ∉ y :: (s ++ [z,x])) (hb : b ∉ y :: (s ++ [z,x])) (hab : a ≠ b) :
    packetCourses s z x y a b =
      occupationLift a (occupationLift b (rotationOrbit (y :: (s ++ [z,x])))) := by
  rw [packet_courses_catalog s z x y a b hab
    (fun h => ha (by simp [h])) (fun h => hb (by simp [h]))]
  exact rooted_catalog y a b _ ht ha hb hab

theorem packet_courses_card (s : List α) (z x y a b : α)
    (ht : (y :: (s ++ [z,x])).Nodup)
    (ha : a ∉ y :: (s ++ [z,x])) (hb : b ∉ y :: (s ++ [z,x])) (hab : a ≠ b) :
    (packetCourses s z x y a b).card = (s.length+3)*(s.length+4)*(s.length+5) := by
  rw [packet_courses_catalog s z x y a b hab
    (fun h => ha (by simp [h])) (fun h => hb (by simp [h])),
    rooted_catalog_card y a b _ ht ha hb hab]
  simp [Nat.add_assoc]

/-- Select the last two symbols as the local clocks. At the two tiny base
orders where there are no such symbols, retain the ordinary catalog. -/
def exchangedTail (y a b : α) (t : List α) : Finset (List α) :=
  match t.reverse with
  | x :: z :: rs => packetCourses rs.reverse z x y a b
  | _ => rootedOrbits y (catalog a b t)

theorem exchangedTail_eq (y a b : α) (t : List α) (hab : a ≠ b)
    (ha : a ∉ t) (hb : b ∉ t) :
    exchangedTail y a b t = rootedOrbits y (catalog a b t) := by
  cases hr : t.reverse with
  | nil => simp [exchangedTail, hr]
  | cons x rest =>
    cases rest with
    | nil => simp [exchangedTail, hr]
    | cons z rs =>
      have ht : t = rs.reverse ++ [z,x] := by
        have he := congrArg List.reverse hr
        simpa [List.reverse_cons, List.append_assoc] using he
      simp only [exchangedTail, hr]
      rw [ht] at ha hb ⊢
      exact packet_courses_catalog _ z x y a b hab ha hb

/-- Arbitrary per-parent choices of the executed exchange program preserve
the entire permutation universe for every alphabet size. No packing search,
regular selection pattern, or cardinality-to-coverage inference is used.
This is occupation of a family of course programs; short global assembly is
deliberately not asserted. -/
theorem global_course_occupation (y a b : α) (A : List α)
    (hA : (y :: A).Nodup) (ha : a ∉ y :: A) (hb : b ∉ y :: A) (hab : a ≠ b)
    (select : List α → Bool) :
    A.permutations.toFinset.biUnion (fun t =>
      if select t then exchangedTail y a b t else rootedOrbits y (catalog a b t)) =
        (a :: b :: y :: A).permutations.toFinset := by
  calc
    _ = A.permutations.toFinset.biUnion (fun t => rootedOrbits y (catalog a b t)) := by
      apply biUnion_congr rfl
      intro t ht
      have hp := List.mem_permutations.mp (List.mem_toFinset.mp ht)
      have hat : a ∉ t := fun h => ha (by simp [hp.subset h])
      have hbt : b ∉ t := fun h => hb (by simp [hp.subset h])
      rw [exchangedTail_eq y a b t hab hat hbt]
      split <;> rfl
    _ = _ := by
      simpa only [plannedRoots, Bool.false_eq_true, if_false] using
        global_planned_occupation y a b A hA ha hb hab (fun _ => false)
          (fun _ => 0) (fun _ => 0) (by simp) (by simp)

#print axioms prefix_segment
#print axioms front_full_segment
#print axioms catalog_two
#print axioms short_courses_roots
#print axioms longA_courses_roots
#print axioms longB_courses_roots
#print axioms packet_courses_catalog
#print axioms packet_courses_fiber
#print axioms packet_courses_card
#print axioms exchangedTail_eq
#print axioms global_course_occupation
end Coeff2.Charlieplex.PacketOccupationBridge
