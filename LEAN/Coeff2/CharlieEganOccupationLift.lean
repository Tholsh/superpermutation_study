import Mathlib.Data.List.Lemmas
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.Rotate
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Literal occupation under insertion of a fresh symbol

This module enumerates actual lists, not an assumed graph or abstract cover.
`insertionFiber z p` inserts the new symbol at every position of `p`.
`occupationLift` takes the disjoint union of these literal fibers.

The permutation-universe theorem links this enumeration to all permutations
of the enlarged alphabet. The overlap theorem retains exact occupation, not
just coverage counts. It is a module for a procedural lift, not a claim that
arbitrary lifted pieces already have cheap compatible entry/exit ports.
-/

namespace Coeff2.Charlieplex.EganOccupationLift

open Finset
variable {α : Type*} [DecidableEq α]

def insertionFiber (z : α) (p : List α) : Finset (List α) :=
  (range (p.length + 1)).image (fun i => p.insertIdx i z)

theorem mem_insertionFiber {z : α} {p w : List α} :
    w ∈ insertionFiber z p ↔ ∃ i ≤ p.length, p.insertIdx i z = w := by
  simp [insertionFiber, Nat.lt_succ_iff]

theorem erase_insertIdx (z : α) (p : List α) (hz : z ∉ p)
    (i : ℕ) (hi : i ≤ p.length) : (p.insertIdx i z).erase z = p := by
  induction p generalizing i with
  | nil => have : i = 0 := Nat.eq_zero_of_le_zero hi; subst i; simp
  | cons a p ih =>
    have ha : z ≠ a := fun he => hz (by simp [he])
    have hp : z ∉ p := fun h => hz (List.mem_cons_of_mem a h)
    cases i with
    | zero => simp
    | succ i =>
      simp only [List.insertIdx_succ_cons]
      rw [List.erase_cons_tail (by simpa using ha.symm), ih hp i (Nat.le_of_succ_le_succ hi)]

/-- No position is guessed or discarded: this is the complete deletion fiber. -/
theorem mem_insertionFiber_iff (z : α) (p w : List α) (hz : z ∉ p) :
    w ∈ insertionFiber z p ↔ z ∈ w ∧ w.erase z = p := by
  constructor
  · rintro h
    obtain ⟨i, hi, rfl⟩ := mem_insertionFiber.mp h
    exact ⟨(List.mem_insertIdx hi).mpr (Or.inl rfl), erase_insertIdx z p hz i hi⟩
  · rintro ⟨hzw, he⟩
    obtain ⟨s, t, _, hw, hd⟩ := List.exists_erase_eq hzw
    have hp : p = s ++ t := he.symm.trans hd
    apply mem_insertionFiber.mpr
    refine ⟨s.length, ?_, ?_⟩
    · simp [hp]
    · rw [hp, hw]
      have hins : ∀ s : List α, (s ++ t).insertIdx s.length z = s ++ z :: t := by
        intro s
        induction s with
        | nil => rfl
        | cons a s ih => simpa using congrArg (List.cons a) ih
      exact hins s

theorem insertionFiber_card (z : α) (p : List α) (hz : z ∉ p) :
    (insertionFiber z p).card = p.length + 1 := by
  rw [insertionFiber, card_image_of_injOn]
  · exact card_range _
  · intro i hi j hj hij
    exact List.injOn_insertIdx_index_of_notMem p z hz
      (Nat.le_of_lt_succ (mem_range.mp hi)) (Nat.le_of_lt_succ (mem_range.mp hj)) hij

theorem insertionFiber_disjoint (z : α) {p q : List α}
    (hp : z ∉ p) (hq : z ∉ q) (hne : p ≠ q) :
    Disjoint (insertionFiber z p) (insertionFiber z q) := by
  apply disjoint_left.mpr
  intro w hw hv
  exact hne (((mem_insertionFiber_iff z p w hp).mp hw).2.symm.trans
    ((mem_insertionFiber_iff z q w hq).mp hv).2)

def occupationLift (z : α) (U : Finset (List α)) : Finset (List α) :=
  U.biUnion (insertionFiber z)

theorem mem_occupationLift (z : α) (U : Finset (List α)) (w : List α)
    (hz : ∀ p ∈ U, z ∉ p) :
    w ∈ occupationLift z U ↔ z ∈ w ∧ w.erase z ∈ U := by
  simp only [occupationLift, mem_biUnion]
  constructor
  · rintro ⟨p, hp, hw⟩
    obtain ⟨ha, he⟩ := (mem_insertionFiber_iff z p w (hz p hp)).mp hw
    exact ⟨ha, he.symm ▸ hp⟩
  · rintro ⟨ha, hp⟩
    exact ⟨w.erase z, hp, (mem_insertionFiber_iff z _ w (hz _ hp)).mpr ⟨ha, rfl⟩⟩

theorem occupationLift_card (z : α) (U : Finset (List α))
    (hz : ∀ p ∈ U, z ∉ p) :
    (occupationLift z U).card = ∑ p ∈ U, (p.length + 1) := by
  unfold occupationLift
  rw [card_biUnion]
  · exact sum_congr rfl (fun p hp => insertionFiber_card z p (hz p hp))
  · intro p hp q hq hpq
    exact insertionFiber_disjoint z (hz p hp) (hz q hq) hpq

theorem occupationLift_card_uniform (z : α) (U : Finset (List α)) (n : ℕ)
    (hz : ∀ p ∈ U, z ∉ p) (hlen : ∀ p ∈ U, p.length = n) :
    (occupationLift z U).card = U.card * (n + 1) := by
  rw [occupationLift_card z U hz]
  exact sum_const_nat (fun p hp => by rw [hlen p hp])

/-- Exact collision sets commute with the lift, including partial occupation. -/
theorem occupationLift_inter (z : α) (U V : Finset (List α))
    (hU : ∀ p ∈ U, z ∉ p) (hV : ∀ p ∈ V, z ∉ p) :
    occupationLift z (U ∩ V) = occupationLift z U ∩ occupationLift z V := by
  ext w
  rw [mem_occupationLift z (U ∩ V) w (fun p hp => hU p (mem_inter.mp hp).1)]
  simp only [mem_inter, mem_occupationLift z U w hU, mem_occupationLift z V w hV]
  exact ⟨fun ⟨ha, hu, hv⟩ => ⟨⟨ha, hu⟩, ha, hv⟩,
    fun ⟨⟨ha, hu⟩, _, hv⟩ => ⟨ha, hu, hv⟩⟩

/-- The numerator form of preservation of the uniform normalized Gram matrix. -/
theorem overlap_mass_preserved (z : α) (U V : Finset (List α)) (n : ℕ)
    (hU : ∀ p ∈ U, z ∉ p) (hV : ∀ p ∈ V, z ∉ p)
    (hlen : ∀ p ∈ U, p.length = n) :
    (occupationLift z U ∩ occupationLift z V).card * n.factorial =
      (U ∩ V).card * (n + 1).factorial := by
  rw [← occupationLift_inter z U V hU hV,
    occupationLift_card_uniform z (U ∩ V) n
      (fun p hp => hU p (mem_inter.mp hp).1)
      (fun p hp => hlen p (mem_inter.mp hp).1),
    Nat.factorial_succ, Nat.mul_assoc]

/-- The lifted full occupation is exactly the enlarged permutation universe. -/
theorem occupationLift_permutations (z : α) (alphabet : List α) (hz : z ∉ alphabet) :
    occupationLift z alphabet.permutations.toFinset = (z :: alphabet).permutations.toFinset := by
  have hfresh : ∀ p ∈ alphabet.permutations.toFinset, z ∉ p := by
    intro p hp hzp
    exact hz ((List.mem_permutations.mp (List.mem_toFinset.mp hp)).subset hzp)
  ext w
  rw [mem_occupationLift z _ w hfresh]
  simp only [List.mem_toFinset, List.mem_permutations]
  constructor
  · rintro ⟨ha, hp⟩
    exact (List.perm_cons_erase ha).trans (hp.cons z)
  · intro hp
    refine ⟨hp.mem_iff.mpr (by simp), ?_⟩
    simpa using hp.erase z

/-- Every generated list is a genuine permutation of the enlarged alphabet. -/
theorem insertionFiber_perm {z : α} {p w : List α} (hw : w ∈ insertionFiber z p) :
    w.Perm (z :: p) := by
  obtain ⟨i, hi, rfl⟩ := mem_insertionFiber.mp hw
  exact List.perm_insertIdx z p hi

theorem insertionFiber_nodup {z : α} {p w : List α}
    (hp : p.Nodup) (hz : z ∉ p) (hw : w ∈ insertionFiber z p) : w.Nodup :=
  (insertionFiber_perm hw).nodup_iff.mpr (List.nodup_cons.mpr ⟨hz, hp⟩)

omit [DecidableEq α] in
/-- Rotation equivalence survives deleting/filtering actual symbols. -/
theorem isRotated_filter {p q : List α} (h : p.IsRotated q) (keep : α → Bool) :
    (p.filter keep).IsRotated (q.filter keep) := by
  obtain ⟨k, hk, rfl⟩ := List.isRotated_iff_mod.mp h
  rw [List.rotate_eq_drop_append_take hk, List.filter_append]
  have he : p.filter keep = (p.take k).filter keep ++ (p.drop k).filter keep := by
    rw [← List.filter_append, List.take_append_drop]
  rw [he]
  exact List.isRotated_append

theorem isRotated_erase {p q : List α} (h : p.IsRotated q) (hp : p.Nodup) (z : α) :
    (p.erase z).IsRotated (q.erase z) := by
  rw [hp.erase_eq_filter, (h.nodup_iff.mp hp).erase_eq_filter]
  exact isRotated_filter h (· != z)

omit [DecidableEq α] in
/-- Pointing a duplicate-free cycle at a fixed symbol removes rotational ambiguity. -/
theorem pointed_cycle_unique {b : α} {s t : List α}
    (hp : (b :: s).Nodup) (h : (b :: s).IsRotated (b :: t)) : s = t := by
  obtain ⟨k, hk⟩ := h
  have hi : k % (b :: s).length < (b :: s).length := Nat.mod_lt _ (by simp)
  have hh : (b :: s)[k % (b :: s).length]? = some b := by
    rw [← List.head?_rotate hi, List.rotate_mod, hk]
    rfl
  have hv : (b :: s)[k % (b :: s).length] = (b :: s)[0] := by
    rw [List.getElem?_eq_getElem hi] at hh
    exact Option.some.inj hh
  have hzero : k % (b :: s).length = 0 := hp.getElem_inj_iff.mp hv
  have hr : (b :: s).rotate k = b :: s := by
    rw [← List.rotate_mod, hzero, List.rotate_zero]
  exact (List.cons.inj (hr.symm.trans hk)).2

def rotationOrbit (q : List α) : Finset (List α) := q.cyclicPermutations.toFinset

theorem mem_rotationOrbit {p q : List α} :
    p ∈ rotationOrbit q ↔ p.IsRotated q := by
  simp [rotationOrbit]

theorem rotationOrbit_card (q : List α) (hq : q.Nodup) (hne : q ≠ []) :
    (rotationOrbit q).card = q.length := by
  rw [rotationOrbit, List.toFinset_card_of_nodup hq.cyclicPermutations,
    List.length_cyclicPermutations_of_ne_nil q hne]

/-- The child labels are anchored at the old symbol b; hence there is no
duplicate child for the wrap-around gap. -/
theorem rotationOrbit_lift_refinement (z b : α) (tail : List α)
    (hq : (b :: tail).Nodup) (hz : z ∉ b :: tail) :
    occupationLift z (rotationOrbit (b :: tail)) =
      (insertionFiber z tail).biUnion (fun r => rotationOrbit (b :: r)) := by
  have hzb : z ≠ b := fun he => hz (by simp [he])
  have hzt : z ∉ tail := fun h => hz (by simp [h])
  have hecons : ∀ s : List α, (b :: s).erase z = b :: s.erase z := by
    intro s
    exact List.erase_cons_tail (by simpa using hzb.symm)
  have fresh : ∀ p ∈ rotationOrbit (b :: tail), z ∉ p := by
    intro p hp hm
    exact hz ((mem_rotationOrbit.mp hp).mem_iff.mp hm)
  ext w
  constructor
  · intro hw
    have hw' := hw
    rw [occupationLift, mem_biUnion] at hw'
    obtain ⟨p, hp, hwp⟩ := hw'
    have hn : w.Nodup := insertionFiber_nodup
      ((mem_rotationOrbit.mp hp).nodup_iff.mpr hq) (fresh p hp) hwp
    obtain ⟨hzw, hold⟩ := (mem_occupationLift z _ w fresh).mp hw
    have hb : b ∈ w := List.mem_of_mem_erase
      ((mem_rotationOrbit.mp hold).mem_iff.mpr (by simp))
    obtain ⟨s, t, he⟩ := List.mem_iff_append.mp hb
    have hr : w.IsRotated (b :: (t ++ s)) := by
      rw [he]
      exact List.isRotated_append
    have hn' : (b :: (t ++ s)).Nodup := hr.nodup_iff.mp hn
    have hed : (b :: (t ++ s).erase z).IsRotated (b :: tail) := by
      have h := (isRotated_erase hr hn z).symm.trans (mem_rotationOrbit.mp hold)
      simpa only [hecons] using h
    have ht : (t ++ s).erase z = tail := pointed_cycle_unique
      (by simpa only [hecons] using hn'.erase z) hed
    have hzr : z ∈ t ++ s := by
      have h := hr.mem_iff.mp hzw
      simpa [hzb] using h
    exact mem_biUnion.mpr ⟨t ++ s,
      (mem_insertionFiber_iff z tail _ hzt).mpr ⟨hzr, ht⟩, mem_rotationOrbit.mpr hr⟩
  · intro hw
    obtain ⟨r, hr, hwr⟩ := mem_biUnion.mp hw
    obtain ⟨hzr, her⟩ := (mem_insertionFiber_iff z tail r hzt).mp hr
    have hp : (b :: r).Perm (b :: z :: tail) := (insertionFiber_perm hr).cons b
    have hn' : (b :: r).Nodup := hp.nodup_iff.mpr (by
      simp only [List.nodup_cons] at hq ⊢
      exact ⟨by simp [hzb.symm, hq.1], hzt, hq.2⟩)
    have hrot := mem_rotationOrbit.mp hwr
    have hn : w.Nodup := hrot.nodup_iff.mpr hn'
    apply (mem_occupationLift z _ w fresh).mpr
    refine ⟨hrot.mem_iff.mpr (by simp [hzr]), mem_rotationOrbit.mpr ?_⟩
    have hd := isRotated_erase hrot hn z
    simpa only [hecons, her] using hd

theorem child_rotationOrbits_disjoint (z b : α) (tail : List α)
    (hq : (b :: tail).Nodup) (hz : z ∉ b :: tail)
    {r s : List α} (hr : r ∈ insertionFiber z tail) (hrs : r ≠ s) :
    Disjoint (rotationOrbit (b :: r)) (rotationOrbit (b :: s)) := by
  have hzb : b ≠ z := fun h => hz (by simp [h])
  have hzt : z ∉ tail := fun h => hz (by simp [h])
  have hn : (b :: r).Nodup := ((insertionFiber_perm hr).cons b).nodup_iff.mpr (by
    simp only [List.nodup_cons] at hq ⊢
    exact ⟨by simp [hzb, hq.1], hzt, hq.2⟩)
  apply disjoint_left.mpr
  intro w hw hv
  exact hrs (pointed_cycle_unique hn
    ((mem_rotationOrbit.mp hw).symm.trans (mem_rotationOrbit.mp hv)))

theorem occupationLift_fresh (z a : α) (U : Finset (List α)) (haz : a ≠ z)
    (ha : ∀ p ∈ U, a ∉ p) : ∀ w ∈ occupationLift z U, a ∉ w := by
  intro w hw haw
  obtain ⟨p, hp, hwp⟩ := mem_biUnion.mp hw
  have h := (insertionFiber_perm hwp).subset haw
  exact (List.mem_cons.mp h).elim haz (ha p hp)

/-- Fresh-symbol insertion commutes as an exact finite set, not as a path order. -/
theorem occupationLift_comm (a z : α) (U : Finset (List α)) (haz : a ≠ z)
    (ha : ∀ p ∈ U, a ∉ p) (hz : ∀ p ∈ U, z ∉ p) :
    occupationLift z (occupationLift a U) = occupationLift a (occupationLift z U) := by
  ext w
  rw [mem_occupationLift z _ w (occupationLift_fresh a z U haz.symm hz),
    mem_occupationLift a _ w (occupationLift_fresh z a U haz ha),
    mem_occupationLift a U (w.erase z) ha, mem_occupationLift z U (w.erase a) hz]
  simp only [List.mem_erase_of_ne haz, List.mem_erase_of_ne haz.symm]
  rw [List.erase_comm z a]
  exact and_left_comm

theorem occupationLift_biUnion {ι : Type*} [DecidableEq ι]
    (z : α) (S : Finset ι) (F : ι → Finset (List α)) :
    occupationLift z (S.biUnion F) = S.biUnion (fun i => occupationLift z (F i)) := by
  ext w
  simp only [occupationLift, mem_biUnion]
  constructor
  · rintro ⟨p, ⟨i, hi, hp⟩, hw⟩; exact ⟨i, hi, p, hp, hw⟩
  · rintro ⟨i, hi, p, hp, hw⟩; exact ⟨p, ⟨i, hi, hp⟩, hw⟩

/-- All literal permutations whose deletion of the held symbol lies in q's
rotation orbit. The theorem below identifies these with Egan's nested rides. -/
def markedCycle (a : α) (q : List α) : Finset (List α) :=
  occupationLift a (rotationOrbit q)

omit [DecidableEq α] in
/-- At each departure port, advancing the inner phase then taking one outer
rotation is exactly the canonical two-character move (append b,a). -/
theorem marked_cycle_port_step (a b : α) (tail : List α) :
    (a :: ((b :: tail).rotate 1)).rotate 1 =
      (a :: b :: tail).drop 2 ++ ((a :: b :: tail).take 2).reverse := by
  simp [List.append_assoc]

/-- Literal bridge to the nested rotation footprint of a marked Egan 2-cycle. -/
theorem markedCycle_eq_nested_rotations (a : α) (q : List α)
    (hq : q.Nodup) (ha : a ∉ q) :
    markedCycle a q = (rotationOrbit q).biUnion (fun r => rotationOrbit (a :: r)) := by
  have fresh : ∀ p ∈ rotationOrbit q, a ∉ p := by
    intro p hp hm; exact ha ((mem_rotationOrbit.mp hp).mem_iff.mp hm)
  ext w
  constructor
  · intro hw
    obtain ⟨haw, hold⟩ := (mem_occupationLift a _ w fresh).mp hw
    obtain ⟨s, t, _, he, hd⟩ := List.exists_erase_eq haw
    have hr : w.IsRotated (a :: (t ++ s)) := by
      rw [he]; exact List.isRotated_append
    have hb : (t ++ s).IsRotated q := by
      have h := mem_rotationOrbit.mp hold
      rw [hd] at h
      exact List.isRotated_append.trans h
    exact mem_biUnion.mpr ⟨t ++ s, mem_rotationOrbit.mpr hb, mem_rotationOrbit.mpr hr⟩
  · intro hw
    obtain ⟨r, hr, hwr⟩ := mem_biUnion.mp hw
    have hrot := mem_rotationOrbit.mp hwr
    have hn : (a :: r).Nodup := List.nodup_cons.mpr
      ⟨fresh r hr, (mem_rotationOrbit.mp hr).nodup_iff.mpr hq⟩
    apply (mem_occupationLift a _ w fresh).mpr
    refine ⟨hrot.mem_iff.mpr (by simp), mem_rotationOrbit.mpr ?_⟩
    have hd := isRotated_erase hrot (hrot.nodup_iff.mpr hn) a
    have hd' : (w.erase a).IsRotated r := by simpa using hd
    exact hd'.trans (mem_rotationOrbit.mp hr)

theorem markedCycle_card (a : α) (q : List α)
    (hq : q.Nodup) (hne : q ≠ []) (ha : a ∉ q) :
    (markedCycle a q).card = q.length * (q.length + 1) := by
  rw [markedCycle, occupationLift_card_uniform a _ q.length]
  · rw [rotationOrbit_card q hq hne]
  · intro p hp h; exact ha ((mem_rotationOrbit.mp hp).mem_iff.mp h)
  · intro p hp; exact (mem_rotationOrbit.mp hp).perm.length_eq

/-- The all-n marked two-cycle refinement. `b` is an old anchor, `a` is held,
and `z` is new. The child list has exactly tail.length+1 cyclic gaps. -/
theorem markedCycle_lift_refinement (a z b : α) (tail : List α)
    (hq : (b :: tail).Nodup) (ha : a ∉ b :: tail) (hz : z ∉ b :: tail)
    (haz : a ≠ z) :
    occupationLift z (markedCycle a (b :: tail)) =
      (insertionFiber z tail).biUnion (fun r => markedCycle a (b :: r)) := by
  have fresh (x : α) (hx : x ∉ b :: tail) :
      ∀ p ∈ rotationOrbit (b :: tail), x ∉ p := by
    intro p hp hm; exact hx ((mem_rotationOrbit.mp hp).mem_iff.mp hm)
  rw [markedCycle, occupationLift_comm a z _ haz (fresh a ha) (fresh z hz),
    rotationOrbit_lift_refinement z b tail hq hz, occupationLift_biUnion]
  rfl

theorem child_markedCycles_disjoint (a z b : α) (tail : List α)
    (hq : (b :: tail).Nodup) (ha : a ∉ b :: tail) (hz : z ∉ b :: tail)
    (haz : a ≠ z) {r s : List α} (hr : r ∈ insertionFiber z tail)
    (hs : s ∈ insertionFiber z tail) (hrs : r ≠ s) :
    Disjoint (markedCycle a (b :: r)) (markedCycle a (b :: s)) := by
  have fresh {t : List α} (ht : t ∈ insertionFiber z tail) :
      ∀ p ∈ rotationOrbit (b :: t), a ∉ p := by
    intro p hp hm
    have h := ((mem_rotationOrbit.mp hp).perm.trans ((insertionFiber_perm ht).cons b)).subset hm
    have hab : a ≠ b := fun he => ha (by simp [he])
    have hat : a ∉ tail := fun h => ha (by simp [h])
    simp [hab, haz, hat] at h
  apply disjoint_left.mpr
  intro w hw hv
  have hwr := ((mem_occupationLift a _ w (fresh hr)).mp hw).2
  have hws := ((mem_occupationLift a _ w (fresh hs)).mp hv).2
  exact disjoint_left.mp (child_rotationOrbits_disjoint z b tail hq hz hr hrs) hwr hws

/-- Uniform child size, with no fixed alphabet order. If the old order is
n=tail.length+2, each child has n(n+1) literal permutation addresses. -/
theorem child_markedCycle_card (a z b : α) (tail : List α)
    (hq : (b :: tail).Nodup) (ha : a ∉ b :: tail) (hz : z ∉ b :: tail)
    (haz : a ≠ z) {r : List α} (hr : r ∈ insertionFiber z tail) :
    (markedCycle a (b :: r)).card = (tail.length + 2) * (tail.length + 3) := by
  have hp := (insertionFiber_perm hr).cons b
  have hzb : b ≠ z := fun he => hz (by simp [he])
  have hzt : z ∉ tail := fun h => hz (by simp [h])
  have hn : (b :: r).Nodup := hp.nodup_iff.mpr (by
    simp only [List.nodup_cons] at hq ⊢
    exact ⟨by simp [hzb, hq.1], hzt, hq.2⟩)
  have hf : a ∉ b :: r := by
    intro hm
    have h := hp.subset hm
    have hab : a ≠ b := fun he => ha (by simp [he])
    have hat : a ∉ tail := fun h => ha (by simp [h])
    simp [hab, haz, hat] at h
  have hl : r.length = tail.length + 1 := (insertionFiber_perm hr).length_eq
  rw [markedCycle_card a (b :: r) hn (by simp) hf]
  simp [hl, Nat.add_assoc]

end Coeff2.Charlieplex.EganOccupationLift
