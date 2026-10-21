import Coeff2.CharlieNonwholeOccupation

/-!
# Two-marker occupation from literal insertions, at arbitrary order

The base tail `t` has length n-3; a separate pointing symbol turns each root
below into a rotation orbit of length n. Rows hold `a`, columns hold `b`.
No numerical corpus matrix is a hypothesis. This is an occupation module;
it does not assert that the redistributed sets have cheap compatible ports.
-/
namespace Coeff2.Charlieplex.TwoMarkerPartition
open Finset EganOccupationLift EganComponentGraph PhaseDetour
variable {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
private theorem fresh_cons {a x : α} {t : List α} (h : a ∉ x :: t) :
    a ≠ x ∧ a ∉ t := by simpa using h

def row (a b : α) (t : List α) (i : ℕ) : Finset (List α) :=
  insertionFiber a (t.insertIdx i b)

omit [DecidableEq α] in
theorem fresh_insert (a b : α) (t : List α) (hab : a ≠ b)
    (ha : a ∉ t) (i : ℕ) : a ∉ t.insertIdx i b := by
  intro h
  exact (List.eq_or_mem_of_mem_insertIdx h).elim hab ha

theorem intersection_cons (a b x : α) (r s : List α)
    (ha : a ∉ x :: r) (hb : b ∉ x :: s) (hab : a ≠ b) :
    insertionFiber a (x :: r) ∩ insertionFiber b (x :: s) =
      (insertionFiber a r ∩ insertionFiber b s).image (List.cons x) := by
  have hax : a ≠ x := (fresh_cons ha).1
  have hbx : b ≠ x := (fresh_cons hb).1
  have har : a ∉ r := (fresh_cons ha).2
  have hbs : b ∉ s := (fresh_cons hb).2
  ext w
  constructor
  · intro hw
    obtain ⟨haw, hea⟩ := (mem_insertionFiber_iff a _ w ha).mp (mem_inter.mp hw).1
    obtain ⟨hbw, heb⟩ := (mem_insertionFiber_iff b _ w hb).mp (mem_inter.mp hw).2
    cases w with
    | nil => simp at haw
    | cons y w =>
      have hya : y ≠ a := by
        intro hy; subst y
        rw [List.erase_cons_tail (by simpa using hab)] at heb
        exact hax (List.cons.inj heb).1
      have hyb : y ≠ b := by
        intro hy; subst y
        rw [List.erase_cons_tail (by simpa using hab.symm)] at hea
        exact hbx (List.cons.inj hea).1
      rw [List.erase_cons_tail (by simpa using hya)] at hea
      rw [List.erase_cons_tail (by simpa using hyb)] at heb
      have hyx := (List.cons.inj hea).1
      subst y
      apply mem_image.mpr
      refine ⟨w, mem_inter.mpr ⟨?_, ?_⟩, rfl⟩
      · exact (mem_insertionFiber_iff a _ _ har).mpr
          ⟨by simpa [hax] using haw, (List.cons.inj hea).2⟩
      · exact (mem_insertionFiber_iff b _ _ hbs).mpr
          ⟨by simpa [hbx] using hbw, (List.cons.inj heb).2⟩
  · rintro hw
    obtain ⟨w, hv, rfl⟩ := mem_image.mp hw
    obtain ⟨haw, hea⟩ := (mem_insertionFiber_iff a _ w har).mp (mem_inter.mp hv).1
    obtain ⟨hbw, heb⟩ := (mem_insertionFiber_iff b _ w hbs).mp (mem_inter.mp hv).2
    apply mem_inter.mpr
    constructor
    · apply (mem_insertionFiber_iff a _ _ ha).mpr
      exact ⟨by simp [haw], by simpa [hax.symm] using congrArg (List.cons x) hea⟩
    · apply (mem_insertionFiber_iff b _ _ hb).mpr
      exact ⟨by simp [hbw], by simpa [hbx.symm] using congrArg (List.cons x) heb⟩

theorem front_later_intersection (a b x : α) (t : List α) (j : ℕ)
    (hab : a ≠ b) (ha : a ∉ x :: t) (hb : b ∉ x :: t)
    (hj : j ≤ t.length) :
    insertionFiber a (b :: x :: t) ∩ insertionFiber b (x :: t.insertIdx j a) =
      {b :: x :: t.insertIdx j a} := by
  have hax : a ≠ x := (fresh_cons ha).1
  have hbx : b ≠ x := (fresh_cons hb).1
  have hat : a ∉ t := (fresh_cons ha).2
  have hbt : b ∉ t := (fresh_cons hb).2
  have haf : a ∉ b :: x :: t := by simp [hab, ha]
  have hbf : b ∉ x :: t.insertIdx j a := by
    simp [hbx, fresh_insert b a t hab.symm hbt j]
  have hgood : b :: x :: t.insertIdx j a ∈
      insertionFiber a (b :: x :: t) ∩ insertionFiber b (x :: t.insertIdx j a) := by
    apply mem_inter.mpr
    constructor
    · apply (mem_insertionFiber_iff a _ _ haf).mpr
      constructor
      · have h := (List.mem_insertIdx hj).mpr (Or.inl (rfl : a = a))
        simp [h]
      · simp [hab.symm, hax.symm, erase_insertIdx a t hat j hj]
    · exact mem_insertionFiber.mpr ⟨0, by omega, by simp⟩
  apply eq_singleton_iff_unique_mem.mpr
  refine ⟨hgood, ?_⟩
  intro w hw
  rcases common_root_two_candidates a b b x (x :: t) (t.insertIdx j a)
      w haf hbf hbx hw with he | he
  · subst w
    have h := ((mem_insertionFiber_iff b _ _ hbf).mp (mem_inter.mp hw).2).2
    rw [List.erase_cons_tail (by simpa using hab)] at h
    exact False.elim (hax (List.cons.inj h).1)
  · exact he

/-- Exact all-order crossing matrix of the two literal insertion partitions:
one common rotation root in different gaps, two in the same gap. -/
theorem crossing_card (a b : α) (t : List α) (hab : a ≠ b)
    (ha : a ∉ t) (hb : b ∉ t) (i j : ℕ)
    (hi : i ≤ t.length) (hj : j ≤ t.length) :
    (row a b t i ∩ row b a t j).card = 1 + if i = j then 1 else 0 := by
  induction t generalizing i j with
  | nil =>
    have hi0 : i = 0 := by simpa using hi
    have hj0 : j = 0 := by simpa using hj
    subst i; subst j
    simpa [row] using adjacent_fiber_intersection_card a b [] hab (by simp) (by simp)
  | cons x t ih =>
    have hat : a ∉ t := (fresh_cons ha).2
    have hbt : b ∉ t := (fresh_cons hb).2
    cases i with
    | zero =>
      cases j with
      | zero => simpa [row] using adjacent_fiber_intersection_card a b (x :: t) hab ha hb
      | succ j =>
        simp only [row, List.insertIdx_zero, List.insertIdx_succ_cons]
        rw [front_later_intersection a b x t j hab ha hb (by simpa using hj)]
        simp
    | succ i =>
      cases j with
      | zero =>
        simp only [row, List.insertIdx_zero, List.insertIdx_succ_cons]
        rw [inter_comm, front_later_intersection b a x t i hab.symm hb ha (by simpa using hi)]
        simp
      | succ j =>
        have hax : a ≠ x := (fresh_cons ha).1
        have hbx : b ≠ x := (fresh_cons hb).1
        simp only [row, List.insertIdx_succ_cons]
        rw [intersection_cons a b x _ _
          (by simp [hax, fresh_insert a b t hab hat i])
          (by simp [hbx, fresh_insert b a t hab.symm hbt j]) hab,
          card_image_of_injective _ List.cons_injective]
        simpa [row] using ih hat hbt i j (by simpa using hi) (by simpa using hj)

/-- Every row is a literal insertion fiber of the expected size. -/
theorem row_card (a b : α) (t : List α) (hab : a ≠ b) (ha : a ∉ t)
    (i : ℕ) (hi : i ≤ t.length) : (row a b t i).card = t.length + 2 := by
  rw [row, insertionFiber_card a _ (fresh_insert a b t hab ha i)]
  simp [List.length_insertIdx_of_le_length hi]

theorem rows_disjoint (a b : α) (t : List α) (hab : a ≠ b)
    (ha : a ∉ t) (hb : b ∉ t) (i j : ℕ)
    (hi : i ≤ t.length) (hj : j ≤ t.length) (hne : i ≠ j) :
    Disjoint (row a b t i) (row a b t j) := by
  apply insertionFiber_disjoint a
    (fresh_insert a b t hab ha i) (fresh_insert a b t hab ha j)
  intro he
  exact hne (List.injOn_insertIdx_index_of_notMem t b hb hi hj he)

def catalog (a b : α) (t : List α) : Finset (List α) :=
  (range (t.length + 1)).biUnion (row a b t)

theorem catalog_eq_lift (a b : α) (t : List α) :
    catalog a b t = occupationLift a (insertionFiber b t) := by
  unfold catalog occupationLift
  rw [insertionFiber, image_biUnion]
  rfl

theorem catalog_comm (a b : α) (t : List α) (hab : a ≠ b)
    (ha : a ∉ t) (hb : b ∉ t) : catalog a b t = catalog b a t := by
  have h := occupationLift_comm b a {t} hab.symm
    (by simpa using hb) (by simpa using ha)
  simpa [catalog_eq_lift, occupationLift] using h

theorem catalog_card (a b : α) (t : List α) (hab : a ≠ b)
    (ha : a ∉ t) (hb : b ∉ t) :
    (catalog a b t).card = (t.length + 1) * (t.length + 2) := by
  rw [catalog, card_biUnion]
  · calc
      _ = ∑ _i ∈ range (t.length + 1), (t.length + 2) :=
        sum_congr rfl (fun i hi => row_card a b t hab ha i
          (Nat.le_of_lt_succ (mem_range.mp hi)))
      _ = _ := by simp
  · intro i hi j hj hij
    exact rows_disjoint a b t hab ha hb i j
      (Nat.le_of_lt_succ (mem_range.mp hi)) (Nat.le_of_lt_succ (mem_range.mp hj)) hij

def hubs (a b : α) (t : List α) (h k : ℕ) : Finset (List α) :=
  row b a t h ∪ row b a t k

/-- Transfer two whole columns to their named recipients, leaving the other
pieces as partial rows. Membership refers to actual symbol lists. -/
def switched (a b : α) (t : List α) (h k i : ℕ) : Finset (List α) :=
  (row a b t i \ hubs a b t h k) ∪
    if i = h ∨ i = k then row b a t i else ∅

theorem hubs_subset_catalog (a b : α) (t : List α) (hab : a ≠ b)
    (ha : a ∉ t) (hb : b ∉ t) (h k : ℕ)
    (hh : h ≤ t.length) (hk : k ≤ t.length) :
    hubs a b t h k ⊆ catalog a b t := by
  rw [catalog_comm a b t hab ha hb]
  intro w hw
  rcases mem_union.mp hw with hw | hw
  · exact mem_biUnion.mpr ⟨h, mem_range.mpr (by omega), hw⟩
  · exact mem_biUnion.mpr ⟨k, mem_range.mpr (by omega), hw⟩

/-- All-order exact occupation conservation: no missing roots and no guessed
matching. The boundary ordering of these sets is a separate problem. -/
theorem switched_union (a b : α) (t : List α) (hab : a ≠ b)
    (ha : a ∉ t) (hb : b ∉ t) (h k : ℕ)
    (hh : h ≤ t.length) (hk : k ≤ t.length) :
    (range (t.length + 1)).biUnion (switched a b t h k) = catalog a b t := by
  have hsub := hubs_subset_catalog a b t hab ha hb h k hh hk
  ext w
  constructor
  · intro hw
    obtain ⟨i, hi, hw⟩ := mem_biUnion.mp hw
    rcases mem_union.mp hw with hr | hc
    · exact mem_biUnion.mpr ⟨i, hi, (mem_sdiff.mp hr).1⟩
    · by_cases his : i = h ∨ i = k
      · have hwc : w ∈ row b a t i := by simpa [his] using hc
        apply hsub
        rcases his with rfl | rfl
        · exact mem_union_left _ hwc
        · exact mem_union_right _ hwc
      · simp [his] at hc
  · intro hw
    by_cases hwh : w ∈ hubs a b t h k
    · rcases mem_union.mp hwh with hwh | hwh
      · exact mem_biUnion.mpr ⟨h, mem_range.mpr (by omega), by simp [switched, hwh]⟩
      · exact mem_biUnion.mpr ⟨k, mem_range.mpr (by omega), by simp [switched, hwh]⟩
    · obtain ⟨i, hi, hwi⟩ := mem_biUnion.mp hw
      exact mem_biUnion.mpr ⟨i, hi, mem_union_left _ (mem_sdiff.mpr ⟨hwi, hwh⟩)⟩

theorem switched_disjoint (a b : α) (t : List α) (hab : a ≠ b)
    (ha : a ∉ t) (hb : b ∉ t) (h k i j : ℕ)
    (hi : i ≤ t.length) (hj : j ≤ t.length) (hne : i ≠ j) :
    Disjoint (switched a b t h k i) (switched a b t h k j) := by
  have hrow := disjoint_left.mp (rows_disjoint a b t hab ha hb i j hi hj hne)
  have hcol := disjoint_left.mp (rows_disjoint b a t hab.symm hb ha i j hi hj hne)
  apply disjoint_left.mpr
  intro w hwi hwj
  have memsw (i : ℕ) : w ∈ switched a b t h k i ↔
      (w ∈ row a b t i ∧ w ∉ hubs a b t h k) ∨
      ((i = h ∨ i = k) ∧ w ∈ row b a t i) := by
    by_cases his : i = h ∨ i = k <;> simp [switched, his]
  rw [memsw] at hwi hwj
  rcases hwi with ⟨hwi, hwih⟩ | ⟨his, hwi⟩
  · rcases hwj with ⟨hwj, _⟩ | ⟨hjs, hwj⟩
    · exact hrow hwi hwj
    · apply hwih
      rcases hjs with rfl | rfl
      · exact mem_union_left _ hwj
      · exact mem_union_right _ hwj
  · rcases hwj with ⟨_, hwjh⟩ | ⟨_, hwj⟩
    · apply hwjh
      rcases his with rfl | rfl
      · exact mem_union_left _ hwi
      · exact mem_union_right _ hwi
    · exact hcol hwi hwj

theorem hubs_inter_card (a b : α) (t : List α) (hab : a ≠ b)
    (ha : a ∉ t) (hb : b ∉ t) (h k i : ℕ)
    (hh : h ≤ t.length) (hk : k ≤ t.length) (hneq : h ≠ k)
    (hi : i ≤ t.length) :
    (row a b t i ∩ hubs a b t h k).card = 2 + if i = h ∨ i = k then 1 else 0 := by
  rw [hubs, inter_union_distrib_left, card_union_of_disjoint]
  · rw [crossing_card a b t hab ha hb i h hi hh,
      crossing_card a b t hab ha hb i k hi hk]
    by_cases hih : i = h <;> by_cases hik : i = k <;> simp_all
  · exact (rows_disjoint b a t hab.symm hb ha h k hh hk hneq).mono
      inter_subset_right inter_subset_right

theorem remainder_card (a b : α) (t : List α) (hab : a ≠ b)
    (ha : a ∉ t) (hb : b ∉ t) (h k i : ℕ)
    (hh : h ≤ t.length) (hk : k ≤ t.length) (hneq : h ≠ k)
    (hi : i ≤ t.length) :
    (row a b t i \ hubs a b t h k).card =
      t.length - if i = h ∨ i = k then 1 else 0 := by
  have he := card_sdiff_add_card_inter (row a b t i) (hubs a b t h k)
  rw [hubs_inter_card a b t hab ha hb h k i hh hk hneq hi,
    row_card a b t hab ha i hi] at he
  split_ifs at he ⊢ <;> omega

/-- With n=length(t)+3, there are n-4 short pieces of n-3 orbits and two
long pieces of 2n-5 orbits. This now follows from literal set arithmetic. -/
theorem switched_card (a b : α) (t : List α) (hab : a ≠ b)
    (ha : a ∉ t) (hb : b ∉ t) (h k i : ℕ)
    (hh : h ≤ t.length) (hk : k ≤ t.length) (hneq : h ≠ k)
    (hi : i ≤ t.length) :
    (switched a b t h k i).card =
      if i = h ∨ i = k then 2 * t.length + 1 else t.length := by
  have ht : 1 ≤ t.length := by omega
  unfold switched
  by_cases his : i = h ∨ i = k
  · rw [if_pos his, card_union_of_disjoint]
    · rw [remainder_card a b t hab ha hb h k i hh hk hneq hi,
        row_card b a t hab.symm hb i hi, if_pos his, if_pos his]
      omega
    · apply disjoint_left.mpr
      intro w hw hc
      apply (mem_sdiff.mp hw).2
      rcases his with rfl | rfl
      · exact mem_union_left _ hc
      · exact mem_union_right _ hc
  · simp only [if_neg his, union_empty]
    rw [remainder_card a b t hab ha hb h k i hh hk hneq hi, if_neg his, Nat.sub_zero]

theorem row_inter_remainder (a b : α) (t : List α) (hab : a ≠ b)
    (ha : a ∉ t) (hb : b ∉ t) (h k i j : ℕ)
    (hi : i ≤ t.length) (hj : j ≤ t.length) :
    row a b t i ∩ (row a b t j \ hubs a b t h k) =
      if i = j then row a b t i \ hubs a b t h k else ∅ := by
  by_cases hij : i = j
  · subst j
    ext w
    simp only [if_pos, mem_inter, mem_sdiff]
    tauto
  · have hd := disjoint_left.mp (rows_disjoint a b t hab ha hb i j hi hj hij)
    rw [if_neg hij]
    apply eq_empty_iff_forall_notMem.mpr
    intro w hw
    exact hd (mem_inter.mp hw).1 (mem_sdiff.mp (mem_inter.mp hw).2).1

/-- Generator-free derivation of the earlier rank-one ownership formula,
now for explicit literal insertion sets and every alphabet size. -/
theorem switched_crossing_card (a b : α) (t : List α) (hab : a ≠ b)
    (ha : a ∉ t) (hb : b ∉ t) (h k i j : ℕ)
    (hh : h ≤ t.length) (hk : k ≤ t.length) (hneq : h ≠ k)
    (hi : i ≤ t.length) (hj : j ≤ t.length) :
    (row a b t i ∩ switched a b t h k j).card =
      (if i = j then t.length else 0) + (if j = h ∨ j = k then 1 else 0) := by
  have ht : 1 ≤ t.length := by omega
  unfold switched
  by_cases hjs : j = h ∨ j = k
  · rw [if_pos hjs, inter_union_distrib_left, card_union_of_disjoint]
    · rw [row_inter_remainder a b t hab ha hb h k i j hi hj,
        crossing_card a b t hab ha hb i j hi hj]
      by_cases hij : i = j
      · subst j
        rw [if_pos rfl, if_pos rfl, if_pos rfl, if_pos hjs,
          remainder_card a b t hab ha hb h k i hh hk hneq hi, if_pos hjs]
        omega
      · simp [hij, hjs]
    · apply disjoint_left.mpr
      intro w hw hc
      apply (mem_sdiff.mp (mem_inter.mp hw).2).2
      rcases hjs with rfl | rfl
      · exact mem_union_left _ (mem_inter.mp hc).2
      · exact mem_union_right _ (mem_inter.mp hc).2
  · rw [if_neg hjs, union_empty, row_inter_remainder a b t hab ha hb h k i j hi hj]
    by_cases hij : i = j
    · subst j
      rw [if_pos rfl, if_pos rfl, if_neg hjs,
        remainder_card a b t hab ha hb h k i hh hk hneq hi, if_neg hjs]
      simp
    · simp [hij, hjs]

theorem catalog_perm (a b : α) (t : List α) {p : List α}
    (hp : p ∈ catalog a b t) : p.Perm (a :: b :: t) := by
  rw [catalog_eq_lift] at hp
  obtain ⟨q, hq, hpq⟩ := mem_biUnion.mp hp
  exact (insertionFiber_perm hpq).trans ((insertionFiber_perm hq).cons a)

/-- The pointed sets really are the double-insertion fiber of a literal base
rotation orbit. Not an assumed abstract occupation universe. -/
theorem rooted_catalog (z a b : α) (t : List α)
    (ht : (z :: t).Nodup) (ha : a ∉ z :: t) (hb : b ∉ z :: t)
    (hab : a ≠ b) :
    rootedOrbits z (catalog a b t) =
      occupationLift a (occupationLift b (rotationOrbit (z :: t))) := by
  have haz : a ≠ z := (fresh_cons ha).1
  have hbz : b ≠ z := (fresh_cons hb).1
  have hat : a ∉ t := (fresh_cons ha).2
  have hbt : b ∉ t := (fresh_cons hb).2
  rw [rotationOrbit_lift_refinement b z t ht hb, occupationLift_biUnion]
  rw [catalog_eq_lift, rootedOrbits, occupationLift, biUnion_biUnion]
  apply biUnion_congr rfl
  intro r hr
  have hp := insertionFiber_perm hr
  have hnr : (z :: r).Nodup := (hp.cons z).nodup_iff.mpr (by
    simp only [List.nodup_cons] at ht ⊢
    exact ⟨by simp [hbz.symm, ht.1], hbt, ht.2⟩)
  have har : a ∉ z :: r := by
    have hf : a ∉ r := fun hm => by
      have hm' := hp.subset hm
      simp [hab, hat] at hm'
    simp [haz, hf]
  exact (rotationOrbit_lift_refinement a z r hnr har).symm

theorem rooted_catalog_card (z a b : α) (t : List α)
    (ht : (z :: t).Nodup) (ha : a ∉ z :: t) (hb : b ∉ z :: t)
    (hab : a ≠ b) :
    (rootedOrbits z (catalog a b t)).card =
      (t.length + 1) * (t.length + 2) * (t.length + 3) := by
  have hn : (z :: a :: b :: t).Nodup := by
    have hat := fresh_cons ha
    have hbt := fresh_cons hb
    have hzt := List.nodup_cons.mp ht
    simp only [List.nodup_cons]
    exact ⟨by simp [hat.1.symm, hbt.1.symm, hzt.1],
      by simp [hab, hat.2], hbt.2, hzt.2⟩
  rw [rootedOrbits_card z _ (fun p hp =>
    ((catalog_perm a b t hp).cons z).nodup_iff.mpr hn)]
  calc
    _ = ∑ _p ∈ catalog a b t, (t.length + 3) := by
      apply sum_congr rfl
      intro p hp
      have hl := (catalog_perm a b t hp).length_eq
      simp only [List.length_cons] at hl
      omega
    _ = _ := by simp [catalog_card a b t hab (fresh_cons ha).2 (fresh_cons hb).2]

/-- Exact conservation after restoring every rotation phase. -/
theorem switched_literal_occupation (z a b : α) (t : List α)
    (ht : (z :: t).Nodup) (ha : a ∉ z :: t) (hb : b ∉ z :: t)
    (hab : a ≠ b) (h k : ℕ) (hh : h ≤ t.length) (hk : k ≤ t.length) :
    rootedOrbits z ((range (t.length + 1)).biUnion (switched a b t h k)) =
      occupationLift a (occupationLift b (rotationOrbit (z :: t))) := by
  rw [switched_union a b t hab (fresh_cons ha).2 (fresh_cons hb).2 h k hh hk]
  exact rooted_catalog z a b t ht ha hb hab

/-- The atomicity result now applies to actual roots, without an assumed
matrix support. It is limited to this old/new catalog, not all possible trades. -/
theorem literal_trade_atomic (a b : α) (t : List α) (hab : a ≠ b)
    (ha : a ∉ t) (hb : b ∉ t) (h k : Fin (t.length + 1)) (hneq : h ≠ k)
    (removed added : Fin (t.length + 1) → ℤ)
    (hocc : ∀ (i j : Fin (t.length + 1)) (w : List α),
      w ∈ row a b t i ∩ switched a b t h k j → removed i = added j) :
    (∀ i, removed i = added h) ∧ (∀ j, added j = added h) := by
  have hh : h.val ≤ t.length := by omega
  have hk : k.val ≤ t.length := by omega
  have hne : h.val ≠ k.val := fun he => hneq (Fin.ext he)
  have ht : 1 ≤ t.length := by omega
  apply NonwholeOccupation.occupation_trade_atomic h k removed added
  intro i j hs
  have hc := switched_crossing_card a b t hab ha hb h k i j hh hk hne
    (by omega) (by omega)
  have hpos : 0 < (row a b t i ∩ switched a b t h k j).card := by
    rw [hc]
    rcases hs with hij | hjh | hjk
    · subst j; simp; omega
    · subst j; simp
    · subst j; simp
  obtain ⟨w, hw⟩ := card_pos.mp hpos
  exact hocc i j w hw

theorem rooted_permutations (z : α) (A : List α) :
    rootedOrbits z A.permutations.toFinset = (z :: A).permutations.toFinset := by
  ext w
  constructor
  · intro hw
    obtain ⟨p, hp, hwp⟩ := mem_biUnion.mp hw
    apply List.mem_toFinset.mpr
    apply List.mem_permutations.mpr
    exact (mem_rotationOrbit.mp hwp).perm.trans
      ((List.mem_permutations.mp (List.mem_toFinset.mp hp)).cons z)
  · intro hw
    have hp := List.mem_permutations.mp (List.mem_toFinset.mp hw)
    have hz : z ∈ w := hp.mem_iff.mpr (by simp)
    obtain ⟨s, t, he⟩ := List.mem_iff_append.mp hz
    have hr : w.IsRotated (z :: (t ++ s)) := by
      rw [he]; exact List.isRotated_append
    have htail : (t ++ s).Perm A := List.Perm.cons_inv (hr.perm.symm.trans hp)
    exact mem_biUnion.mpr ⟨t ++ s,
      List.mem_toFinset.mpr (List.mem_permutations.mpr htail), mem_rotationOrbit.mpr hr⟩

def plannedRoots (a b : α) (select : List α → Bool) (left right : List α → ℕ)
    (t : List α) : Finset (List α) :=
  if select t then (range (t.length + 1)).biUnion (switched a b t (left t) (right t))
  else catalog a b t

/-- Complete all-N occupation theorem for an arbitrary independent choice of
ordinary/switched catalog in every base fiber. The choices need not be regular.
This proves the actual permutation universe, not only its cardinality. -/
theorem global_planned_occupation (z a b : α) (A : List α)
    (hA : (z :: A).Nodup) (ha : a ∉ z :: A) (hb : b ∉ z :: A) (hab : a ≠ b)
    (select : List α → Bool) (left right : List α → ℕ)
    (hl : ∀ t ∈ A.permutations.toFinset, left t ≤ t.length)
    (hr : ∀ t ∈ A.permutations.toFinset, right t ≤ t.length) :
    A.permutations.toFinset.biUnion (fun t => rootedOrbits z (plannedRoots a b select left right t)) =
      (a :: b :: z :: A).permutations.toFinset := by
  calc
    _ = A.permutations.toFinset.biUnion (fun t =>
        occupationLift a (occupationLift b (rotationOrbit (z :: t)))) := by
      apply biUnion_congr rfl
      intro t ht
      have hp := (List.mem_permutations.mp (List.mem_toFinset.mp ht)).cons z
      have hnt := hp.nodup_iff.mpr hA
      have hat : a ∉ z :: t := fun hm => ha (hp.subset hm)
      have hbt : b ∉ z :: t := fun hm => hb (hp.subset hm)
      unfold plannedRoots
      split
      · exact switched_literal_occupation z a b t hnt hat hbt hab (left t) (right t)
          (hl t ht) (hr t ht)
      · exact rooted_catalog z a b t hnt hat hbt hab
    _ = occupationLift a (occupationLift b (rootedOrbits z A.permutations.toFinset)) := by
      simp only [rootedOrbits, occupationLift_biUnion]
    _ = _ := by
      rw [rooted_permutations z A, occupationLift_permutations b (z :: A) hb,
        occupationLift_permutations a (b :: z :: A) (by simp [hab, ha])]

#print axioms crossing_card
#print axioms row_card
#print axioms rows_disjoint
#print axioms catalog_comm
#print axioms catalog_card
#print axioms switched_union
#print axioms switched_disjoint
#print axioms switched_card
#print axioms switched_crossing_card
#print axioms rooted_catalog
#print axioms rooted_catalog_card
#print axioms switched_literal_occupation
#print axioms literal_trade_atomic
#print axioms global_planned_occupation
end Coeff2.Charlieplex.TwoMarkerPartition
