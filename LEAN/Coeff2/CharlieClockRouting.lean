import Coeff2.CharlieSignedBoundaryLift
import Mathlib.Data.ZMod.QuotientGroup

/-!
# Phase-first routing of occupation-preserving packets

The insertion slot is a clock in Z/(n-3). The literal port laws imported
above give forward = -1 and backward = +1. This file retains every prefix
clock, not just the total charge. Subtracting the prefix charge leaves a
constant clock along the interior of a lower circuit; only the closing seam
advances it by the total charge.

The results classify the phase routes over a supplied closed lower circuit.
They do not invent that circuit, prove its parent fibers disjoint, or claim
that different circuits have an inexpensive global attachment.
-/
namespace Coeff2.Charlieplex.ClockRouting
open SignedBoundaryLift

def tick (backward : Bool) : ℤ := if backward then 1 else -1

theorem charge_append (as bs : List Bool) : charge (as ++ bs) = charge as + charge bs := by
  induction as with
  | nil => simp [charge]
  | cons a as ih => cases a <;> simp [charge, ih] <;> ring

theorem prefix_step (ds : List Bool) (i : ℕ) (hi : i < ds.length) :
    charge (ds.take (i+1)) = charge (ds.take i) + tick ds[i] := by
  induction ds generalizing i with
  | nil => simp at hi
  | cons b ds ih =>
    cases i with
    | zero => simp [charge, tick]
    | succ i =>
      have hi' : i < ds.length := by simpa using hi
      simp only [List.take_succ_cons, charge, List.getElem_cons_succ]
      rw [ih i hi']
      unfold tick
      abel

def offset {k : ℕ} (ds : List Bool) (i : ℕ) : ZMod k := charge (ds.take i)

/-- The sheet reached at each actual lower-edge position. -/
def phaseAt {k : ℕ} (ds : List Bool) (start : ZMod k) (i : ℕ) : ZMod k :=
  start + offset ds i

theorem phaseAt_exec {k : ℕ} (ds : List Bool) (start : ZMod k) (i : ℕ) :
    phaseAt ds start i = transport (ds.take i) start := by
  rw [transport_eq]; rfl

theorem phaseAt_step {k : ℕ} (ds : List Bool) (start : ZMod k)
    (i : ℕ) (hi : i < ds.length) :
    phaseAt ds start (i+1) = phaseAt ds start i + (tick ds[i] : ZMod k) := by
  simp only [phaseAt, offset, prefix_step ds i hi, Int.cast_add]
  abel

def nextIndex (ds : List Bool) (i : Fin ds.length) : Fin ds.length :=
  if h : i.val + 1 < ds.length then ⟨i.val+1, h⟩ else ⟨0, by omega⟩

/-- One directed edge of the supplied circuit, with its literal signed tick. -/
def step {k : ℕ} (ds : List Bool) (s : Fin ds.length × ZMod k) :
    Fin ds.length × ZMod k :=
  (nextIndex ds s.1, s.2 + (tick ds[s.1.val] : ZMod k))

/-- This change of coordinates is reversible: no phase information is lost. -/
def normalize {k : ℕ} (ds : List Bool) :
    (Fin ds.length × ZMod k) ≃ (Fin ds.length × ZMod k) where
  toFun s := (s.1, s.2 - offset ds s.1.val)
  invFun s := (s.1, s.2 + offset ds s.1.val)
  left_inv s := by simp
  right_inv s := by simp

/-- All interior clock operations cancel; the closing seam retains the charge. -/
def seamStep {k : ℕ} (ds : List Bool) (s : Fin ds.length × ZMod k) :
    Fin ds.length × ZMod k :=
  (nextIndex ds s.1,
    if s.1.val+1 < ds.length then s.2 else s.2 + (charge ds : ZMod k))

theorem normalized_step {k : ℕ} (ds : List Bool) (s : Fin ds.length × ZMod k) :
    normalize ds (step ds s) = seamStep ds (normalize ds s) := by
  apply Prod.ext
  · rfl
  · change (s.2 + (tick ds[s.1.val] : ZMod k)) - offset ds (nextIndex ds s.1).val = _
    have h := prefix_step ds s.1.val s.1.isLt
    by_cases hi : s.1.val+1 < ds.length
    · simp only [nextIndex, seamStep, normalize, Equiv.coe_fn_mk, hi, if_true]
      change (s.2 + (tick ds[s.1.val] : ZMod k)) -
        (charge (ds.take (s.1.val+1)) : ZMod k) = s.2 - (charge (ds.take s.1.val) : ZMod k)
      rw [h, Int.cast_add]
      abel
    · have he : s.1.val+1 = ds.length := by omega
      have ht : charge ds = charge (ds.take s.1.val) + tick ds[s.1.val] := by
        simpa only [he, List.take_length] using h
      simp only [nextIndex, seamStep, normalize, Equiv.coe_fn_mk, hi, if_false, dite_false]
      simp only [offset, List.take_zero, charge, Int.cast_zero]
      change (s.2 + (tick ds[s.1.val] : ZMod k)) - 0 =
        s.2 - (charge (ds.take s.1.val) : ZMod k) + (charge ds : ZMod k)
      rw [ht, Int.cast_add]
      abel

/-- Exact execution for any number of repetitions of the entire lower circuit. -/
theorem laps_then_prefix {k : ℕ} (ds : List Bool) (start : ZMod k) (laps i : ℕ) :
    transport (ds.take i) ((transport ds)^[laps] start) =
      start + laps • (charge ds : ZMod k) + offset ds i := by
  rw [repeated_transport, transport_eq]; rfl

/-- Return is exact divisibility by the clock period, not an approximate balance. -/
theorem return_iff {k : ℕ} (ds : List Bool) (start : ZMod k) (laps : ℕ) :
    (transport ds)^[laps] start = start ↔ addOrderOf (charge ds : ZMod k) ∣ laps := by
  rw [repeated_transport, add_eq_left, addOrderOf_dvd_iff_nsmul_eq_zero]

section FiniteClock
variable {k : ℕ} [NeZero k]

/-- Canonical nonnegative residue of the signed return charge. -/
def residue (ds : List Bool) : ℕ := (charge ds : ZMod k).val

def splitCount (ds : List Bool) : ℕ := Nat.gcd k (residue (k:=k) ds)

theorem period_formula (ds : List Bool) :
    addOrderOf (charge ds : ZMod k) = k / splitCount (k:=k) ds := by
  have h := ZMod.addOrderOf_coe (residue (k:=k) ds) (NeZero.ne k)
  simpa only [residue, ZMod.natCast_zmod_val, splitCount] using h

theorem return_iff_divides (ds : List Bool) (start : ZMod k) (laps : ℕ) :
    (transport ds)^[laps] start = start ↔ (k / splitCount (k:=k) ds) ∣ laps := by
  rw [return_iff, period_formula]

/-- The generated subgroup contains precisely the phase displacements obtained
by complete laps, including negative laps for the reversible clock. -/
abbrev LapSubgroup (ds : List Bool) := AddSubgroup.zmultiples (charge ds : ZMod k)

abbrev CircuitLabels (ds : List Bool) := ZMod k ⧸ LapSubgroup (k:=k) ds

def circuitLabel (ds : List Bool) (s : Fin ds.length × ZMod k) : CircuitLabels (k:=k) ds :=
  QuotientAddGroup.mk (s.2 - offset ds s.1.val)

theorem circuit_count (ds : List Bool) :
    Nat.card (CircuitLabels (k:=k) ds) = splitCount (k:=k) ds := by
  have h := (LapSubgroup (k:=k) ds).card_mul_index
  rw [Nat.card_zmultiples, period_formula, AddSubgroup.index_eq_card, Nat.card_zmod] at h
  have hg : splitCount (k:=k) ds ∣ k := Nat.gcd_dvd_left _ _
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  have hgp : 0 < splitCount (k:=k) ds := Nat.gcd_pos_of_pos_left _ hk
  have hq : 0 < k / splitCount (k:=k) ds := Nat.div_pos (Nat.le_of_dvd hk hg) hgp
  exact Nat.eq_of_mul_eq_mul_left hq (h.trans (Nat.div_mul_cancel hg).symm)

omit [NeZero k] in
/-- A phase-class test, retaining the position-dependent offsets. -/
theorem labels_eq_iff (ds : List Bool) (u v : Fin ds.length × ZMod k) :
    circuitLabel ds u = circuitLabel ds v ↔
      ∃ laps : ℤ, v.2 = u.2 + laps • (charge ds : ZMod k) +
        offset ds v.1.val - offset ds u.1.val := by
  rw [circuitLabel, circuitLabel, QuotientAddGroup.eq_iff_sub_mem]
  change (u.2 - offset ds u.1.val) - (v.2 - offset ds v.1.val) ∈
    AddSubgroup.zmultiples (charge ds : ZMod k) ↔ _
  rw [AddSubgroup.mem_zmultiples_iff]
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨-t, ?_⟩
    simp only [neg_smul]
    linear_combination ht
  · rintro ⟨t, ht⟩
    refine ⟨-t, ?_⟩
    simp only [neg_smul]
    linear_combination ht

/-- Explicit clock-route coordinates for a chosen return class. -/
def routeState (ds : List Bool) (start : ZMod k) (laps : ℤ) (i : Fin ds.length) :
    Fin ds.length × ZMod k :=
  (i, start + laps • (charge ds : ZMod k) + offset ds i.val)

omit [NeZero k] in
theorem route_step (ds : List Bool) (start : ZMod k) (laps : ℤ) (i : Fin ds.length) :
    step ds (routeState ds start laps i) =
      routeState ds start (if i.val+1 < ds.length then laps else laps+1) (nextIndex ds i) := by
  apply Prod.ext
  · rfl
  · have h := prefix_step ds i.val i.isLt
    by_cases hi : i.val+1 < ds.length
    · simp only [step, routeState, hi, if_true, nextIndex]
      change start + laps • (charge ds : ZMod k) + (charge (ds.take i.val) : ZMod k) +
        (tick ds[i.val] : ZMod k) =
        start + laps • (charge ds : ZMod k) + (charge (ds.take (i.val+1)) : ZMod k)
      rw [h, Int.cast_add]
      abel
    · have he : i.val+1 = ds.length := by omega
      have ht : charge ds = charge (ds.take i.val) + tick ds[i.val] := by
        simpa only [he, List.take_length] using h
      simp only [step, routeState, hi, if_false, nextIndex, dite_false]
      simp only [offset, List.take_zero, charge, Int.cast_zero]
      change start + laps • (charge ds : ZMod k) + (charge (ds.take i.val) : ZMod k) +
        (tick ds[i.val] : ZMod k) = start + (laps+1) • (charge ds : ZMod k) + 0
      rw [add_smul, one_smul, ht, Int.cast_add]
      abel

omit [NeZero k] in
theorem label_step (ds : List Bool) (s : Fin ds.length × ZMod k) :
    circuitLabel ds (step ds s) = circuitLabel ds s := by
  change QuotientAddGroup.mk (normalize ds (step ds s)).2 =
    QuotientAddGroup.mk (normalize ds s).2
  rw [normalized_step]
  by_cases hi : s.1.val+1 < ds.length
  · simp only [seamStep, normalize, Equiv.coe_fn_mk, hi, if_true]
  · simp only [seamStep, normalize, Equiv.coe_fn_mk, hi, if_false]
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    simpa only [add_sub_cancel_left] using AddSubgroup.mem_zmultiples (charge ds : ZMod k)

/-- Every phase in a label is attained with a bounded NONNEGATIVE lap count.
This removes any reliance on running the word backwards. -/
theorem labels_eq_forward_laps (ds : List Bool) (u v : Fin ds.length × ZMod k) :
    circuitLabel ds u = circuitLabel ds v ↔
      ∃ laps < k / splitCount (k:=k) ds,
        v.2 = u.2 + laps • (charge ds : ZMod k) +
          offset ds v.1.val - offset ds u.1.val := by
  constructor
  · intro h
    have hm := QuotientAddGroup.eq_iff_sub_mem.mp h.symm
    change (v.2 - offset ds v.1.val) - (u.2 - offset ds u.1.val) ∈
      AddSubgroup.zmultiples (charge ds : ZMod k) at hm
    rw [mem_zmultiples_iff_mem_range_addOrderOf] at hm
    obtain ⟨laps, hl, ht⟩ := Finset.mem_image.mp hm
    refine ⟨laps, ?_, ?_⟩
    · simpa only [period_formula] using Finset.mem_range.mp hl
    · linear_combination -ht
  · rintro ⟨laps, _, hl⟩
    apply (labels_eq_iff ds u v).mpr
    exact ⟨(laps:ℤ), by simpa only [natCast_zsmul] using hl⟩

/-- A constructive parametrization of every edge-sheet in a phase circuit.
The subgroup coordinate is exactly a possible complete-lap displacement. -/
def circuitFiberEquiv (ds : List Bool) (start : ZMod k) :
    (Fin ds.length × LapSubgroup (k:=k) ds) ≃
      {s : Fin ds.length × ZMod k // circuitLabel ds s = QuotientAddGroup.mk start} where
  toFun u := ⟨(u.1, start + u.2.val + offset ds u.1.val), by
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    change ((start + u.2.val + offset ds u.1.val) - offset ds u.1.val) - start ∈ _
    simpa only [add_sub_cancel_right, add_sub_cancel_left] using u.2.property⟩
  invFun s := (s.val.1, ⟨(s.val.2 - offset ds s.val.1.val) - start,
    QuotientAddGroup.eq_iff_sub_mem.mp s.property⟩)
  left_inv u := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      simp
  right_inv s := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change start + ((s.val.2 - offset ds s.val.1.val) - start) + offset ds s.val.1.val = s.val.2
      abel

theorem states_per_circuit (ds : List Bool) (start : ZMod k) :
    Nat.card {s : Fin ds.length × ZMod k // circuitLabel ds s = QuotientAddGroup.mk start} =
      ds.length * (k / splitCount (k:=k) ds) := by
  rw [← Nat.card_congr (circuitFiberEquiv ds start), Nat.card_prod,
    Nat.card_fin, Nat.card_zmultiples, period_formula]

omit [NeZero k] in
/-- For a nonempty lower circuit every counted phase class really occurs. -/
theorem label_surjective (ds : List Bool) (hne : ds ≠ []) :
    Function.Surjective (circuitLabel (k:=k) ds) := by
  intro q
  refine QuotientAddGroup.induction_on q ?_
  intro p
  refine ⟨(⟨0, List.length_pos_iff.mpr hne⟩, p), ?_⟩
  simp [circuitLabel, offset, charge]

end FiniteClock

/-- Changing one forward event into a backward event adds two clock ticks.
This is a phase law only: a valid lower circuit must still be supplied. -/
theorem flip_charge (as bs : List Bool) :
    charge (as ++ true :: bs) = charge (as ++ false :: bs) + 2 := by
  simp only [charge_append, charge, Bool.false_eq_true, if_false, if_true]
  ring

theorem same_counts_same_return {k : ℕ} (as bs : List Bool)
    (hL : as.length = bs.length) (hB : backwardCount as = backwardCount bs) (p : ZMod k) :
    transport as p = transport bs p := by
  simp only [transport_eq, charge_counts, hL, hB]

section Occupation
open Finset PacketPorts PacketOccupationBridge EganOccupationLift EganComponentGraph TwoMarkerPartition
variable {α : Type*} [DecidableEq α]

/-- Choose the clocks from the last three symbols of the supplied cyclic
phase. At the tiny orders without three symbols use the insertion fiber. -/
def phasedPacket (p : List α) (a b : α) : Finset (List α) :=
  match p.reverse with
  | y :: x :: z :: rs => packetCourses rs.reverse z x y a b
  | _ => occupationLift a (occupationLift b (rotationOrbit p))

theorem phasedPacket_eq (p : List α) (a b : α) (hp : p.Nodup)
    (ha : a ∉ p) (hb : b ∉ p) (hab : a ≠ b) :
    phasedPacket p a b = occupationLift a (occupationLift b (rotationOrbit p)) := by
  unfold phasedPacket
  split
  next y x z rs hr =>
    have he : p = rs.reverse ++ [z,x,y] := by
      have h := congrArg List.reverse hr
      simpa [List.reverse_cons, List.append_assoc] using h
    have rot : (y :: (rs.reverse ++ [z,x])).IsRotated p := by
      rw [he]
      simpa [List.append_assoc] using
        (List.isRotated_append (l:=[y]) (l':=rs.reverse ++ [z,x]))
    rw [packet_courses_fiber _ z x y a b (rot.nodup_iff.mpr hp)
      (fun h => ha (rot.perm.subset h)) (fun h => hb (rot.perm.subset h)) hab,
      orbit_eq_of_rotated rot]
  next => rfl

/-- The phase can be chosen FIRST: every cyclic clock setting executes an
exchange with the identical exact occupation, not just the identical size. -/
theorem phasedPacket_rotate (p : List α) (a b : α) (hp : p.Nodup)
    (ha : a ∉ p) (hb : b ∉ p) (hab : a ≠ b) (r : ℕ) :
    phasedPacket (p.rotate r) a b = phasedPacket p a b := by
  rw [phasedPacket_eq _ a b (List.nodup_rotate.mpr hp)
    (fun h => ha ((List.rotate_perm p r).subset h))
    (fun h => hb ((List.rotate_perm p r).subset h)) hab,
    phasedPacket_eq p a b hp ha hb hab]
  have hr : (p.rotate r).IsRotated p := List.IsRotated.symm ⟨r, rfl⟩
  rw [orbit_eq_of_rotated hr]

/-- Arbitrary per-parent clock phases AND exchange selections preserve full
occupation. The phases still determine the ports, so attachment is not erased. -/
theorem clocked_global_occupation (y a b : α) (A : List α)
    (hA : (y :: A).Nodup) (ha : a ∉ y :: A) (hb : b ∉ y :: A) (hab : a ≠ b)
    (phase : List α → ℕ) (backward : List α → Bool) :
    A.permutations.toFinset.biUnion (fun t =>
      if backward t then phasedPacket ((y :: t).rotate (phase t)) a b
      else rootedOrbits y (catalog a b t)) =
        (a :: b :: y :: A).permutations.toFinset := by
  calc
    _ = A.permutations.toFinset.biUnion (fun t => rootedOrbits y (catalog a b t)) := by
      apply biUnion_congr rfl
      intro t ht
      have perm : (y :: t).Perm (y :: A) :=
        (List.mem_permutations.mp (List.mem_toFinset.mp ht)).cons y
      have hn := perm.nodup_iff.mpr hA
      have hat : a ∉ y :: t := fun h => ha (perm.subset h)
      have hbt : b ∉ y :: t := fun h => hb (perm.subset h)
      rw [phasedPacket_rotate _ a b hn hat hbt hab,
        phasedPacket_eq _ a b hn hat hbt hab,
        ← rooted_catalog y a b t hn hat hbt hab]
      split <;> rfl
    _ = _ := by
      simpa only [Bool.false_eq_true, if_false] using
        global_course_occupation y a b A hA ha hb hab (fun _ => false)
end Occupation

#print axioms phaseAt_step
#print axioms normalized_step
#print axioms laps_then_prefix
#print axioms return_iff_divides
#print axioms circuit_count
#print axioms labels_eq_iff
#print axioms route_step
#print axioms label_step
#print axioms labels_eq_forward_laps
#print axioms states_per_circuit
#print axioms label_surjective
#print axioms flip_charge
#print axioms same_counts_same_return
#print axioms phasedPacket_rotate
#print axioms clocked_global_occupation
end Coeff2.Charlieplex.ClockRouting
