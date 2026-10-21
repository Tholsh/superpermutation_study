import Coeff2.CharlieClockRouting

/-!
# One further clock level, including literal connector clocks

The recursion theorem allows a state-dependent clock increment. The literal
bridge below subdivides a forward boundary edge at every insertion position.
It is valid even when the emitted symbol equals a symbol in the boundary.
In particular the wrapped path may have a repeated-symbol intermediate frame.
This proves a recursive routing/occupation lift, not a short-length bound.
-/
namespace Coeff2.Charlieplex.RecursiveClockLift
open SignedBoundaryLift PacketPorts

section Tower
variable {X : Type*} {k : ℕ}

def liftStep (T : X → X) (delta : X → ZMod k) (s : X × ZMod k) : X × ZMod k :=
  (T s.1, s.2 + delta s.1)

def accumulated (T : X → X) (delta : X → ZMod k) (x : X) : ℕ → ZMod k
  | 0 => 0
  | t+1 => accumulated T delta x t + delta (T^[t] x)

theorem lift_iterate (T : X → X) (delta : X → ZMod k) (x : X) (j : ZMod k) (t : ℕ) :
    (liftStep T delta)^[t] (x,j) = (T^[t] x, j + accumulated T delta x t) := by
  induction t with
  | zero => simp [accumulated]
  | succ t ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [liftStep, accumulated, Function.iterate_succ_apply']
    congr 1
    abel

/-- The lower-level transition is now a function, not an externally supplied
list of decisions; this identity persists for every number of steps. -/
theorem projection_iterate (T : X → X) (delta : X → ZMod k) (s : X × ZMod k) (t : ℕ) :
    ((liftStep T delta)^[t] s).1 = T^[t] s.1 := by
  rw [lift_iterate]

theorem return_lift (T : X → X) (delta : X → ZMod k) (x : X) (j : ZMod k)
    (period : ℕ) (h : T^[period] x = x) :
    (liftStep T delta)^[period] (x,j) = (x, j + accumulated T delta x period) := by
  rw [lift_iterate, h]

theorem repeated_return (T : X → X) (delta : X → ZMod k) (x : X) (j : ZMod k)
    (period laps : ℕ) (h : T^[period] x = x) :
    ((liftStep T delta)^[period])^[laps] (x,j) =
      (x, j + laps • accumulated T delta x period) := by
  induction laps with
  | zero => simp
  | succ laps ih =>
    rw [Function.iterate_succ_apply', ih, return_lift T delta x _ period h,
      succ_nsmul]
    congr 1
    abel

/-- The next clock may depend on the ENTIRE state of the preceding clock.
No independence of the phase levels is assumed. -/
theorem two_level_projection {h : ℕ} (T : X → X) (delta : X → ZMod k)
    (epsilon : X × ZMod k → ZMod h) (s : (X × ZMod k) × ZMod h) (t : ℕ) :
    (((liftStep (liftStep T delta) epsilon)^[t] s).1).1 = T^[t] s.1.1 := by
  rw [projection_iterate, projection_iterate]

theorem unit_return_covers [NeZero k] (T : X → X) (delta : X → ZMod k)
    (x : X) (j : ZMod k) (period : ℕ) (hret : T^[period] x = x)
    (hcover : ∀ y : X, ∃ i < period, T^[i] x = y)
    (hu : IsUnit (accumulated T delta x period)) (y : X) (z : ZMod k) :
    ∃ i < period, ∃ laps < k,
      (liftStep T delta)^[i] (((liftStep T delta)^[period])^[laps] (x,j)) = (y,z) := by
  obtain ⟨i, hi, hy⟩ := hcover y
  obtain ⟨u, hu⟩ := hu
  let v : ZMod k := (z - j - accumulated T delta x i) * (↑u⁻¹ : ZMod k)
  refine ⟨i, hi, v.val, ZMod.val_lt v, ?_⟩
  rw [repeated_return T delta x j period v.val hret, lift_iterate, hy]
  apply Prod.ext
  · rfl
  · change j + v.val • accumulated T delta x period + accumulated T delta x i = z
    rw [← hu, nsmul_eq_mul, ZMod.natCast_zmod_val]
    dsimp only [v]
    rw [mul_assoc, Units.inv_mul, mul_one]
    ring

/-- A bounded neutral prefix can always turn the return clock into a
one-tick clock. This is an existence bound; native construction may choose
a cheaper coprime adjustment such as minus one instead. -/
theorem neutral_prefix_exists {k : ℕ} [NeZero k] (d : ZMod k) :
    ∃ t < k, d - (t : ZMod k) = 1 := by
  refine ⟨(d-1).val, ZMod.val_lt _, ?_⟩
  rw [ZMod.natCast_zmod_val]
  ring

end Tower

section Literal
variable {α : Type*}

/-- A literal append, retaining a boundary of the same positive width. -/
def appendStep (frame : List α) (a : α) : List α := frame.tail ++ [a]

def emit : List α → List α → List α
  | frame, [] => frame
  | frame, a :: rest => emit (appendStep frame a) rest

def nextSlot (width i : ℕ) : ℕ := if i = 0 then width else i-1

/-- Crossing the inserted marker emits the lower symbol and then the marker.
Other slots emit only the lower symbol. -/
def slotPayload (b z : α) (i : ℕ) : List α := if i = 0 then [z,b] else [z]

theorem interior_literal (x b z : α) (s : List α) (j : ℕ) (hj : j ≤ s.length) :
    emit ((x :: s).insertIdx (j+1) b) [z] = (s ++ [z]).insertIdx j b := by
  rw [PacketOccupationBridge.insert_append b s [z] j hj]
  simp [emit, appendStep]

/-- No freshness condition on z is needed: rotation returns are included. -/
theorem wrapped_literal (x b z : α) (s : List α) :
    emit ((x :: s).insertIdx 0 b) [z,b] = (s ++ [z]).insertIdx (s.length+1) b := by
  rw [show s.length+1 = (s ++ [z]).length by simp,
    PacketOccupationBridge.insert_end]
  simp [emit, appendStep, List.append_assoc]

theorem literal_next_level (x b z : α) (s : List α) (i : ℕ) (hi : i ≤ s.length+1) :
    emit ((x :: s).insertIdx i b) (slotPayload b z i) =
      (s ++ [z]).insertIdx (nextSlot (s.length+1) i) b := by
  cases i with
  | zero => simpa [slotPayload, nextSlot] using wrapped_literal x b z s
  | succ j =>
    simpa [slotPayload, nextSlot] using interior_literal x b z s j (by omega)

theorem nextSlot_bound (width i : ℕ) (hi : i ≤ width) : nextSlot width i ≤ width := by
  unfold nextSlot
  split <;> omega

/-- The literal subdivision is the same minus-one insertion clock at the
next radix, including the two-symbol wrapped case. -/
theorem nextSlot_clock (width i : ℕ) (hi : i ≤ width) :
    (nextSlot width i : ZMod (width+1)) = (i : ZMod (width+1)) - 1 := by
  by_cases hz : i = 0
  · subst i
    simp only [nextSlot, if_true, Nat.cast_zero, zero_sub]
    have h := ZMod.natCast_self (width+1)
    push_cast at h
    linear_combination h
  · rw [nextSlot, if_neg hz, Nat.cast_sub (by omega), Nat.cast_one]

/-- The edge list is exactly the insertion family of the original transition
word. It preserves multiplicities: repeated frames are not merged away. -/
theorem lifted_edge_catalog (x b z : α) (s : List α) :
    insertions b (x :: (s ++ [z])) =
      [b :: x :: (s ++ [z])] ++
      (insertions b s).map (fun q => x :: (q ++ [z])) ++
      [(x :: (s ++ [z])) ++ [b]] := by
  simp [insertions, insertions_snoc, List.map_map, Function.comp_def]

theorem insertion_count (b : α) (s : List α) : (insertions b s).length = s.length+1 := by
  induction s with
  | nil => rfl
  | cons x s ih => simp [insertions, ih]

theorem lifted_edge_count (x b z : α) (s : List α) :
    (insertions b (x :: (s ++ [z]))).length = s.length+3 := by
  simp [insertion_count, Nat.add_assoc]

theorem payload_cost (b z : α) (i : ℕ) :
    (slotPayload b z i).length = 1 + if i = 0 then 1 else 0 := by
  by_cases h : i = 0 <;> simp [slotPayload, h]

theorem all_slots_cost (b z : α) (width : ℕ) :
    ((List.range (width+1)).map (fun i => (slotPayload b z i).length)).sum = width+2 := by
  rw [List.range_succ_eq_map]
  simp [slotPayload, List.map_map, Function.comp_def, Nat.add_comm]

/-- This is a genuine literal recursion, not merely a projection defined to
commute. It applies to any supplied lower transition with a nonempty frame. -/
theorem encoded_step {X : Type*} (T : X → X) (head symbol : X → α)
    (tail : X → List α) (width : ℕ)
    (ht : ∀ x, (tail x).length + 1 = width)
    (hT : ∀ x, head (T x) :: tail (T x) = tail x ++ [symbol x])
    (b : α) (x : X) (i : ℕ) (hi : i ≤ width) :
    emit ((head x :: tail x).insertIdx i b) (slotPayload b (symbol x) i) =
      (head (T x) :: tail (T x)).insertIdx (nextSlot width i) b := by
  rw [hT x, ← ht x]
  exact literal_next_level (head x) b (symbol x) (tail x) i (by rw [ht x]; exact hi)

end Literal

#print axioms lift_iterate
#print axioms projection_iterate
#print axioms repeated_return
#print axioms two_level_projection
#print axioms unit_return_covers
#print axioms neutral_prefix_exists
#print axioms literal_next_level
#print axioms nextSlot_clock
#print axioms lifted_edge_catalog
#print axioms all_slots_cost
#print axioms encoded_step
end Coeff2.Charlieplex.RecursiveClockLift
