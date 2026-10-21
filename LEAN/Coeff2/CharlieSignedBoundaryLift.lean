import Coeff2.CharliePacketOccupationBridge
import Mathlib.Data.ZMod.Basic

/-!
# Signed insertion-phase transport from literal packet ports

Forward lower edges use ordinary pieces; backward edges use the observed
non-whole packet. Their sheet transports are -1 and +1 respectively.
This file proves the literal local routing and its modular composition.
The imported PacketOccupationBridge now proves exact all-order occupation
of the short/long course programs, not just their abstract catalog counts.
It does not assert that an arbitrary lower cycle covers every parent fiber,
nor that a set of resulting circuits admits an optimal global ordering.
-/
namespace Coeff2.Charlieplex.SignedBoundaryLift
open PacketPorts
variable {α : Type*}

def insertions (b : α) : List α → List (List α)
  | [] => [[b]]
  | x :: xs => (b :: x :: xs) :: (insertions b xs).map (List.cons x)

theorem insertions_snoc (b z : α) (s : List α) :
    insertions b (s ++ [z]) =
      (insertions b s).map (fun q => q ++ [z]) ++ [s ++ [z,b]] := by
  induction s with
  | nil => rfl
  | cons x s ih => simp [insertions, ih, List.map_map, Function.comp_def]

theorem insertion_fronts (b z : α) (s : List α) :
    (insertions b (s ++ [z])).map List.dropLast =
      insertions b s ++ [s ++ [z]] := by
  rw [insertions_snoc]
  simp [List.map_map, Function.comp_def]

theorem insertion_backs (b x : α) (s : List α) :
    (insertions b (x :: s)).map List.tail = [x :: s] ++ insertions b s := by
  simp [insertions, List.map_map, Function.comp_def]

/-- An ordinary upper piece is a literal de Bruijn edge on its middle word t.
The exit is the previously proved full-course execution, not an assumed port. -/
theorem ordinary_reduced_ports (t : List α) (a h : α) :
    ((t ++ [h]) ++ [a]).take (t.length - 1) = t.dropLast ∧
      (finish (advance ((t ++ [h]) ++ [a]) t.length) 0).drop 3 = t.tail := by
  constructor
  · rw [List.append_assoc, List.take_append_of_le_length (by omega)]
    exact List.dropLast_eq_take.symm
  · rw [fixed_clock_exit]
    cases t <;> rfl

/-- Interior forward sheet j becomes sheet j-1, by literal list equality. -/
theorem forward_interior (x z b : α) (r s : List α) :
    (x :: (r ++ b :: (s ++ [z]))).dropLast = x :: (r ++ b :: s) ∧
      (x :: (r ++ b :: (s ++ [z]))).tail = r ++ b :: (s ++ [z]) := by
  constructor
  · have he : x :: (r ++ b :: (s ++ [z])) = (x :: (r ++ b :: s)) ++ [z] := by simp
    rw [he, List.dropLast_append_of_ne_nil (by simp)]
    simp only [List.dropLast_singleton, List.append_nil]
  · rfl

/-- The wrapped forward sheet passes through the one b-free intermediate
vertex; its two ordinary pieces take the front insertion to the back. -/
theorem forward_wrap (x z b : α) (s : List α) :
    (b :: x :: (s ++ [z])).dropLast = b :: x :: s ∧
    (b :: x :: (s ++ [z])).tail = x :: (s ++ [z]) ∧
    ((x :: (s ++ [z])) ++ [b]).dropLast = x :: (s ++ [z]) ∧
    ((x :: (s ++ [z])) ++ [b]).tail = s ++ [z,b] := by
  have h1 : (b :: x :: (s ++ [z])).dropLast = b :: x :: s := by
    change ((b :: x :: s) ++ [z]).dropLast = _
    rw [List.dropLast_append_of_ne_nil (by simp)]
    simp only [List.dropLast_singleton, List.append_nil]
  have h2 : ((x :: (s ++ [z])) ++ [b]).dropLast = x :: (s ++ [z]) := by
    rw [List.dropLast_append_of_ne_nil (by simp)]
    simp only [List.dropLast_singleton, List.append_nil]
  exact ⟨h1, rfl, h2, by simp⟩

theorem short_reduced_ports (q : List α) (z x y a : α) :
    (q ++ [z,x,y,a]).take (q.length + 1) = q ++ [z] ∧
      (finish (advance (q ++ [z,x,y,a]) q.length) 0).drop 3 = y :: q := by
  constructor
  · rw [List.take_append]; simp
  · rw [short_exit]; rfl

/-- Every short backward piece sends an insertion in s to the same insertion
one position later, because y is prepended. -/
theorem backward_interior (r s : List α) (b y z : α) :
    (r ++ b :: s) ++ [z] = r ++ b :: (s ++ [z]) ∧
      y :: (r ++ b :: s) = (y :: r) ++ b :: s := by
  simp

/-- The two long pieces are exactly the wrapped backward sheet. -/
theorem backward_wrap (s : List α) (z x y a b : α) :
    (s ++ [z,b,x,y,a]).take (s.length + 2) = s ++ [z,b] ∧
    (longAExit s z x y a b).drop 3 = y :: (s ++ [z]) ∧
    (y :: (s ++ [z,x,a,b])).take (s.length + 2) = y :: (s ++ [z]) ∧
    (longBExit s z x y a b).drop 3 = b :: y :: s := by
  rw [longA_exit, longB_exit]
  simp only [List.drop_succ_cons, List.drop_zero, List.take_succ_cons]
  constructor
  · rw [List.take_append]; simp
  · refine ⟨trivial, ?_, trivial⟩
    rw [List.take_append]; simp

section Boundary
variable {G : Type*} [AddCommGroup G]
private theorem list_sum_sub {β : Type*} (xs : List β) (f g : β → G) :
    (xs.map (fun x => f x - g x)).sum = (xs.map f).sum - (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; abel
def insertionSum (b : α) (f : List α → G) (s : List α) : G :=
  ((insertions b s).map f).sum

/-- Ordinary port imbalance is the insertion lift of the lower forward edge.
The b-free intermediate vertex cancels exactly. -/
theorem forward_boundary (b x z : α) (s : List α) (f : List α → G) :
    ((insertions b (x :: (s ++ [z]))).map
      (fun q => f q.dropLast - f q.tail)).sum =
      insertionSum b f (x :: s) - insertionSum b f (s ++ [z]) := by
  rw [list_sum_sub]
  have hf := congrArg (fun qs : List (List α) => (qs.map f).sum)
    (insertion_fronts b z (x :: s))
  have hb := congrArg (fun qs : List (List α) => (qs.map f).sum)
    (insertion_backs b x (s ++ [z]))
  simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append,
    List.sum_cons, List.sum_nil, add_zero, List.map_map, Function.comp_def] at hf hb
  change _ = _ at hf
  rw [show x :: (s ++ [z]) = (x :: s) ++ [z] by rfl] at hb ⊢
  rw [hf, hb]
  unfold insertionSum
  abel

/-- The packet's short ports and two long ports have the insertion lift of
one backward lower edge as their complete boundary. No term is approximated. -/
theorem backward_boundary (b y z : α) (s : List α) (f : List α → G) :
    ((insertions b s).map (fun q => f (q ++ [z]) - f (y :: q))).sum +
      (f (s ++ [z,b]) - f (y :: (s ++ [z]))) +
      (f (y :: (s ++ [z])) - f (b :: y :: s)) =
      insertionSum b f (s ++ [z]) - insertionSum b f (y :: s) := by
  simp only [insertionSum, insertions_snoc, insertions, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil,
    add_zero, List.map_map, Function.comp_def, list_sum_sub]
  abel
end Boundary

def charge : List Bool → ℤ
  | [] => 0
  | d :: ds => (if d then 1 else -1) + charge ds

def backwardCount : List Bool → ℕ
  | [] => 0
  | d :: ds => (if d then 1 else 0) + backwardCount ds

theorem charge_counts (ds : List Bool) :
    charge ds = 2 * (backwardCount ds : ℤ) - (ds.length : ℤ) := by
  induction ds with
  | nil => rfl
  | cons d ds ih => cases d <;> simp [charge, backwardCount, ih] <;> ring

def transport {k : ℕ} (ds : List Bool) (phase : ZMod k) : ZMod k :=
  match ds with
  | [] => phase
  | d :: ds => transport ds (phase + if d then 1 else -1)

theorem transport_eq {k : ℕ} (ds : List Bool) (phase : ZMod k) :
    transport ds phase = phase + (charge ds : ZMod k) := by
  induction ds generalizing phase with
  | nil => simp [transport, charge]
  | cons d ds ih => cases d <;> simp [transport, charge, ih] <;> ring

theorem repeated_transport {k : ℕ} (ds : List Bool) (phase : ZMod k) (r : ℕ) :
    (transport ds)^[r] phase = phase + r • (charge ds : ZMod k) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply', transport_eq, ih, succ_nsmul]
    abel

/-- A proven phase period, not an assumed number of connected graph pieces. -/
theorem phase_period (k d : ℕ) (hk : k ≠ 0) :
    addOrderOf (d : ZMod k) = k / Nat.gcd k d := ZMod.addOrderOf_coe d hk

def block (n : ℕ) : List Bool := List.replicate (n - 5) false ++ [true]

theorem block_charge (r : ℕ) : charge (block (r + 5)) = 1 - (r : ℤ) := by
  have hc : ∀ j : ℕ, charge (List.replicate j false ++ [true]) = 1 - (j : ℤ) := by
    intro j
    induction j with
    | zero => simp [charge]
    | succ j ih => simp [List.replicate_succ, charge, ih]; ring
  simpa [block] using hc r

theorem witness_eight_transport (p : ZMod 5) :
    (transport (block 8))^[4] p = p + 2 := by
  rw [repeated_transport]
  norm_num [block, charge, List.replicate_succ]
  decide +kernel

theorem nine_transport_splits (p : ZMod 6) :
    (transport (block 9))^[10] p = p := by
  rw [repeated_transport]
  norm_num [block, charge, List.replicate_succ]
  decide +kernel

theorem eight_phase_period : addOrderOf (2 : ZMod 5) = 5 := by
  have h := phase_period 5 2 (by decide)
  norm_num at h ⊢
  exact h

/-- Accounting for a certified assembly into g cost-three circuits. The
equation is an exact ledger, not an assertion that such a circuit cover exists. -/
theorem lifted_cycle_length_ledger (n parents packets circuits : ℤ) :
    parents * (n-2) * (n*n+n-3) + 2*packets -
      (parents*(n-2)-circuits)*(n-3) =
      parents*(n-2)*n*n + 2*packets + circuits*(n-3) := by ring

#print axioms ordinary_reduced_ports
#print axioms forward_wrap
#print axioms backward_wrap
#print axioms forward_boundary
#print axioms backward_boundary
#print axioms charge_counts
#print axioms transport_eq
#print axioms repeated_transport
#print axioms phase_period
#print axioms witness_eight_transport
#print axioms nine_transport_splits
#print axioms eight_phase_period
#print axioms lifted_cycle_length_ledger
end Coeff2.Charlieplex.SignedBoundaryLift
