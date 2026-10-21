import Coeff2.CharliePhaseDetour

/-!
# Occupation algebra of the observed non-whole packet

The literal C++ audit finds M = (n-3) I + 1 (e_a+e_b)^T at n=4..26.
This module proves the algebra of that explicit operator and the atomic-trade
consequence of its ownership support. It does NOT prove that every literal
packet has that matrix for every n; that generator-to-matrix bridge remains.
Nor is this matrix the boundary transport operator or a completion theorem.
-/
namespace Coeff2.Charlieplex.NonwholeOccupation

variable {ι : Type*}

/-- The two distinguished columns are the long pieces. -/
def projection (a b : ι) (x : ι → ℚ) : ι → ℚ :=
  fun _ => (x a + x b) / 2

/-- Matrix action of r I + 1 (e_a+e_b)^T, with r=n-3 in the packet. -/
def transfer (r : ℚ) (a b : ι) (x : ι → ℚ) : ι → ℚ :=
  fun i => r * x i + (x a + x b)

theorem projection_idempotent (a b : ι) (x : ι → ℚ) :
    projection a b (projection a b x) = projection a b x := by
  funext i
  simp only [projection]
  ring

/-- This is generally an oblique projection, not an orthogonal quantum one. -/
theorem transfer_split (r : ℚ) (a b : ι) (x : ι → ℚ) :
    transfer r a b x = fun i =>
      r * (x i - projection a b x i) + (r + 2) * projection a b x i := by
  funext i
  simp only [transfer, projection]
  ring

theorem transfer_differences (r : ℚ) (a b : ι) (x : ι → ℚ) (i j : ι) :
    transfer r a b x i - transfer r a b x j = r * (x i - x j) := by
  simp only [transfer]
  ring

theorem transfer_collective (r : ℚ) (a b : ι) (x : ι → ℚ) :
    transfer r a b x a + transfer r a b x b = (r + 2) * (x a + x b) := by
  simp only [transfer]
  ring

theorem transfer_constant (r c : ℚ) (a b : ι) :
    transfer r a b (fun _ => c) = fun _ => (r + 2) * c := by
  funext i
  simp only [transfer]
  ring

theorem transfer_zero_sum (r : ℚ) (a b : ι) (x : ι → ℚ)
    (hx : x a + x b = 0) : transfer r a b x = fun i => r * x i := by
  funext i
  simp [transfer, hx]

def transferPower (r : ℚ) (a b : ι) : ℕ → (ι → ℚ) → (ι → ℚ)
  | 0, x => x
  | k + 1, x => transfer r a b (transferPower r a b k x)

/-- Formal powers of the count matrix. Not a composability theorem for packets. -/
theorem transfer_power_split (r : ℚ) (a b : ι) (x : ι → ℚ) (k : ℕ) (i : ι) :
    transferPower r a b k x i =
      r ^ k * (x i - projection a b x i) + (r + 2) ^ k * projection a b x i := by
  induction k generalizing i with
  | zero =>
    simp only [transferPower, pow_zero, one_mul]
    ring
  | succ k ih =>
    simp only [transferPower, transfer, ih, pow_succ, projection]
    ring

/-- Support of the literal old/new ownership incidence found in the audit. -/
def ownershipSupport (a b i j : ι) : Prop := i = j ∨ j = a ∨ j = b

/-- For each individual orbit, removing its old owner must match adding its
new owner. A hub long piece meets every old piece, forcing one common choice. -/
theorem occupation_trade_atomic (a b : ι) (removed added : ι → ℤ)
    (h : ∀ i j, ownershipSupport a b i j → removed i = added j) :
    (∀ i, removed i = added a) ∧ (∀ j, added j = added a) := by
  constructor
  · intro i
    exact h i a (Or.inr (Or.inl rfl))
  · intro j
    exact (h j j (Or.inl rfl)).symm.trans (h j a (Or.inr (Or.inl rfl)))

/-- In the Boolean selection case, any selected piece forces the whole bundle. -/
theorem selected_piece_forces_bundle (a b : ι) (removed added : ι → ℤ)
    (h : ∀ i j, ownershipSupport a b i j → removed i = added j)
    (j : ι) (hj : added j = 1) :
    (∀ i, removed i = 1) ∧ (∀ i, added i = 1) := by
  obtain ⟨hr, ha⟩ := occupation_trade_atomic a b removed added h
  have hone : added a = 1 := (ha j).symm.trans hj
  exact ⟨fun i => (hr i).trans hone, fun i => (ha i).trans hone⟩

/-- The earlier literal-piece +2 cost identity extends additively to k packets.
Both overlap totals must come from actual connected arrangements. -/
theorem bundle_shorter_iff (internal oldOverlap newOverlap k : ℤ) :
    internal + 2 * k - newOverlap < internal - oldOverlap ↔
      2 * k < newOverlap - oldOverlap := by omega

#print axioms projection_idempotent
#print axioms transfer_split
#print axioms transfer_differences
#print axioms transfer_collective
#print axioms transfer_constant
#print axioms transfer_zero_sum
#print axioms transfer_power_split
#print axioms occupation_trade_atomic
#print axioms selected_piece_forces_bundle
#print axioms bundle_shorter_iff

end Coeff2.Charlieplex.NonwholeOccupation
