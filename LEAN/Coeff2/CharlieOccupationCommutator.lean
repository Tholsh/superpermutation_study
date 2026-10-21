import Mathlib.Tactic

/-! Literal occupation multiplies state amplitudes pointwise. Its failure
to commute with clock transport is an exact difference of occupation bits,
not a claim of quantum hardware or a cheap superpermutation construction. -/
namespace Coeff2.Charlieplex.OccupationCommutator
variable {X K : Type*} [Ring K]

def transport (next : X → X) (v : X → K) : X → K := fun x => v (next x)
def diagonal (mask : X → K) (v : X → K) : X → K := fun x => mask x * v x

theorem commutator_entry (next : X → X) (mask v : X → K) (x : X) :
    transport next (diagonal mask v) x - diagonal mask (transport next v) x =
      (mask (next x) - mask x) * v (next x) := by
  simp only [transport, diagonal, sub_mul]

/-- Commutation on every amplitude is equivalent to invariant occupation.
This statement does not need finite state spaces or diagonalizability. -/
theorem commute_iff (next : X → X) (mask : X → K) :
    (∀ v, transport next (diagonal mask v) = diagonal mask (transport next v)) ↔
      ∀ x, mask (next x) = mask x := by
  constructor
  · intro h x
    have he := congrFun (h (fun _ => 1)) x
    simpa [transport, diagonal] using he
  · intro h v
    funext x
    simp [transport, diagonal, h x]

omit [Ring K] in
theorem invariant_iterates (next : X → X) (mask : X → K)
    (h : ∀ x, mask (next x) = mask x) (k : ℕ) (x : X) :
    mask (next^[k] x) = mask x := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', h, ih]

/-- Therefore a commuting Boolean occupation mask must have one fixed bit
throughout every clock orbit. Partial occupation cannot commute. -/
theorem partial_orbit_not_commuting [Nontrivial K] (next : X → X)
    (occupied : X → Bool) (x : X) (k : ℕ)
    (h : occupied (next^[k] x) ≠ occupied x) :
    ¬ (∀ v, transport next (diagonal (fun y => if occupied y then (1:K) else 0) v) =
      diagonal (fun y => if occupied y then (1:K) else 0) (transport next v)) := by
  intro hc
  have hi := invariant_iterates next (fun y => if occupied y then (1:K) else 0)
    ((commute_iff next _).mp hc) k x
  cases ha : occupied (next^[k] x) <;> cases hb : occupied x <;>
    simp_all

#print axioms commute_iff
#print axioms partial_orbit_not_commuting
end Coeff2.Charlieplex.OccupationCommutator
