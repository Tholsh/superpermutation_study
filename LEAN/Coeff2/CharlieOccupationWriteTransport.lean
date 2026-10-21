import Coeff2.CharlieOccupationCommutator

/-! One literal occupation write has an exact local operator update.
This is not a claim that all future completion obligations are local. -/
namespace Coeff2.Charlieplex.OccupationWriteTransport
open OccupationCommutator
variable {X K : Type*} [DecidableEq X] [Ring K]

def point (y : X) (a : K) (v : X → K) : X → K :=
  fun x => if x=y then a*v y else 0

theorem diagonal_write (mask : X → K) (y : X) (a : K) (v : X → K) :
    diagonal (Function.update mask y a) v - diagonal mask v =
      point y (a-mask y) v := by
  funext x
  by_cases h : x=y
  · subst x; simp [diagonal, point, sub_mul]
  · simp [diagonal, point, h]

/-- The change in the clock/occupation commutator is R times one point
operator minus that point operator times R. No dense diagonalization needed. -/
theorem commutator_write (next : X → X) (mask : X → K) (y : X)
    (a : K) (v : X → K) :
    (transport next (diagonal (Function.update mask y a) v) -
      diagonal (Function.update mask y a) (transport next v)) -
    (transport next (diagonal mask v) - diagonal mask (transport next v)) =
    transport next (point y (a-mask y) v) -
      point y (a-mask y) (transport next v) := by
  have h₁ := congrFun (diagonal_write mask y a v)
  have h₂ := congrFun (diagonal_write mask y a (transport next v))
  funext x
  have he₁ := h₁ (next x)
  have he₂ := h₂ x
  simp only [Pi.sub_apply, transport] at *
  rw [← he₁, ← he₂]
  abel

/-- In a reversible clock the update is supported at the written position
and its immediate predecessor. This does not bound global obstruction. -/
theorem write_support (next : X ≃ X) (mask : X → K) (y : X)
    (a : K) (v : X → K) (x : X) (hx : x≠y) (hp : x≠next.symm y) :
    (transport next (point y (a-mask y) v) -
      point y (a-mask y) (transport next v)) x = 0 := by
  have hn : next x≠y := by
    intro h
    apply hp
    exact next.injective (by simpa using h)
  simp [transport, point, hx, hn]

#print axioms diagonal_write
#print axioms commutator_write
#print axioms write_support
end Coeff2.Charlieplex.OccupationWriteTransport
