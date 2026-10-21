import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

/-! Algebra of rectangular lift mismatches. Eigenvector hypotheses are
explicit. This does not assume literal deletion is an unconditional clock
intertwiner or supply an occupation-preserving cheap construction. -/
namespace Coeff2.Charlieplex.LiftEigenoperators
variable {I J R : Type*} [Fintype I] [Fintype J] [CommRing R]

def outer (u : I → R) (v : J → R) : Matrix I J R := fun i j => u i * v j
def defect (upper : Matrix I I R) (lower : Matrix J J R)
    (lift : Matrix I J R) : Matrix I J R := upper * lift - lift * lower

/-- A right upper eigenvector and LEFT lower eigenvector give a rectangular
eigenoperator. No common dimension or simultaneous diagonalization needed. -/
theorem rank_one_mode (upper : Matrix I I R) (lower : Matrix J J R)
    (u : I → R) (v : J → R) (a b : R)
    (hu : ∀ i, (∑ k, upper i k * u k) = a * u i)
    (hv : ∀ j, (∑ k, v k * lower k j) = b * v j) :
    defect upper lower (outer u v) =
      fun i j => (a-b) * (u i * v j) := by
  ext i j
  simp only [defect, Matrix.sub_apply, Matrix.mul_apply, outer]
  calc
    (∑ k, upper i k * (u k * v j)) - (∑ k, (u i * v k) * lower k j) =
        (∑ k, upper i k * u k) * v j - u i * (∑ k, v k * lower k j) := by
      rw [Finset.sum_mul, Finset.mul_sum]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro k hk <;> ring
    _ = (a-b) * (u i * v j) := by rw [hu i, hv j]; ring

theorem matched_mode (upper : Matrix I I R) (lower : Matrix J J R)
    (u : I → R) (v : J → R) (a : R)
    (hu : ∀ i, (∑ k, upper i k * u k) = a * u i)
    (hv : ∀ j, (∑ k, v k * lower k j) = a * v j) :
    upper * outer u v = outer u v * lower := by
  have h := rank_one_mode upper lower u v a a hu hv
  have hz : defect upper lower (outer u v) = 0 := by
    ext i j
    simpa using congrFun (congrFun h i) j
  exact sub_eq_zero.mp hz

#print axioms rank_one_mode
#print axioms matched_mode
end Coeff2.Charlieplex.LiftEigenoperators
