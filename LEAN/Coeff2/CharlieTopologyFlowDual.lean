import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-! Exact integer primal/dual certificates for the remaining topology flow.
Every matrix row and column may be literal, compressed, or a free endpoint.
This does not assume global connectivity: the protected spanning tree and
literal expansion supply that separate certificate in the native model.
-/
namespace Coeff2.Charlieplex.TopologyFlowDual
variable {V E : Type*} [Fintype V] [Fintype E]

def cost (c x : E → ℤ) : ℤ := ∑ e, c e*x e
def residual (A : V → E → ℤ) (c : E → ℤ) (y : V → ℤ) (e : E) : ℤ :=
  c e - ∑ v, y v*A v e
def contribution (r l u : ℤ) : ℤ := if 0 ≤ r then r*l else r*u
def bound (A : V → E → ℤ) (c l u : E → ℤ) (b y : V → ℤ) : ℤ :=
  (∑ v, y v*b v) + ∑ e, contribution (residual A c y e) (l e) (u e)

theorem contribution_le (r l x u : ℤ) (hl : l ≤ x) (hu : x ≤ u) :
    contribution r l u ≤ r*x := by
  unfold contribution
  split_ifs with hr
  · exact mul_le_mul_of_nonneg_left hl hr
  · exact mul_le_mul_of_nonpos_left hu (le_of_lt (lt_of_not_ge hr))

theorem flow_cost_identity (A : V → E → ℤ) (c x : E → ℤ) (b y : V → ℤ)
    (balance : ∀ v, (∑ e, A v e*x e) = b v) :
    cost c x = (∑ v, y v*b v) + ∑ e, residual A c y e*x e := by
  classical
  have hc : ∀ e, c e = (∑ v, y v*A v e) + residual A c y e := by
    intro e
    unfold residual
    ring
  unfold cost
  calc
    (∑ e, c e*x e) = ∑ e, ((∑ v, y v*A v e)*x e + residual A c y e*x e) := by
      apply Finset.sum_congr rfl
      intro e _
      rw [hc e]
      ring
    _ = (∑ e, ∑ v, y v*(A v e*x e)) + ∑ e, residual A c y e*x e := by
      simp_rw [Finset.sum_add_distrib, Finset.sum_mul, mul_assoc]
    _ = (∑ v, ∑ e, y v*(A v e*x e)) + ∑ e, residual A c y e*x e := by
      rw [Finset.sum_comm]
    _ = (∑ v, y v*b v) + ∑ e, residual A c y e*x e := by
      congr 1
      apply Finset.sum_congr rfl
      intro v _
      rw [← Finset.mul_sum, balance v]

theorem dual_lower_bound (A : V → E → ℤ) (c l x u : E → ℤ) (b y : V → ℤ)
    (balance : ∀ v, (∑ e, A v e*x e) = b v)
    (limits : ∀ e, l e ≤ x e ∧ x e ≤ u e) :
    bound A c l u b y ≤ cost c x := by
  unfold bound
  have hsum : (∑ e, contribution (residual A c y e) (l e) (u e)) ≤
      ∑ e, residual A c y e*x e := by
    apply Finset.sum_le_sum
    intro e _
    exact contribution_le _ _ _ _ (limits e).1 (limits e).2
  calc
    _ ≤ (∑ v, y v*b v) + ∑ e, residual A c y e*x e := add_le_add le_rfl hsum
    _ = cost c x := (flow_cost_identity A c x b y balance).symm

theorem certified_minimum (A : V → E → ℤ) (c l x z u : E → ℤ) (b y : V → ℤ)
    (certificate : cost c x = bound A c l u b y)
    (zBalance : ∀ v, (∑ e, A v e*z e) = b v)
    (zLimits : ∀ e, l e ≤ z e ∧ z e ≤ u e) : cost c x ≤ cost c z := by
  rw [certificate]
  exact dual_lower_bound A c l z u b y zBalance zLimits

theorem contribution_sensitivity (r l next u : ℤ) :
    contribution r next u = contribution r l u + max r 0*(next-l) := by
  by_cases hr : 0 ≤ r
  · simp only [contribution, if_pos hr, max_eq_left hr]
    ring
  · have hn : r ≤ 0 := le_of_lt (lt_of_not_ge hr)
    simp [contribution, hr, max_eq_right hn]

theorem bound_sensitivity (A : V → E → ℤ) (c l next u : E → ℤ) (b y : V → ℤ) :
    bound A c next u b y = bound A c l u b y +
      ∑ e, max (residual A c y e) 0*(next e-l e) := by
  unfold bound
  have ht : ∀ e, contribution (residual A c y e) (next e) (u e) =
      contribution (residual A c y e) (l e) (u e) +
        max (residual A c y e) 0*(next e-l e) := by
    intro e
    exact contribution_sensitivity _ _ _ _
  simp_rw [ht, Finset.sum_add_distrib]
  ring

theorem swap_bound [DecidableEq E] (A : V → E → ℤ) (c l u : E → ℤ)
    (b y : V → ℤ) (add remove : E) :
    bound A c (fun e => l e + (if e=add then 1 else 0) -
      (if e=remove then 1 else 0)) u b y =
    bound A c l u b y + max (residual A c y add) 0 -
      max (residual A c y remove) 0 := by
  rw [bound_sensitivity A c l (fun e => l e + (if e=add then 1 else 0) -
    (if e=remove then 1 else 0)) u b y]
  have hterm : ∀ e, max (residual A c y e) 0 *
      (l e + (if e=add then 1 else 0) - (if e=remove then 1 else 0) - l e) =
      (if e=add then max (residual A c y e) 0 else 0) -
      (if e=remove then max (residual A c y e) 0 else 0) := by
    intro e
    split_ifs <;> ring
  simp_rw [hterm, Finset.sum_sub_distrib]
  simp
  ring

#print axioms flow_cost_identity
#print axioms dual_lower_bound
#print axioms certified_minimum
#print axioms bound_sensitivity
#print axioms swap_bound
end Coeff2.Charlieplex.TopologyFlowDual
