import Coeff2.CharlieCommutatorConnector
import Coeff2.CharlieCyclicOccupationDebt
import Coeff2.CharlieReservedExitConnector
import Mathlib.Data.Finset.Max

/-!
Exact elimination of a finite phase-clock balance block. These are integer
transport equations, not occupation probabilities or a common eigenbasis.
A cyclic primitive exists precisely under the supplied zero total charge;
its constant mode is fixed by nonnegativity. This minimizes repeated required
edge copies for a FIXED dirty attachment ledger. Choosing that ledger remains
a separate integer connectivity problem.
-/
namespace Coeff2.Charlieplex.ClockBalanceElimination
open scoped BigOperators

section ConstantMode
variable {X : Type*}

theorem invariant_iterate (next : X → X) (f : X → ℤ)
    (same : ∀ x, f (next x) = f x) (k : ℕ) (x : X) :
    f ((next^[k]) x) = f x := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', same, ih]

/-- The only freedom in two solutions on one transitive clock is a constant.
This is the exact zero mode, not a conjectured occupation-sector quotient. -/
theorem derivative_difference_constant (next : X → X)
    (reachable : ∀ x y, ∃ k, (next^[k]) x = y)
    (f H : X → ℤ)
    (same : ∀ x, f (next x) - f x = H (next x) - H x) (r x : X) :
    f x - H x = f r - H r := by
  obtain ⟨k, hk⟩ := reachable r x
  have hi : ∀ y, (f (next y) - H (next y)) = f y - H y := by
    intro y
    have hh := same y
    omega
  have hh := invariant_iterate next (fun y => f y - H y) hi k r
  rwa [hk] at hh

variable [Fintype X]

/-- Subtract the attained minimum of a primitive. This produces the unique
componentwise smallest nonnegative solution, hence the exact minimum sum. -/
theorem normalized_is_least (next : X → X)
    (reachable : ∀ x y, ∃ k, (next^[k]) x = y)
    (H f : X → ℤ) (r : X) (minimum : ∀ x, H r ≤ H x)
    (same : ∀ x, f (next x) - f x = H (next x) - H x)
    (positive : ∀ x, 0 ≤ f x) :
    (∀ x, 0 ≤ H x - H r) ∧
    (∀ x, H x - H r ≤ f x) ∧
    (∑ x, (H x - H r)) ≤ ∑ x, f x := by
  have hl : ∀ x, H x - H r ≤ f x := by
    intro x
    have hc := derivative_difference_constant next reachable f H same r x
    have hp := positive r
    omega
  exact ⟨fun x => sub_nonneg.mpr (minimum x), hl,
    Finset.sum_le_sum (fun x _ => hl x)⟩

theorem normalized_derivative (next : X → X) (H : X → ℤ) (r x : X) :
    (H (next x) - H r) - (H x - H r) = H (next x) - H x := by ring

theorem nonnegative_clock_minimum [Nonempty X] (next : X → X)
    (reachable : ∀ x y, ∃ k, (next^[k]) x = y) (H : X → ℤ) :
    ∃ r, (∀ x, 0 ≤ H x - H r) ∧
      ∀ f : X → ℤ,
        (∀ x, f (next x) - f x = H (next x) - H x) →
        (∀ x, 0 ≤ f x) →
        (∀ x, H x - H r ≤ f x) ∧
          (∑ x, (H x - H r)) ≤ ∑ x, f x := by
  classical
  obtain ⟨r, _, hr⟩ := Finset.exists_min_image Finset.univ H Finset.univ_nonempty
  have hm : ∀ x, H r ≤ H x := fun x => hr x (Finset.mem_univ x)
  refine ⟨r, fun x => sub_nonneg.mpr (hm x), ?_⟩
  intro f hd hp
  exact (normalized_is_least next reachable H f r hm hd hp).2
end ConstantMode

/-- Integer prefix sums give a cyclic primitive without a linear solve. -/
def primitive (h : ℕ → ℤ) {m : ℕ} (i : Fin (m+1)) : ℤ :=
  ∑ j ∈ Finset.range i.val, h j

theorem primitive_balance (m : ℕ) (h : ℕ → ℤ)
    (closed : (∑ j ∈ Finset.range (m+1), h j) = 0) (i : Fin (m+1)) :
    primitive h (finRotate (m+1) i) - primitive h i = h i.val := by
  by_cases last : i = Fin.last m
  · subst i
    rw [finRotate_last]
    simp only [primitive, Fin.val_zero, Fin.val_last, Finset.range_zero, Finset.sum_empty]
    rw [Finset.sum_range_succ] at closed
    omega
  · have hv := coe_finRotate_of_ne_last last
    simp only [primitive]
    rw [hv, Finset.sum_range_succ]
    ring

theorem finite_clock_reachable (m : ℕ) (x y : Fin (m+1)) :
    ∃ k, ((finRotate (m+1))^[k]) x = y := by
  obtain ⟨k,hk⟩ := CyclicOccupationDebt.fin_phase_reachable (m+1) x y
  exact ⟨k, (CyclicOccupationDebt.advance_eq_iterate _ _ _).symm.trans hk⟩

/-- Uniform in the radix. Given a zero-sum signed attachment charge, this
is an attained algebraic minimum over ALL nonnegative clock-copy vectors. -/
theorem exact_clock_solver (m : ℕ) (h : ℕ → ℤ)
    (closed : (∑ j ∈ Finset.range (m+1), h j) = 0) :
    ∃ r : Fin (m+1),
      (∀ x : Fin (m+1), 0 ≤ primitive (m := m) h x - primitive (m := m) h r) ∧
      (∀ x : Fin (m+1),
        (primitive (m := m) h (finRotate (m+1) x) - primitive (m := m) h r) -
          (primitive (m := m) h x - primitive (m := m) h r) = h x.val) ∧
      ∀ f : Fin (m+1) → ℤ,
        (∀ x, f (finRotate (m+1) x) - f x = h x.val) →
        (∀ x, 0 ≤ f x) →
        (∀ x, primitive (m := m) h x - primitive (m := m) h r ≤ f x) ∧
          (∑ x, (primitive (m := m) h x - primitive (m := m) h r)) ≤ ∑ x, f x := by
  obtain ⟨r, hp, least⟩ := nonnegative_clock_minimum (finRotate (m+1))
    (finite_clock_reachable m) (primitive h : Fin (m+1) → ℤ)
  refine ⟨r, hp, ?_, ?_⟩
  · intro x
    rw [normalized_derivative, primitive_balance m h closed x]
  · intro f hf hpos
    apply least f _ hpos
    intro x
    rw [primitive_balance m h closed x, hf x]

/-- A fixed circulant integer kernel; no occupation history enters its entries. -/
def saw (m : ℕ) (r j : Fin (m+1)) : ℤ := ((r-j).val : ℤ)

theorem saw_difference (m : ℕ) (r j : Fin (m+1)) :
    saw m r j - saw m r (finRotate (m+1) j) =
      1 - (m+1 : ℕ) * (if j = r then (1 : ℤ) else 0) := by
  have he : r - finRotate (m+1) j = (finRotate (m+1)).symm (r-j) := by
    rw [finRotate_apply, finRotate_symm_apply]
    abel
  by_cases hj : j = r
  · subst j
    unfold saw
    rw [he]
    simp only [sub_self, finRotate_symm_apply, zero_sub, Fin.val_zero,
      Fin.coe_neg_one, if_pos rfl]
    push_cast
    ring
  · have hd : r-j ≠ 0 := sub_ne_zero.mpr (Ne.symm hj)
    have hp : 0 < (r-j).val := by
      apply Nat.pos_of_ne_zero
      simpa only [Fin.val_ne_zero_iff] using hd
    unfold saw
    rw [he, coe_finRotate_symm_of_ne_zero hd]
    simp only [if_neg hj, mul_zero, sub_zero]
    push_cast [Nat.cast_sub (by omega : 1 ≤ (r-j).val)]
    ring

section Adjoint
variable {X : Type*} [Fintype X]

/-- Exact discrete integration by parts on a permutation clock. -/
theorem weighted_charge (next : Equiv.Perm X) (w z : X → ℤ) :
    (∑ j, w j * (z j - z (next.symm j))) =
      ∑ j, (w j - w (next j)) * z j := by
  have reindex : (∑ j, w j * z (next.symm j)) =
      ∑ j, w (next j) * z j := by
    simpa using ((show X ≃ X from next).sum_comp
      (fun j => w j * z (next.symm j))).symm
  simp_rw [mul_sub, sub_mul]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, reindex]
end Adjoint

/-- The entire clock operator collapses to its total mass and one coordinate.
This proves the fixed-matrix readout, rather than fitting its coefficients. -/
theorem saw_charge_score (m : ℕ) (z : Fin (m+1) → ℤ) (r : Fin (m+1)) :
    (∑ j, saw m r j * (z j - z ((finRotate (m+1)).symm j))) =
      (∑ j, z j) - (m+1 : ℕ) * z r := by
  rw [weighted_charge]
  simp_rw [saw_difference]
  have term (j : Fin (m+1)) :
      (1 - (m+1 : ℕ) * (if j = r then (1 : ℤ) else 0)) * z j =
      z j - (m+1 : ℕ) * (if j = r then z j else 0) := by
    split_ifs <;> ring
  simp_rw [term]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp

/-- On the least nonnegative clock solution one coordinate vanishes. The
maximum of these FIXED linear forms is exactly the minimum repeat bill. -/
theorem saw_exact_readout (m : ℕ) (z : Fin (m+1) → ℤ)
    (positive : ∀ j, 0 ≤ z j) (zero : ∃ r, z r = 0) :
    (∀ r, (∑ j, saw m r j * (z j - z ((finRotate (m+1)).symm j))) ≤
      ∑ j, z j) ∧
    ∃ r, (∑ j, saw m r j * (z j - z ((finRotate (m+1)).symm j))) =
      ∑ j, z j := by
  constructor
  · intro r
    rw [saw_charge_score]
    have hp := mul_nonneg (show 0 ≤ ((m+1 : ℕ) : ℤ) by positivity) (positive r)
    omega
  · obtain ⟨r, hr⟩ := zero
    refine ⟨r, ?_⟩
    rw [saw_charge_score, hr, mul_zero, sub_zero]

/-- The inverse can be read from the same fixed matrix: multiplying by the
radix avoids any truncated division or rational approximation. -/
theorem saw_reconstruct (m : ℕ) (z : Fin (m+1) → ℤ) (r : Fin (m+1)) :
    (m+1 : ℕ) * z r = (∑ j, z j) -
      (∑ j, saw m r j * (z j - z ((finRotate (m+1)).symm j))) := by
  rw [saw_charge_score]
  ring

def score (m : ℕ) (h : Fin (m+1) → ℤ) (r : Fin (m+1)) : ℤ :=
  ∑ j, saw m r j * h j

def gamma (m : ℕ) (h : Fin (m+1) → ℤ) : ℤ :=
  (Finset.univ.image (score m h)).max' (Finset.univ_nonempty.image _)

theorem score_le_gamma (m : ℕ) (h : Fin (m+1) → ℤ) (r : Fin (m+1)) :
    score m h r ≤ gamma m h := by
  unfold gamma
  exact Finset.le_max' _ _ (Finset.mem_image.mpr ⟨r, Finset.mem_univ r, rfl⟩)

theorem gamma_attained (m : ℕ) (h : Fin (m+1) → ℤ) :
    ∃ r, score m h r = gamma m h := by
  have hm : gamma m h ∈ Finset.univ.image (score m h) := by
    unfold gamma
    exact Finset.max'_mem _ _
  obtain ⟨r, _, hr⟩ := Finset.mem_image.mp hm
  exact ⟨r, hr⟩

theorem score_add (m : ℕ) (h k : Fin (m+1) → ℤ) (r : Fin (m+1)) :
    score m (fun j => h j + k j) r = score m h r + score m k r := by
  simp [score, mul_add, Finset.sum_add_distrib]

/-- Coordinated charges can save repeat transport: the exact block penalty
is subadditive, not an independent sum over separately optimized ports. -/
theorem gamma_subadditive (m : ℕ) (h k : Fin (m+1) → ℤ) :
    gamma m (fun j => h j + k j) ≤ gamma m h + gamma m k := by
  obtain ⟨r, hr⟩ := gamma_attained m (fun j => h j + k j)
  rw [← hr, score_add]
  exact add_le_add (score_le_gamma m h r) (score_le_gamma m k r)

theorem gamma_zero (m : ℕ) : gamma m (fun _ => 0) = 0 := by
  obtain ⟨r,hr⟩ := gamma_attained m (fun _ => 0)
  simpa [score] using hr.symm

theorem gamma_readout (m : ℕ) (z : Fin (m+1) → ℤ)
    (positive : ∀ j, 0 ≤ z j) (zero : ∃ r, z r = 0) :
    gamma m (fun j => z j - z ((finRotate (m+1)).symm j)) = ∑ j, z j := by
  obtain ⟨upper, r, attained⟩ := saw_exact_readout m z positive zero
  apply le_antisymm
  · obtain ⟨s, hs⟩ := gamma_attained m (fun j => z j - z ((finRotate (m+1)).symm j))
    rw [← hs]
    exact upper s
  · rw [← attained]
    exact score_le_gamma m _ r

/-- Opposite transport charges cancel a whole number of radix clocks.
For a nonconstant 0/1 primitive the exact separate bill is one full radix;
their combined charge is zero and gamma_zero makes its bill zero. This is
a phase-budget identity, NOT an existence theorem for a literal cheap glue. -/
theorem opposite_charge_width (m : ℕ) (z : Fin (m+1) → ℤ)
    (low high : ℤ) (rLow rHigh : Fin (m+1))
    (bounds : ∀ j, low ≤ z j ∧ z j ≤ high)
    (atLow : z rLow = low) (atHigh : z rHigh = high) :
    gamma m (fun j => z j - z ((finRotate (m+1)).symm j)) +
      gamma m (fun j => -(z j - z ((finRotate (m+1)).symm j))) =
        (m+1 : ℕ) * (high-low) := by
  have hLow := gamma_readout m (fun j => z j-low)
    (fun j => sub_nonneg.mpr (bounds j).1) ⟨rLow, by simp [atLow]⟩
  have hHigh := gamma_readout m (fun j => high-z j)
    (fun j => sub_nonneg.mpr (bounds j).2) ⟨rHigh, by simp [atHigh]⟩
  have sameLow : (fun j => (z j-low) - (z ((finRotate (m+1)).symm j)-low)) =
      (fun j => z j - z ((finRotate (m+1)).symm j)) := by funext j; ring
  have sameHigh : (fun j => (high-z j) - (high-z ((finRotate (m+1)).symm j))) =
      (fun j => -(z j - z ((finRotate (m+1)).symm j))) := by funext j; ring
  rw [sameLow] at hLow
  rw [sameHigh] at hHigh
  rw [hLow, hHigh, ← Finset.sum_add_distrib]
  have term (j : Fin (m+1)) : (z j-low)+(high-z j) = high-low := by ring
  simp_rw [term]
  simp <;> ring

section LiftTree
variable {V I : Type*} [DecidableEq V]

def liftedParent (block : V → I) (gateway : I → V) (localNext : V → V)
    (exit : I → V) (v : V) : V :=
  if v = gateway (block v) then exit (block v) else localNext v

/-- A quotient tree lifts without breaking the required clock internally.
The explicit rank proves acyclicity. Gateways select ONE omitted required
edge per clock; dirty singleton blocks have no internal required edge.
Existence of the quotient tree is supplied by actual reachability to the
terminal, not by phase counts alone. -/
theorem lifted_parent_descends (width : ℕ) (block : V → I)
    (gateway : I → V) (localNext : V → V) (exit : I → V)
    (localDistance : V → ℕ) (quotientDepth : I → ℕ) (terminal : V)
    (bounded : ∀ v, localDistance v < width)
    (localBlock : ∀ v, block (localNext v) = block v)
    (localDescent : ∀ v, v ≠ gateway (block v) →
      localDistance (localNext v) < localDistance v)
    (exitDescent : ∀ v, v = gateway (block v) → v ≠ terminal →
      localDistance v = 0 ∧ quotientDepth (block (exit (block v))) < quotientDepth (block v))
    (v : V) (nonterminal : v ≠ terminal) :
    width * quotientDepth (block (liftedParent block gateway localNext exit v)) +
        localDistance (liftedParent block gateway localNext exit v) <
      width * quotientDepth (block v) + localDistance v := by
  by_cases gatewayHere : v = gateway (block v)
  · simp only [liftedParent, if_pos gatewayHere]
    obtain ⟨hz, hd⟩ := exitDescent v gatewayHere nonterminal
    have hb := bounded (exit (block v))
    calc
      _ < width * (quotientDepth (block (exit (block v))) + 1) := by nlinarith
      _ ≤ width * quotientDepth (block v) :=
        Nat.mul_le_mul_left width (Nat.succ_le_of_lt hd)
      _ = _ := by rw [hz, Nat.add_zero]
  · simp only [liftedParent, if_neg gatewayHere, localBlock]
    exact Nat.add_lt_add_left (localDescent v gatewayHere) _
end LiftTree

end Coeff2.Charlieplex.ClockBalanceElimination

#print axioms Coeff2.Charlieplex.ClockBalanceElimination.derivative_difference_constant
#print axioms Coeff2.Charlieplex.ClockBalanceElimination.nonnegative_clock_minimum
#print axioms Coeff2.Charlieplex.ClockBalanceElimination.primitive_balance
#print axioms Coeff2.Charlieplex.ClockBalanceElimination.exact_clock_solver
#print axioms Coeff2.Charlieplex.ClockBalanceElimination.saw_difference
#print axioms Coeff2.Charlieplex.ClockBalanceElimination.saw_charge_score
#print axioms Coeff2.Charlieplex.ClockBalanceElimination.saw_exact_readout
#print axioms Coeff2.Charlieplex.ClockBalanceElimination.saw_reconstruct
#print axioms Coeff2.Charlieplex.ClockBalanceElimination.gamma_readout
#print axioms Coeff2.Charlieplex.ClockBalanceElimination.gamma_subadditive
#print axioms Coeff2.Charlieplex.ClockBalanceElimination.opposite_charge_width
#print axioms Coeff2.Charlieplex.ClockBalanceElimination.lifted_parent_descends
