import Coeff2.CharlieThreeLevelEigenoperatorTransport
import Coeff2.CharlieFreeRowCoverage
import Mathlib.Algebra.Ring.GeomSum

/-! A deterministic guarded occupation write acts on diagonal matrices.
Its superoperator preserves the classical diagonal sector, where it is
exactly a weighted transfer matrix. No eigenbasis or cheapness is assumed.
The concrete row-to-mask/frame transition table is a separate application. -/
namespace Coeff2.Charlieplex.OccupationSuperoperator
variable {S R : Type*} [Fintype S] [DecidableEq S] [CommSemiring R]

def act (K X : Matrix S S R) : Matrix S S R := K * X * K.transpose
def classicalTransfer (K : Matrix S S R) : Matrix S S R :=
  fun i j => K i j * K i j

theorem act_add (K X Y : Matrix S S R) :
    act K (X + Y) = act K X + act K Y := by
  simp only [act, Matrix.mul_add, Matrix.add_mul]

/-- A column has at most one nonzero output for a deterministic write.
Then the diagonal occupation sector is invariant under its superoperator. -/
theorem diagonal_sector (K : Matrix S S R) (x : S → R)
    (hcolumn : ∀ s i j, i ≠ j → K i s * K j s = 0) :
    act K (Matrix.diagonal x) =
      Matrix.diagonal ((classicalTransfer K).mulVec x) := by
  ext i j
  simp only [act, Matrix.mul_apply, Matrix.transpose_apply]
  have hentry :
      (∑ k, (∑ l, K i l * Matrix.diagonal x l k) * K j k) =
        ∑ k, K i k * x k * K j k := by
    apply Finset.sum_congr rfl
    intro k hk
    simp [Matrix.diagonal_apply]
  rw [hentry]
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq, Matrix.mulVec, dotProduct,
      classicalTransfer]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  · rw [Matrix.diagonal_apply_ne _ hij]
    apply Finset.sum_eq_zero
    intro k hk
    calc
      K i k * x k * K j k = x k * (K i k * K j k) := by ring
      _ = 0 := by rw [hcolumn k i j hij, mul_zero]

/-- Ordered superoperator composition is ordered classical transport on
this invariant sector. It does not commute the choices or erase guards. -/
theorem diagonal_composition (K L : Matrix S S R) (x : S → R)
    (hk : ∀ s i j, i ≠ j → K i s * K j s = 0)
    (hl : ∀ s i j, i ≠ j → L i s * L j s = 0) :
    act K (act L (Matrix.diagonal x)) =
      Matrix.diagonal ((classicalTransfer K).mulVec
        ((classicalTransfer L).mulVec x)) := by
  rw [diagonal_sector L x hl, diagonal_sector K _ hk]

/-- The exact per-row cost decomposition is uniform in n and visible
volume. Subtraction lives in integers; no truncated natural subtraction
is silently used in the normalized deficit. -/
theorem row_cost_split (n v overlap : ℕ) :
    (((n+1)*v+(n-2) : ℕ) : ℤ) - overlap =
      (n+1 : ℕ)*v + ((n-2 : ℕ) - (overlap : ℤ)) := by
  push_cast
  ring

/-- Cancel assigned volume BEFORE enumerating a row. The remaining target
budget imposes a minimum overlap band, uniformly in n. The unassigned
volume rem-v is exact because the row footprint is disjoint and contained
in the remaining target; that geometric premise supplies hv. -/
theorem row_budget_band (n v rem overlap : ℕ) (hv : v ≤ rem)
    (cost finish target : ℤ) :
    cost + (((n+1)*v+(n-2) : ℕ) : ℤ) - overlap +
      (n+1 : ℕ)*(rem-v : ℕ) + finish ≤ target ↔
    (n-2 : ℕ) ≤ (overlap : ℤ) + target - cost -
      (n+1 : ℕ)*rem - finish := by
  push_cast [Nat.cast_sub hv]
  constructor <;> intro h <;> nlinarith

section OrderedElimination
variable {F K : Type*} [Fintype F] [DecidableEq F] [CommRing K]

/-- The literal occupation guard strictly increases the assigned grade.
This is a cardinality fact about a disjoint NONEMPTY write, not phase. -/
theorem nonempty_write_increases {O : Type*} [DecidableEq O]
    (used added : Finset O) (h : Disjoint used added) (hne : added.Nonempty) :
    used.card < (used ∪ added).card := by
  rw [Finset.card_union_of_disjoint h]
  have hp := Finset.card_pos.mpr hne
  omega

def writeTransfer {O : Type*} [DecidableEq O] (mask : F → Finset O)
    (added : Finset O) (boundaryWeight : Matrix F F K) : Matrix F F K :=
  fun i j => if mask i = mask j ∪ added ∧ Disjoint (mask j) added
    then boundaryWeight i j else 0

/-- A concrete mask-write matrix has the required grading automatically;
its boundary weights need not commute or have a common eigenbasis. -/
theorem writeTransfer_grade {O : Type*} [DecidableEq O]
    (mask : F → Finset O) (added : Finset O) (hne : added.Nonempty)
    (W : Matrix F F K) :
    ∀ i j, (mask i).card ≤ (mask j).card → writeTransfer mask added W i j = 0 := by
  intro i j hij
  unfold writeTransfer
  split_ifs with h
  · have hg := nonempty_write_increases (mask j) added h.2 hne
    rw [← h.1] at hg
    omega
  · rfl

/-- A power of a strictly occupation-graded transfer can only raise the
grade by at least its exponent. Row i is destination; column j is source. -/
theorem graded_power_zero (T : Matrix F F K) (grade : F → ℕ)
    (ht : ∀ i j, grade i ≤ grade j → T i j = 0)
    (k : ℕ) (i j : F) (h : grade i < grade j+k) : (T^k) i j = 0 := by
  induction k generalizing i j with
  | zero =>
      have hij : i ≠ j := by intro he; subst j; omega
      simp [hij]
  | succ k ih =>
      rw [pow_succ, Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro a ha
      by_cases hja : grade j < grade a
      · rw [ih i a (by omega), zero_mul]
      · rw [ht a j (by omega), mul_zero]

/-- Bounded occupation grading supplies nilpotency, uniformly in alphabet
order and dictionary size. No diagonalization is required. -/
theorem graded_nilpotent (T : Matrix F F K) (grade : F → ℕ) (D : ℕ)
    (ht : ∀ i j, grade i ≤ grade j → T i j = 0)
    (bound : ∀ i, grade i ≤ D) : T^(D+1) = 0 := by
  ext i j
  exact graded_power_zero T grade ht (D+1) i j (by have := bound i; omega)

def finiteClosure (A : Matrix F F K) (m : ℕ) : Matrix F F K :=
  ∑ i ∈ Finset.range m, A^i

/-- Nilpotency turns the closure into a finite exact polynomial, with no
analytic convergence or diagonalization assumption. -/
theorem finiteClosure_exact (A : Matrix F F K) (m : ℕ) (ha : A^m = 0) :
    (1-A)*finiteClosure A m = 1 := by
  simpa [finiteClosure, ha] using mul_neg_geom_sum A m

/-- Eliminate zero-deficit transport A without commuting it with charged
transport B. Q is its exact closure, not an approximation. The separate
nilpotency/path bridge must supply the closure premise in an application. -/
theorem zero_deficit_factor (A B Q : Matrix F F K)
    (hq : (1-A)*Q = 1) :
    1-A-B = (1-A)*(1-Q*B) := by
  calc
    1-A-B = (1-A) - ((1-A)*Q)*B := by rw [hq, Matrix.one_mul]
    _ = (1-A)*(1-Q*B) := by
      simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]

/-- A second exact closure H then gives an ordered inverse for the full
transport. This is an algebraic elimination identity, not a speed promise. -/
theorem zero_deficit_resolvent (A B Q H : Matrix F F K)
    (hq : (1-A)*Q = 1) (hh : (1-Q*B)*H = 1) :
    (1-A-B)*(H*Q) = 1 := by
  rw [zero_deficit_factor A B Q hq]
  calc
    ((1-A)*(1-Q*B))*(H*Q) = (1-A)*(((1-Q*B)*H)*Q) := by
      simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hh, Matrix.one_mul, hq]

/-- Exact finite zero-deficit elimination. Occupation grading is what
must establish both nilpotency premises for an actual row-state machine. -/
theorem finite_zero_deficit_resolvent (A B : Matrix F F K) (m k : ℕ)
    (ha : A^m = 0) (hc : (finiteClosure A m * B)^k = 0) :
    (1-A-B)*(finiteClosure (finiteClosure A m * B) k * finiteClosure A m) = 1 := by
  exact zero_deficit_resolvent A B (finiteClosure A m)
    (finiteClosure (finiteClosure A m * B) k)
    (finiteClosure_exact A m ha)
    (finiteClosure_exact (finiteClosure A m * B) k hc)

/-- Zero-deficit closure may preserve grade (its identity term), but cannot
lower it. Following it after a charged write still strictly raises grade. -/
theorem closure_charged_grade (A B : Matrix F F K) (grade : F → ℕ) (m : ℕ)
    (ha : ∀ i j, grade i ≤ grade j → A i j = 0)
    (hb : ∀ i j, grade i ≤ grade j → B i j = 0) :
    ∀ i j, grade i ≤ grade j → (finiteClosure A m * B) i j = 0 := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro a ha'
  by_cases hja : grade j < grade a
  · have hq : finiteClosure A m i a = 0 := by
      unfold finiteClosure
      simp only [Matrix.sum_apply]
      apply Finset.sum_eq_zero
      intro k hk
      exact graded_power_zero A grade ha k i a (by omega)
    rw [hq, zero_mul]
  · rw [hb a j (by omega), mul_zero]

/-- Both formerly conditional nilpotency premises follow from the actual
occupation grade. This is the exact finite algebraic reduction for any D.
The state/dictionary's literal completeness and cheapness remain separate. -/
theorem graded_zero_deficit_resolvent (A B : Matrix F F K)
    (grade : F → ℕ) (D : ℕ)
    (ha : ∀ i j, grade i ≤ grade j → A i j = 0)
    (hb : ∀ i j, grade i ≤ grade j → B i j = 0)
    (bound : ∀ i, grade i ≤ D) :
    (1-A-B)*(finiteClosure (finiteClosure A (D+1)*B) (D+1)*
      finiteClosure A (D+1)) = 1 := by
  exact finite_zero_deficit_resolvent A B (D+1) (D+1)
    (graded_nilpotent A grade D ha bound)
    (graded_nilpotent (finiteClosure A (D+1)*B) grade D
      (closure_charged_grade A B grade (D+1) ha hb) bound)

end OrderedElimination

#print axioms act_add
#print axioms diagonal_sector
#print axioms diagonal_composition
#print axioms row_cost_split
#print axioms row_budget_band
#print axioms zero_deficit_factor
#print axioms zero_deficit_resolvent
#print axioms finiteClosure_exact
#print axioms finite_zero_deficit_resolvent
#print axioms nonempty_write_increases
#print axioms writeTransfer_grade
#print axioms graded_power_zero
#print axioms graded_nilpotent
#print axioms closure_charged_grade
#print axioms graded_zero_deficit_resolvent
end Coeff2.Charlieplex.OccupationSuperoperator
