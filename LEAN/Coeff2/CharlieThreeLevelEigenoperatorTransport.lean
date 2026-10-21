import Coeff2.CharlieLiftEigenoperators

/-! Exact composition across three levels. Clock compatibility alone does
not protect intermediate occupation: the two intermediate projectors must
remain in the ordered product. No coverage or cheapness is inferred. -/
namespace Coeff2.Charlieplex.ThreeLevelEigenoperatorTransport
open LiftEigenoperators
variable {I J K H R : Type*}
  [Fintype I] [Fintype J] [Fintype K] [Fintype H] [CommRing R]

/-- The rectangular clock defect obeys an exact product rule. -/
theorem defect_comp (A : Matrix I I R) (B : Matrix J J R)
    (C : Matrix K K R) (L : Matrix I J R) (M : Matrix J K R) :
    defect A C (L * M) = defect A B L * M + L * defect B C M := by
  simp only [defect, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
  abel

/-- Three successive levels: intermediate defects are transported, not
identified across different dimensions. Their sum may cancel algebraically. -/
theorem defect_three (A : Matrix I I R) (B : Matrix J J R)
    (C : Matrix K K R) (D : Matrix H H R)
    (L : Matrix I J R) (M : Matrix J K R) (N : Matrix K H R) :
    defect A D (L * M * N) =
      defect A B L * M * N + L * defect B C M * N +
        L * M * defect C D N := by
  rw [defect_comp A C D (L * M) N, defect_comp A B C L M]
  simp only [Matrix.add_mul, Matrix.mul_assoc]

omit [Fintype I] [Fintype K] in
/-- Rank-one phase ports compose through their literal intermediate pairing. -/
theorem outer_comp (u : I → R) (v x : J → R) (y : K → R) :
    outer u v * outer x y = (∑ j, v j * x j) • outer u y := by
  ext i k
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, outer]
  calc
    (∑ j, (u i * v j) * (x j * y k)) =
        u i * (∑ j, v j * x j) * y k := by
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = (∑ j, v j * x j) * (u i * y k) := by ring

omit [Fintype I] [Fintype H] in
/-- Splitting each intermediate state into free Q and occupied P gives
four exact ordered sectors. Only the Q-Q sector avoids both occupied
intermediate sets. Endpoint compatibility does not remove the other three. -/
theorem occupation_sectors [DecidableEq J] [DecidableEq K]
    (L : Matrix I J R) (M : Matrix J K R) (N : Matrix K H R)
    (Q₂ P₂ : Matrix J J R) (Q₁ P₁ : Matrix K K R)
    (h₂ : Q₂ + P₂ = 1) (h₁ : Q₁ + P₁ = 1) :
    L * M * N =
      L * Q₂ * M * Q₁ * N + L * Q₂ * M * P₁ * N +
      L * P₂ * M * Q₁ * N + L * P₂ * M * P₁ * N := by
  have h : L * M * N = L * (Q₂ + P₂) * M * (Q₁ + P₁) * N := by
    rw [h₂, h₁, Matrix.mul_one, Matrix.mul_one]
  rw [h]
  simp only [Matrix.mul_add, Matrix.add_mul]
  abel

/-- A blocked intermediate singleton can kill every path even when the
unfiltered endpoint clock defect is zero. This is an exact counterexample
to treating endpoint phase alignment as intermediate occupation safety. -/
theorem endpoint_match_not_occupation_safe :
    let E : Matrix (Fin 1) (Fin 1) ℤ := 1
    defect E E (E * E * E) = 0 ∧
      E * (0 : Matrix (Fin 1) (Fin 1) ℤ) * E * E = 0 ∧
      E * E * E ≠ 0 := by
  simp [defect]

section NonnegativePaths
variable (pathWeight : J → K → ℕ) (free₂ : J → Bool) (free₁ : K → Bool)

omit [Fintype I] [Fintype H] [CommRing R] in
/-- The natural-number three-matrix entry is precisely the literal sum over
both intermediate states, with no spectral or independence assumption. -/
theorem triple_entry (L : Matrix I J ℕ) (M : Matrix J K ℕ)
    (N : Matrix K H ℕ) (i : I) (h : H) :
    (L * M * N) i h = ∑ j, ∑ k, L i j * M j k * N k h := by
  simp only [Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

def allowedMass : ℕ :=
  ∑ j, ∑ k, if free₂ j && free₁ k then pathWeight j k else 0

def rejectedMass : ℕ :=
  ∑ j, ∑ k, if free₂ j && free₁ k then 0 else pathWeight j k

omit [Fintype I] [Fintype H] [CommRing R] in
/-- With nonnegative literal path weights, occupation removal is a disjoint
partition, not destructive interference. For three matrices the weight is
L[i,j] * M[j,k] * N[k,h]. -/
theorem path_mass_partition :
    (∑ j, ∑ k, pathWeight j k) =
      allowedMass pathWeight free₂ free₁ + rejectedMass pathWeight free₂ free₁ := by
  simp only [allowedMass, rejectedMass, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  cases h : free₂ j && free₁ k <;> simp

omit [Fintype I] [Fintype H] [CommRing R] in
theorem occupation_preserves_mass_iff :
    allowedMass pathWeight free₂ free₁ = (∑ j, ∑ k, pathWeight j k) ↔
      rejectedMass pathWeight free₂ free₁ = 0 := by
  rw [path_mass_partition pathWeight free₂ free₁]
  omega

omit [Fintype I] [Fintype H] [CommRing R] in
/-- The rejected mass vanishes exactly when every disallowed literal path
has zero weight. There is no signed cancellation loophole. -/
theorem rejected_zero_iff :
    rejectedMass pathWeight free₂ free₁ = 0 ↔
      ∀ j k, (free₂ j && free₁ k) = false → pathWeight j k = 0 := by
  simp only [rejectedMass, Finset.sum_eq_zero_iff, Finset.mem_univ, forall_true_left]
  constructor
  · intro h j k hf
    simpa [hf] using h j k
  · intro h j k
    cases hf : free₂ j && free₁ k with
    | false => simpa [hf] using h j k hf
    | true => simp
end NonnegativePaths

#print axioms defect_comp
#print axioms defect_three
#print axioms outer_comp
#print axioms occupation_sectors
#print axioms endpoint_match_not_occupation_safe
#print axioms path_mass_partition
#print axioms occupation_preserves_mass_iff
#print axioms rejected_zero_iff
#print axioms triple_entry
end Coeff2.Charlieplex.ThreeLevelEigenoperatorTransport
