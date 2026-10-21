import Mathlib.NumberTheory.FrobeniusNumber
import Mathlib.Tactic
import Coeff2.CharlieTraversal

/-!
# The rectangular phase ledger and the two-generator numerical semigroup

This is the numerical-semigroup meaning of Sylvester, not the unrelated
Sylvester word-rewriting congruence in Charlieplex.lean.

The rectangle count and the missing-cost theorem are unconditional arithmetic.
No matrix cell is silently identified with a legal superpermutation splice.
The separate literal reservoir module supplies a finite occupation-safe bridge.
-/

namespace Coeff2.Charlieplex.FrobeniusLedger

def Representable (a b t : ℕ) : Prop :=
  ∃ x y : ℕ, t = a * x + b * y

def conductor (a b : ℕ) : ℕ := (a - 1) * (b - 1)

def largestGap (a b : ℕ) : ℕ := a * b - a - b

theorem representable_zero (a b : ℕ) : Representable a b 0 := ⟨0, 0, by simp⟩

theorem representable_add {a b u v : ℕ}
    (hu : Representable a b u) (hv : Representable a b v) :
    Representable a b (u + v) := by
  obtain ⟨x, y, rfl⟩ := hu
  obtain ⟨z, w, rfl⟩ := hv
  exact ⟨x + z, y + w, by ring⟩

theorem representable_iff_closure (a b t : ℕ) :
    Representable a b t ↔ t ∈ AddSubmonoid.closure ({a,b} : Set ℕ) := by
  simp only [Representable, AddSubmonoid.mem_closure_pair, smul_eq_mul]
  constructor <;> rintro ⟨x, y, h⟩ <;> exact ⟨x, y, by nlinarith [h]⟩

theorem conductor_eq_gap_succ {a b : ℕ} (ha : 1 < a) (hb : 1 < b) :
    conductor a b = largestGap a b + 1 := by
  have hab := Nat.add_le_mul ha hb
  dsimp [conductor, largestGap]
  have hA : a - 1 + 1 = a := by omega
  have hB : b - 1 + 1 = b := by omega
  have hG : a * b - a - b + a + b = a * b := by omega
  nlinarith

theorem largestGap_not_representable {a b : ℕ}
    (hc : Nat.Coprime a b) (ha : 1 < a) (hb : 1 < b) :
    ¬ Representable a b (largestGap a b) := by
  rw [representable_iff_closure]
  exact (frobeniusNumber_iff.mp (frobeniusNumber_pair hc ha hb)).1

theorem representable_of_conductor_le {a b t : ℕ}
    (hc : Nat.Coprime a b) (ha : 1 < a) (hb : 1 < b)
    (ht : conductor a b ≤ t) : Representable a b t := by
  rw [representable_iff_closure]
  apply (frobeniusNumber_iff.mp (frobeniusNumber_pair hc ha hb)).2
  have hC := conductor_eq_gap_succ ha hb
  change largestGap a b < t
  omega

/-- Normalize the a-coefficient into one residue period. This supplies the
finite reservoir bound x<b and y<=t/b, not unbounded repeatability. -/
theorem normalized_representation {a b t : ℕ} (hb : 0 < b)
    (ht : Representable a b t) :
    ∃ x y : ℕ, x < b ∧ y ≤ t / b ∧ t = a * x + b * y := by
  obtain ⟨x, y, ht⟩ := ht
  let r := x % b
  let q := y + a * (x / b)
  have heq : t = a * r + b * q := by
    have hx := Nat.mod_add_div x b
    dsimp [r, q]
    nlinarith [hx]
  refine ⟨r, q, Nat.mod_lt x hb, ?_, heq⟩
  apply (Nat.le_div_iff_mul_le hb).mpr
  nlinarith [heq]

theorem conductor_bounded_witness {a b t : ℕ}
    (hc : Nat.Coprime a b) (ha : 1 < a) (hb : 1 < b)
    (ht : conductor a b ≤ t) :
    ∃ x y : ℕ, x < b ∧ y ≤ t / b ∧ t = a * x + b * y :=
  normalized_representation (by omega) (representable_of_conductor_le hc ha hb ht)

/-- Removing a row and a column removes their common corner only once. -/
theorem rectangular_interior_card {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (row : A) (column : B) :
    (((Finset.univ : Finset A).erase row).product
      ((Finset.univ : Finset B).erase column)).card =
        (Fintype.card A - 1) * (Fintype.card B - 1) := by
  simp

theorem rectangular_interior_is_conductor {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) :
    (((Finset.univ : Finset (Fin a)).erase ⟨0, ha⟩).product
      ((Finset.univ : Finset (Fin b)).erase ⟨0, hb⟩)).card = conductor a b := by
  simp [conductor]

/-- A positive matrix label ab-ai-bj is missing from the semigroup.
Positivity of both excluded coordinates, rather than a bare cell count,
is the essential reason. -/
theorem grid_label_not_representable {a b i j t : ℕ}
    (hc : Nat.Coprime a b) (hi : 0 < i) (hj : 0 < j)
    (hlabel : t + a * i + b * j = a * b) :
    ¬ Representable a b t := by
  rintro ⟨x, y, ht⟩
  have hneq := hc.mul_add_mul_ne_mul
    (a := x + i) (b := y + j) (by omega) (by omega)
  apply hneq
  nlinarith

/-- Every missing nonnegative amount occurs as a positive interior matrix
label. Hence the rectangle is a genuine description of arithmetic holes. -/
theorem missing_has_grid_label {a b t : ℕ}
    (hc : Nat.Coprime a b) (ha : 1 < a) (hb : 1 < b)
    (ht : ¬ Representable a b t) :
    ∃ i j : ℕ, 0 < i ∧ i < b ∧ 0 < j ∧ j < a ∧
      t + a * i + b * j = a * b := by
  have hc_le : conductor a b ≤ t + a * b := by
    dsimp [conductor]
    nlinarith [Nat.sub_le a 1, Nat.sub_le b 1]
  obtain ⟨x, y, hxb, _, heq⟩ :=
    conductor_bounded_witness hc ha hb hc_le
  have hya : y < a := by
    by_contra hn
    have hy : a ≤ y := by omega
    apply ht
    refine ⟨x, y - a, ?_⟩
    have hsub : y - a + a = y := by omega
    nlinarith
  have hx : 0 < x := by
    by_contra h
    have : x = 0 := by omega
    subst x
    nlinarith
  have hy : 0 < y := by
    by_contra h
    have : y = 0 := by omega
    subst y
    nlinarith
  refine ⟨b - x, a - y, by omega, by omega, by omega, by omega, ?_⟩
  have hX : b - x + x = b := by omega
  have hY : a - y + y = a := by omega
  nlinarith

theorem missing_iff_grid_label {a b t : ℕ}
    (hc : Nat.Coprime a b) (ha : 1 < a) (hb : 1 < b) :
    ¬ Representable a b t ↔
      ∃ i j : ℕ, 0 < i ∧ i < b ∧ 0 < j ∧ j < a ∧
        t + a * i + b * j = a * b := by
  constructor
  · exact missing_has_grid_label hc ha hb
  · rintro ⟨i, j, hi, _, hj, _, hl⟩
    exact grid_label_not_representable hc hi hj hl

theorem bounded_coordinates_unique {a b x y x' y' : ℕ}
    (hc : Nat.Coprime a b) (hb : 0 < b) (hx : x < b) (hx' : x' < b)
    (heq : a * x + b * y = a * x' + b * y') :
    x = x' ∧ y = y' := by
  have hmod : Nat.ModEq b (a * x) (a * x') := by
    have hm := congrArg (fun z => z % b) heq
    simpa [Nat.ModEq, Nat.add_mod] using hm
  have hxx := Nat.ModEq.cancel_left_of_coprime hc.symm.gcd_eq_one hmod
  have hex : x = x' := by
    simpa [Nat.ModEq, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hx'] using hxx
  subst x'
  constructor
  · rfl
  · have hy : b * y = b * y' := by omega
    exact Nat.eq_of_mul_eq_mul_left hb hy

/-- The positive cell-to-hole correspondence is one-to-one, not merely a
coincidence of two cardinality formulas. -/
theorem grid_label_unique {a b i j i' j' t : ℕ}
    (hc : Nat.Coprime a b) (hb : 0 < b) (hi : i < b) (hi' : i' < b)
    (h : t + a * i + b * j = a * b)
    (h' : t + a * i' + b * j' = a * b) :
    i = i' ∧ j = j' :=
  bounded_coordinates_unique hc hb hi hi' (by omega)

/-! ## Exact finite-supply arithmetic: one interval, not an unbounded search -/

def BoundedRepresentable (a b capA capB t : ℕ) : Prop :=
  ∃ x y : ℕ, x ≤ capA ∧ y ≤ capB ∧ t = a * x + b * y

theorem solutions_are_shifts {a b t x0 y0 x y : ℕ}
    (hc : Nat.Coprime a b) (hb : 0 < b) (hx0 : x0 < b)
    (h0 : t = a * x0 + b * y0) (hxy : t = a * x + b * y) :
    ∃ k : ℕ, x = x0 + b * k ∧ y0 = y + a * k := by
  have hnorm : a * (x % b) + b * (y + a * (x / b)) = t := by
    have hx := Nat.mod_add_div x b
    nlinarith
  have hu := bounded_coordinates_unique hc hb hx0 (Nat.mod_lt x hb)
    (h0.symm.trans hnorm.symm)
  refine ⟨x / b, ?_, hu.2⟩
  rw [hu.1]
  exact (Nat.mod_add_div x b).symm

theorem bounded_iff_shift {a b capA capB t x0 y0 : ℕ}
    (hc : Nat.Coprime a b) (hb : 0 < b) (hx0 : x0 < b)
    (h0 : t = a * x0 + b * y0) :
    BoundedRepresentable a b capA capB t ↔
      ∃ k : ℕ, x0 + b * k ≤ capA ∧ a * k ≤ y0 ∧ y0 - a * k ≤ capB := by
  constructor
  · rintro ⟨x, y, hx, hy, heq⟩
    obtain ⟨k, hkx, hky⟩ := solutions_are_shifts hc hb hx0 h0 heq
    exact ⟨k, by omega, by omega, by omega⟩
  · rintro ⟨k, hx, hy, hB⟩
    refine ⟨x0 + b * k, y0 - a * k, hx, hB, ?_⟩
    have hsub : y0 - a * k + a * k = y0 := by omega
    nlinarith

/-- Least exchange replacing a b-packets with b a-packets to respect capB. -/
def leastShift (a y0 capB : ℕ) : ℕ :=
  (y0 - capB + (a - 1)) / a

theorem leastShift_le_iff {a y0 capB k : ℕ} (ha : 0 < a) :
    leastShift a y0 capB ≤ k ↔ y0 ≤ capB + a * k := by
  unfold leastShift
  rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul ha]
  have hpred : a - 1 + 1 = a := by omega
  by_cases h : y0 ≤ capB
  · have hsub : y0 - capB = 0 := by omega
    rw [hsub]
    constructor <;> intro h' <;> nlinarith
  · have hsub : y0 - capB + capB = y0 := by omega
    constructor <;> intro h' <;> nlinarith

/-- A constant number of arithmetic operations checks finite capacity once a normalized representation is
known. No candidate is discarded merely because its normalized y exceeds
the b-packet supply: the legal coefficient exchanges are accounted for. -/
theorem bounded_iff_least_shift {a b capA capB t x0 y0 : ℕ}
    (hc : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b) (hx0 : x0 < b)
    (h0 : t = a * x0 + b * y0) :
    BoundedRepresentable a b capA capB t ↔
      x0 + b * leastShift a y0 capB ≤ capA ∧
      a * leastShift a y0 capB ≤ y0 := by
  rw [bounded_iff_shift hc hb hx0 h0]
  constructor
  · rintro ⟨k, hx, hy, hB⟩
    have hm : leastShift a y0 capB ≤ k :=
      leastShift_le_iff ha |>.mpr (by omega)
    constructor <;> nlinarith
  · rintro ⟨hx, hy⟩
    refine ⟨leastShift a y0 capB, hx, hy, ?_⟩
    have hB : y0 ≤ capB + a * leastShift a y0 capB :=
      leastShift_le_iff ha |>.mp le_rfl
    omega

/-- Upgrade the previous polynomial calculation to the actual Frobenius
theorem for the proposed consecutive traversal lengths. -/
theorem traversal_largest_gap {m : ℕ} (hm : 2 ≤ m) :
    FrobeniusNumber
      (largestGap (evenTraversalLength m) (oddTraversalLength m))
      {evenTraversalLength m, oddTraversalLength m} :=
  frobeniusNumber_pair (traversalLengths_coprime (by omega))
    (by dsimp [evenTraversalLength]; omega) (by dsimp [oddTraversalLength]; omega)

theorem traversal_conductor_formula {m : ℕ} (hm : 2 ≤ m) :
    (conductor (evenTraversalLength m) (oddTraversalLength m) : ℤ) =
      4 * (m : ℤ)^2 - 10 * (m : ℤ) + 6 := by
  have he : evenTraversalLength m - 1 + 3 = 2 * m := by
    dsimp [evenTraversalLength]; omega
  have ho : oddTraversalLength m - 1 + 2 = 2 * m := by
    dsimp [oddTraversalLength]; omega
  have he' : ((evenTraversalLength m - 1 : ℕ) : ℤ) + 3 = 2 * m := by exact_mod_cast he
  have ho' : ((oddTraversalLength m - 1 : ℕ) : ℤ) + 2 = 2 * m := by exact_mod_cast ho
  unfold conductor
  push_cast
  nlinarith

end Coeff2.Charlieplex.FrobeniusLedger
