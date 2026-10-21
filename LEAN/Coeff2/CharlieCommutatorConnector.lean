import Coeff2.CharlieOccupationCommutator
import Coeff2.CharlieLiteralState

/-!
Exact connector from literal writes to occupation commutator differences.
The signed boundary and one anchor reconstruct a mask without information
loss. These identities do not bound the number of live boundaries or anchors.
Repeated windows remain legal; their fresh support is empty.
-/
namespace Coeff2.Charlieplex.CommutatorConnector
open OccupationCommutator
variable {P : Type*} [DecidableEq P]

def vacancy (M : Finset P) (p : P) : ℤ := if p ∈ M then 0 else 1
def fresh (M E : Finset P) (p : P) : ℤ := if p ∈ E ∧ p ∉ M then 1 else 0
def flux (next : P → P) (v : P → ℤ) (p : P) : ℤ := v (next p) - v p

theorem vacancy_union (M E : Finset P) (p : P) :
    vacancy (M ∪ E) p = vacancy M p - fresh M E p := by
  by_cases hm : p ∈ M <;> by_cases he : p ∈ E <;>
    simp [vacancy, fresh, hm, he]

theorem flux_union (next : P → P) (M E : Finset P) (p : P) :
    flux next (vacancy (M ∪ E)) p =
      flux next (vacancy M) p - flux next (fresh M E) p := by
  simp only [flux, vacancy_union]
  ring

theorem commutator_union (next : P → P) (M E : Finset P)
    (v : P → ℤ) (p : P) :
    transport next (diagonal (vacancy (M ∪ E)) v) p -
      diagonal (vacancy (M ∪ E)) (transport next v) p =
    (transport next (diagonal (vacancy M) v) p -
      diagonal (vacancy M) (transport next v) p) -
      flux next (fresh M E) p * v (next p) := by
  simp only [commutator_entry]
  change flux next (vacancy (M ∪ E)) p * v (next p) =
    flux next (vacancy M) p * v (next p) - flux next (fresh M E) p * v (next p)
  rw [flux_union, sub_mul]

theorem fresh_singleton (M : Finset P) (hit p : P) (h : hit ∉ M) :
    fresh M {hit} p = if p = hit then 1 else 0 := by
  by_cases he : p = hit
  · subst p; simp [fresh, h]
  · simp [fresh, he]

theorem singleton_flux_connector (next : P → P) (M : Finset P)
    (hit p : P) (h : hit ∉ M) :
    flux next (vacancy (insert hit M)) p = flux next (vacancy M) p +
      (if p = hit then 1 else 0) - (if next p = hit then 1 else 0) := by
  have hu : insert hit M = M ∪ {hit} := by ext q; simp
  rw [hu, flux_union]
  simp only [flux, fresh_singleton M hit _ h]
  ring

theorem connector_support (next : P → P) (M : Finset P)
    (hit p : P) (h : hit ∉ M) (hp : p ≠ hit) (hn : next p ≠ hit) :
    flux next (vacancy (insert hit M)) p = flux next (vacancy M) p := by
  rw [singleton_flux_connector next M hit p h]
  simp [hp, hn]

theorem repeated_write (next : P → P) (M : Finset P)
    (hit : P) (h : hit ∈ M) :
    vacancy (insert hit M) = vacancy M ∧
      flux next (vacancy (insert hit M)) = flux next (vacancy M) := by
  simp [Finset.insert_eq_of_mem h]

theorem reconstruct_from_anchor (v : ℕ → ℤ) (j : ℕ) :
    v j = v 0 + ∑ i ∈ Finset.range j, (v (i + 1) - v i) := by
  induction j with
  | zero => simp
  | succ j ih => rw [Finset.sum_range_succ]; linarith

/-- Summing the reconstructed mask exposes the weighted boundary charge.
This is exact for every radix and every integer-valued phase function. -/
theorem weighted_reconstruct (v : ℕ → ℤ) (m : ℕ) :
    (∑ j ∈ Finset.range m, v j) =
      (m : ℤ) * v 0 +
        ∑ i ∈ Finset.range m, ((m : ℤ) - 1 - (i : ℤ)) * (v (i + 1) - v i) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hw :
        (∑ i ∈ Finset.range (m + 1),
          (((m + 1 : ℕ) : ℤ) - 1 - (i : ℤ)) * (v (i + 1) - v i)) =
        (∑ i ∈ Finset.range m,
          ((m : ℤ) - 1 - (i : ℤ)) * (v (i + 1) - v i)) +
        ∑ i ∈ Finset.range m, (v (i + 1) - v i) := by
      rw [Finset.sum_range_succ]
      have hz : (((m + 1 : ℕ) : ℤ) - 1 - (m : ℤ)) = 0 := by
        push_cast
        ring
      rw [hz, zero_mul, add_zero, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      push_cast
      ring
    rw [Finset.sum_range_succ, ih, hw]
    have ht := reconstruct_from_anchor v m
    push_cast
    nlinarith

theorem anchor_differences_determine (m : ℕ) (v w : ℕ → ℤ)
    (h0 : v 0 = w 0)
    (hd : ∀ j, j + 1 < m → v (j + 1) - v j = w (j + 1) - w j) :
    ∀ j, j < m → v j = w j := by
  intro j
  induction j with
  | zero => intro _; exact h0
  | succ j ih =>
    intro hj
    have hp := ih (by omega)
    have he := hd j hj
    linarith

/-- Every zero-phase slice is the anchor FUNCTION on the next lower frame,
not just one global count. Its differences may themselves be represented. -/
theorem row_reconstruct {R : Type*} (v : R → ℕ → ℤ) (row : R) (phase : ℕ) :
    v row phase = v row 0 +
      ∑ i ∈ Finset.range phase, (v row (i + 1) - v row i) :=
  reconstruct_from_anchor (v row) phase

def rowWrite {R : Type*} [DecidableEq R] (v : R → ℕ → ℤ)
    (hitRow : R) (phase : ℕ) (row : R) (j : ℕ) : ℤ :=
  v row j - if row = hitRow ∧ j = phase then 1 else 0

/-- Only a zero-phase write changes the lower-order anchor function. -/
theorem anchor_no_carry {R : Type*} [DecidableEq R] (v : R → ℕ → ℤ)
    (hitRow row : R) (phase : ℕ) (h : phase ≠ 0) :
    rowWrite v hitRow phase row 0 = v row 0 := by
  simp [rowWrite, Ne.symm h]

theorem anchor_carry {R : Type*} [DecidableEq R] (v : R → ℕ → ℤ)
    (hitRow row : R) :
    rowWrite v hitRow 0 row 0 = v row 0 - if row = hitRow then 1 else 0 := by
  simp [rowWrite]

theorem row_write_difference {R : Type*} [DecidableEq R] (v : R → ℕ → ℤ)
    (hitRow row : R) (phase j : ℕ) :
    rowWrite v hitRow phase row (j + 1) - rowWrite v hitRow phase row j =
      (v row (j + 1) - v row j) +
        (if row = hitRow ∧ j = phase then 1 else 0) -
        (if row = hitRow ∧ j + 1 = phase then 1 else 0) := by
  unfold rowWrite
  ring

def literalEmission (n : ℕ) (state : LiteralSearchState) (symbol : ℕ) :
    Finset (List ℕ) :=
  if literalPermTest n (state.boundary ++ [symbol]) then
    {state.boundary ++ [symbol]} else ∅

theorem literal_step_union (n : ℕ) (state : LiteralSearchState) (symbol : ℕ) :
    (literalStateStep n state symbol).occupied =
      state.occupied ∪ literalEmission n state symbol := by
  cases hit : literalPermTest n (state.boundary ++ [symbol]) <;>
    simp [literalStateStep, literalEmission, hit]

theorem literal_flux_connector (n : ℕ) (state : LiteralSearchState)
    (symbol : ℕ) (next : List ℕ → List ℕ) (p : List ℕ) :
    flux next (vacancy (literalStateStep n state symbol).occupied) p =
      flux next (vacancy state.occupied) p -
        flux next (fresh state.occupied (literalEmission n state symbol)) p := by
  rw [literal_step_union]
  exact flux_union next state.occupied (literalEmission n state symbol) p

/-- The connector applies to the actual streaming state of a literal word,
not to an assumed packet realization. The phase map next is explicit. -/
theorem literal_word_connector (n : ℕ) (hn : 1 ≤ n) (word : List ℕ)
    (symbol : ℕ) (next : List ℕ → List ℕ) (p : List ℕ) :
    flux next (vacancy (literalStateOf n (word ++ [symbol])).occupied) p =
      flux next (vacancy (literalStateOf n word).occupied) p -
        flux next (fresh (literalStateOf n word).occupied
          (literalEmission n (literalStateOf n word) symbol)) p := by
  rw [← literalStateStep_correct n hn word symbol]
  exact literal_flux_connector n (literalStateOf n word) symbol next p

#print axioms commutator_union
#print axioms singleton_flux_connector
#print axioms reconstruct_from_anchor
#print axioms weighted_reconstruct
#print axioms anchor_no_carry
#print axioms anchor_carry
#print axioms literal_word_connector
end Coeff2.Charlieplex.CommutatorConnector
