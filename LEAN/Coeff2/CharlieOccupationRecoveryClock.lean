import Coeff2.CharlieClockBalanceElimination

/-!
Exact JOINT phase/occupation recovery bill on every finite clock. The lower
copy floor may be the Boolean unseen indicator, not a whole occupied course.
This is a cost theorem, not a choice of the future dirty attachment ledger.

One fresh required write consumes one floor unit and one transport unit; their
boundary changes cancel. A repeated required write either consumes an allocated
copy, or forces a full radix winding. Literal graph connectivity and an all-n
bound on the generated dirty ledger are NOT assumed to follow from this block.
-/
namespace Coeff2.Charlieplex.OccupationRecoveryClock
open scoped BigOperators
open ClockBalanceElimination

def charge (m : ℕ) (x : Fin (m+1) → ℤ) (j : Fin (m+1)) : ℤ :=
  x j - x ((finRotate (m+1)).symm j)

def floorScore (m : ℕ) (h lower : Fin (m+1) → ℤ) (r : Fin (m+1)) : ℤ :=
  score m h r + (m+1 : ℕ) * lower r

def recovery (m : ℕ) (h lower : Fin (m+1) → ℤ) : ℤ :=
  (Finset.univ.image (floorScore m h lower)).max' (Finset.univ_nonempty.image _)

theorem floorScore_le_recovery (m : ℕ) (h lower : Fin (m+1) → ℤ)
    (r : Fin (m+1)) : floorScore m h lower r ≤ recovery m h lower := by
  unfold recovery
  exact Finset.le_max' _ _ (Finset.mem_image.mpr ⟨r, Finset.mem_univ r, rfl⟩)

theorem recovery_attained (m : ℕ) (h lower : Fin (m+1) → ℤ) :
    ∃ r, floorScore m h lower r = recovery m h lower := by
  have hh : recovery m h lower ∈ Finset.univ.image (floorScore m h lower) := by
    unfold recovery
    exact Finset.max'_mem _ _
  obtain ⟨r, _, hr⟩ := Finset.mem_image.mp hh
  exact ⟨r, hr⟩

theorem floorScore_readout (m : ℕ) (x lower : Fin (m+1) → ℤ)
    (r : Fin (m+1)) :
    floorScore m (charge m x) lower r = (∑ j, x j) -
      (m+1 : ℕ) * (x r - lower r) := by
  unfold floorScore score charge
  rw [saw_charge_score]
  ring

theorem recovery_lower_bound (m : ℕ) (x lower : Fin (m+1) → ℤ)
    (above : ∀ j, lower j ≤ x j) :
    recovery m (charge m x) lower ≤ ∑ j, x j := by
  obtain ⟨r, hr⟩ := recovery_attained m (charge m x) lower
  rw [← hr, floorScore_readout]
  have hp := mul_nonneg (show 0 ≤ ((m+1 : ℕ) : ℤ) by positivity)
    (sub_nonneg.mpr (above r))
  omega

/-- Tightness at one phase fixes the constant mode. The lower floor is
arbitrary: it can encode vacancy or demanded internal support. -/
theorem recovery_exact (m : ℕ) (x lower : Fin (m+1) → ℤ)
    (above : ∀ j, lower j ≤ x j) (tight : ∃ r, x r = lower r) :
    recovery m (charge m x) lower = ∑ j, x j := by
  apply le_antisymm (recovery_lower_bound m x lower above)
  obtain ⟨r, hr⟩ := tight
  have hh := floorScore_le_recovery m (charge m x) lower r
  rw [floorScore_readout, hr, sub_self, mul_zero, sub_zero] at hh
  exact hh

/-- Occupation and transport enter ONE charge. Adding two independent
penalties would lose this exact cancellation. -/
theorem coupled_recovery (m : ℕ) (h lower : Fin (m+1) → ℤ) :
    recovery m h lower = (∑ j, lower j) +
      gamma m (fun j => h j - charge m lower j) := by
  have row (r : Fin (m+1)) :
      floorScore m h lower r = (∑ j, lower j) +
        score m (fun j => h j - charge m lower j) r := by
    have hs : score m (fun j => h j - charge m lower j) r =
        score m h r - score m (charge m lower) r := by
      simp only [score, mul_sub, Finset.sum_sub_distrib]
    have hc : score m (charge m lower) r =
        (∑ j, lower j) - (m+1 : ℕ) * lower r :=
      saw_charge_score m lower r
    unfold floorScore
    rw [hs, hc]
    ring
  apply le_antisymm
  · obtain ⟨r, hr⟩ := recovery_attained m h lower
    rw [← hr, row]
    have hh := score_le_gamma m (fun j => h j - charge m lower j) r
    omega
  · obtain ⟨r, hr⟩ := gamma_attained m (fun j => h j - charge m lower j)
    rw [← hr, ← row]
    exact floorScore_le_recovery m h lower r

def offset (m : ℕ) (x lower : Fin (m+1) → ℤ) : ℤ :=
  (Finset.univ.image (fun j => lower j - x j)).max' (Finset.univ_nonempty.image _)

def leastCopies (m : ℕ) (x lower : Fin (m+1) → ℤ) (j : Fin (m+1)) : ℤ :=
  x j + offset m x lower

theorem leastCopies_above (m : ℕ) (x lower : Fin (m+1) → ℤ) :
    ∀ j, lower j ≤ leastCopies m x lower j := by
  intro j
  have hh : lower j - x j ≤ offset m x lower := by
    have hi : lower j - x j ∈ (Finset.univ : Finset (Fin (m+1))).image
        (fun r => lower r - x r) :=
      Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
    unfold offset
    exact Finset.le_max' _ _ hi
  unfold leastCopies
  omega

theorem leastCopies_tight (m : ℕ) (x lower : Fin (m+1) → ℤ) :
    ∃ r, leastCopies m x lower r = lower r := by
  have hh : offset m x lower ∈ Finset.univ.image (fun j => lower j - x j) := by
    unfold offset
    exact Finset.max'_mem _ _
  obtain ⟨r, _, hr⟩ := Finset.mem_image.mp hh
  refine ⟨r, ?_⟩
  unfold leastCopies
  omega

theorem leastCopies_charge (m : ℕ) (x lower : Fin (m+1) → ℤ) :
    charge m (leastCopies m x lower) = charge m x := by
  funext j
  unfold charge leastCopies
  ring

/-- The fixed matrix minimizes every nonnegative copy problem with a
phase-dependent floor, not only the uniform whole-clock occupation floor. -/
theorem leastCopies_minimum (m : ℕ) (x lower : Fin (m+1) → ℤ) :
    recovery m (charge m x) lower = ∑ j, leastCopies m x lower j ∧
      ∀ candidate : Fin (m+1) → ℤ,
        charge m candidate = charge m x →
        (∀ j, lower j ≤ candidate j) →
        (∑ j, leastCopies m x lower j) ≤ ∑ j, candidate j := by
  have he := recovery_exact m (leastCopies m x lower) lower
    (leastCopies_above m x lower) (leastCopies_tight m x lower)
  rw [leastCopies_charge] at he
  refine ⟨he, ?_⟩
  intro candidate hc ha
  rw [← he, ← hc]
  exact recovery_lower_bound m candidate lower ha

def backPrimitive (m : ℕ) (h : ℕ → ℤ) (j : Fin (m+1)) : ℤ :=
  primitive h (finRotate (m+1) j)

theorem backPrimitive_charge (m : ℕ) (h : ℕ → ℤ)
    (closed : (∑ j ∈ Finset.range (m+1), h j) = 0) :
    charge m (backPrimitive m h) = fun j => h j.val := by
  funext j
  unfold charge backPrimitive
  rw [Equiv.apply_symm_apply]
  exact primitive_balance m h closed j

/-- No already-completed word is an existence premise: zero total charge
constructs the phase copies algebraically for any supplied lower floor.
This block existence does not claim global directed connectivity. -/
theorem closed_charge_solver (m : ℕ) (h : ℕ → ℤ)
    (closed : (∑ j ∈ Finset.range (m+1), h j) = 0)
    (lower : Fin (m+1) → ℤ) :
    ∃ x : Fin (m+1) → ℤ,
      charge m x = (fun j => h j.val) ∧
      (∀ j, lower j ≤ x j) ∧
      recovery m (fun j => h j.val) lower = ∑ j, x j ∧
      ∀ candidate : Fin (m+1) → ℤ,
        charge m candidate = (fun j => h j.val) →
        (∀ j, lower j ≤ candidate j) → (∑ j, x j) ≤ ∑ j, candidate j := by
  let x := leastCopies m (backPrimitive m h) lower
  have hc := backPrimitive_charge m h closed
  have hm := leastCopies_minimum m (backPrimitive m h) lower
  rw [hc] at hm
  exact ⟨x, (leastCopies_charge _ _ _).trans hc, leastCopies_above _ _ _, hm⟩

def consume (m : ℕ) (x : Fin (m+1) → ℤ) (j r : Fin (m+1)) : ℤ :=
  x r - if r = j then 1 else 0

theorem consume_sum (m : ℕ) (x : Fin (m+1) → ℤ) (j : Fin (m+1)) :
    (∑ r, consume m x j r) = (∑ r, x r) - 1 := by
  simp [consume, Finset.sum_sub_distrib]

/-- A fresh required write consumes its unseen floor and its phase copy.
The combined recovery bill decreases EXACTLY by one, at every radix. -/
theorem fresh_write_cost (m : ℕ) (x lower : Fin (m+1) → ℤ)
    (above : ∀ r, lower r ≤ x r) (tight : ∃ r, x r = lower r) (j : Fin (m+1)) :
    recovery m (charge m (consume m x j)) (consume m lower j) =
      recovery m (charge m x) lower - 1 := by
  have ha : ∀ r, consume m lower j r ≤ consume m x j r := by
    intro r
    unfold consume
    exact sub_le_sub_right (above r) _
  have ht : ∃ r, consume m x j r = consume m lower j r := by
    obtain ⟨r, hr⟩ := tight
    exact ⟨r, by simp [consume, hr]⟩
  rw [recovery_exact m _ _ ha ht, recovery_exact m x lower above tight, consume_sum]

/-- An allocated repeated copy is ordinary transport: its bill drops one. -/
theorem allocated_repeat_cost (m : ℕ) (x lower : Fin (m+1) → ℤ)
    (above : ∀ r, lower r ≤ x r) (tight : ∃ r, x r = lower r)
    (j : Fin (m+1)) (allocated : lower j < x j) :
    recovery m (charge m (consume m x j)) lower =
      recovery m (charge m x) lower - 1 := by
  have ha : ∀ r, lower r ≤ consume m x j r := by
    intro r
    by_cases hj : r = j
    · subst r; simp only [consume, if_pos rfl]; omega
    · simpa [consume, hj] using above r
  have ht : ∃ r, consume m x j r = lower r := by
    obtain ⟨r, hr⟩ := tight
    have hj : r ≠ j := by intro he; subst r; omega
    exact ⟨r, by simp [consume, hj, hr]⟩
  rw [recovery_exact m _ _ ha ht, recovery_exact m x lower above tight, consume_sum]

/-- If an occupied phase has no allocated repeat, reusing it increases the
residual bill by radix-1. Including the symbol just spent costs ONE WHOLE
RADIX. This is a periodic recovery penalty, not a local tree estimate. -/
theorem unallocated_repeat_cost (m : ℕ) (x lower : Fin (m+1) → ℤ)
    (above : ∀ r, lower r ≤ x r) (j : Fin (m+1)) (empty : x j = lower j) :
    recovery m (charge m (consume m x j)) lower =
      recovery m (charge m x) lower + (m+1 : ℕ) - 1 := by
  let repaired : Fin (m+1) → ℤ := fun r => consume m x j r + 1
  have ha : ∀ r, lower r ≤ repaired r := by
    intro r
    dsimp [repaired, consume]
    split_ifs <;> have hh := above r <;> omega
  have ht : ∃ r, repaired r = lower r := by
    exact ⟨j, by simp [repaired, consume, empty]⟩
  have hc : charge m repaired = charge m (consume m x j) := by
    funext r
    unfold charge
    dsimp [repaired]
    ring
  have hs : (∑ r, repaired r) = (∑ r, x r) + (m+1 : ℕ) - 1 := by
    simp only [repaired, Finset.sum_add_distrib, consume_sum]
    simp
    ring
  have he := recovery_exact m repaired lower ha ht
  rw [hc, hs, ← recovery_exact m x lower above ⟨j, empty⟩] at he
  exact he

end Coeff2.Charlieplex.OccupationRecoveryClock

#print axioms Coeff2.Charlieplex.OccupationRecoveryClock.coupled_recovery
#print axioms Coeff2.Charlieplex.OccupationRecoveryClock.closed_charge_solver
#print axioms Coeff2.Charlieplex.OccupationRecoveryClock.leastCopies_minimum
#print axioms Coeff2.Charlieplex.OccupationRecoveryClock.fresh_write_cost
#print axioms Coeff2.Charlieplex.OccupationRecoveryClock.allocated_repeat_cost
#print axioms Coeff2.Charlieplex.OccupationRecoveryClock.unallocated_repeat_cost
