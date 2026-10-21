import Mathlib.Data.List.Rotate
import Mathlib.Tactic

/-!
# Size versus score in the Houston--Egan kernel grammar

Here `m = n - 2`. The literal parser permits digits `1,...,m+1`; a dash
is a separate slot with zero coverage. `digits` retains the digit order,
while `h` counts the dashes. The elementary bounds below need no assumptions
on where the dashes occur, so they also hold for every well-formed specifier.

These are necessary conditions for this grammar, not existence theorems.
In particular, distinct occupied rotation orbits and a tree completion are
NOT inferred from a numerical score. The meaning of `q` is score / (n-2);
it becomes a character saving from E(n) only for a valid closed completion.
-/

namespace Coeff2.Charlieplex.KernelScaling

/-- Total shortfall of the positive digits from their permitted maximum. -/
def deficit (m : ℕ) (digits : List ℕ) : ℕ :=
  (digits.map fun a => m + 1 - a).sum

/-- Exactly the score used by `KernelFinder.c` and `parseNSK`. -/
def score (m : ℕ) (digits : List ℕ) (h : ℕ) : ℤ :=
  (digits.sum : ℤ) - (m : ℤ) * ((digits.length : ℤ) + h)

theorem coverage_add_deficit (m : ℕ) (digits : List ℕ)
    (hbound : ∀ a ∈ digits, a ≤ m + 1) :
    digits.sum + deficit m digits = (m + 1) * digits.length := by
  induction digits with
  | nil => simp [deficit]
  | cons a as ih =>
    have ha := hbound a List.mem_cons_self
    have ht := ih (fun b hb => hbound b (List.mem_cons_of_mem a hb))
    simp only [deficit, List.map_cons, List.sum_cons, List.length_cons] at *
    have hpart : a + (m + 1 - a) = m + 1 := by omega
    nlinarith

/-- Every maximal digit earns one point; deficits and dashes consume points. -/
theorem score_eq_digits_sub_deficit (m h : ℕ) (digits : List ℕ)
    (hbound : ∀ a ∈ digits, a ≤ m + 1) :
    score m digits h = (digits.length : ℤ) - deficit m digits - (m : ℤ) * h := by
  have hc : (digits.sum : ℤ) + deficit m digits =
      ((m : ℤ) + 1) * digits.length := by
    exact_mod_cast coverage_add_deficit m digits hbound
  dsimp [score]
  nlinarith

/-- Exact digit-count scaling, derived from the finite list of digits. -/
theorem digit_count_eq (m q h : ℕ) (digits : List ℕ)
    (hbound : ∀ a ∈ digits, a ≤ m + 1)
    (hscore : score m digits h = (m : ℤ) * q) :
    digits.length = m * (q + h) + deficit m digits := by
  have hs := score_eq_digits_sub_deficit m h digits hbound
  have hi : (digits.length : ℤ) =
      (m : ℤ) * ((q : ℤ) + h) + deficit m digits := by
    nlinarith
  exact_mod_cast hi

/-- Exact occupied-orbit *accounting*. It counts distinct orbits only when
the kernel's independent no-repetition check has succeeded. -/
theorem coverage_eq (m q h : ℕ) (digits : List ℕ)
    (hbound : ∀ a ∈ digits, a ≤ m + 1)
    (hscore : score m digits h = (m : ℤ) * q) :
    digits.sum = m * ((m + 1) * (q + h) + deficit m digits) := by
  have hd := digit_count_eq m q h digits hbound hscore
  have hc := coverage_add_deficit m digits hbound
  rw [hd] at hc
  nlinarith

theorem coverage_lower_bound (m q h : ℕ) (digits : List ℕ)
    (hbound : ∀ a ∈ digits, a ≤ m + 1)
    (hscore : score m digits h = (m : ℤ) * q) :
    m * (m + 1) * (q + h) ≤ digits.sum := by
  rw [coverage_eq m q h digits hbound hscore]
  nlinarith

/-- Relative to the standard score-m kernel, q=t+1. If r ordinary attached
blocks are absorbed into the replacement kernel, each contributes m new
rotation orbits. The number of absorbed blocks is forced, not guessed. -/
theorem absorbed_blocks_eq (m t h r : ℕ) (digits : List ℕ)
    (hm : 0 < m) (hbound : ∀ a ∈ digits, a ≤ m + 1)
    (hscore : score m digits h = (m : ℤ) * (t + 1))
    (hcoverage : digits.sum = m * (m + 1) + m * r) :
    r = (m + 1) * (t + h) + deficit m digits := by
  have hc := coverage_eq m (t + 1) h digits hbound (by exact_mod_cast hscore)
  have heq : m * r = m * ((m + 1) * (t + h) + deficit m digits) := by
    nlinarith
  exact Nat.eq_of_mul_eq_mul_left hm heq

theorem absorbed_blocks_lower_bound (m t h r : ℕ) (digits : List ℕ)
    (hm : 0 < m) (hbound : ∀ a ∈ digits, a ≤ m + 1)
    (hscore : score m digits h = (m : ℤ) * (t + 1))
    (hcoverage : digits.sum = m * (m + 1) + m * r) :
    (m + 1) * (t + h) ≤ r := by
  rw [absorbed_blocks_eq m t h r digits hm hbound hscore hcoverage]
  omega

/-- A score target already forces a slot budget before occupation search. -/
theorem slot_budget_lower_bound (m q h : ℕ) (digits : List ℕ)
    (hbound : ∀ a ∈ digits, a ≤ m + 1)
    (htarget : (m : ℤ) * q ≤ score m digits h) :
    m * q + (m + 1) * h + deficit m digits ≤ digits.length + h := by
  have hs := score_eq_digits_sub_deficit m h digits hbound
  have hi : (m : ℤ) * q + ((m : ℤ) + 1) * h + deficit m digits ≤
      (digits.length : ℤ) + h := by nlinarith
  exact_mod_cast hi

theorem deficit_append (m : ℕ) (xs ys : List ℕ) :
    deficit m (xs ++ ys) = deficit m xs + deficit m ys := by
  simp [deficit]

/-- Safe prefix rejection: subsequent digits cannot erase the deficit or
dash costs already committed. No claim about continuation existence is used. -/
theorem prefix_budget_reject (m q h extraH budget : ℕ) (pre post : List ℕ)
    (hbound : ∀ a ∈ pre ++ post, a ≤ m + 1)
    (hbudget : (pre ++ post).length + (h + extraH) ≤ budget)
    (hreject : budget < m * q + (m + 1) * h + deficit m pre) :
    ¬ (m : ℤ) * q ≤ score m (pre ++ post) (h + extraH) := by
  intro htarget
  have hs := slot_budget_lower_bound m q (h + extraH) (pre ++ post) hbound htarget
  rw [deficit_append] at hs
  nlinarith

/-- The optimistic, zero-deficit/no-dash orbit floor. Not always realizable. -/
def orbitFloor (m q : ℕ) : ℕ := m * (m + 1) * q

/-- Full permutation vertices when these rotation orbits are disjoint. -/
def vertexFloor (m q : ℕ) : ℕ := (m + 2) * orbitFloor m q

theorem orbitFloor_succ_saving (m q : ℕ) :
    orbitFloor m (q + 1) = orbitFloor m q + m * (m + 1) := by
  simp only [orbitFloor]
  ring

theorem orbitFloor_succ_order (m q : ℕ) :
    orbitFloor (m + 1) q = orbitFloor m q + 2 * (m + 1) * q := by
  simp only [orbitFloor]
  ring

theorem vertexFloor_succ_order (m q : ℕ) :
    vertexFloor (m + 1) q = vertexFloor m q + 3 * (m + 1) * (m + 2) * q := by
  simp only [vertexFloor, orbitFloor]
  ring

/-! ## Literal periodicity of consecutive maximal canonical digits

Unlike the score identities, the following lemmas use the actual reversed-
prefix successor operations. Other proper connectors of the same weight
need not have this action. This restriction is intentional.
-/

/-- The actual canonical weight-k edge: discard k symbols, append reversed. -/
def reversePrefixStep {α : Type*} (k : ℕ) (p : List α) : List α :=
  p.drop k ++ (p.take k).reverse

/-- Traverse the remaining weight-one edges of a complete rotation orbit. -/
def finishOrbit {α : Type*} (p : List α) : List α :=
  p.rotate (p.length - 1)

/-- Between two orbit starts inside the same digit. -/
def nextOrbit {α : Type*} (p : List α) : List α :=
  reversePrefixStep 2 (finishOrbit p)

/-- Traverse a maximal digit and its following canonical weight-three edge. -/
def fullDigitNext {α : Type*} (p : List α) : List α :=
  reversePrefixStep 3 (finishOrbit ((nextOrbit^[p.length - 2]) p))

theorem finishOrbit_concat {α : Type*} (xs : List α) (a : α) :
    finishOrbit (xs ++ [a]) = a :: xs := by
  simp [finishOrbit, List.rotate_append_length_eq]

theorem nextOrbit_concat {α : Type*} (xs : List α) (a : α) :
    nextOrbit (xs ++ [a]) = xs.rotate 1 ++ [a] := by
  rw [nextOrbit, finishOrbit_concat]
  cases xs with
  | nil => simp [reversePrefixStep]
  | cons x xs => simp [reversePrefixStep, List.rotate_cons_succ, List.append_assoc]

theorem iterate_nextOrbit_concat {α : Type*} (xs : List α) (a : α) (k : ℕ) :
    (nextOrbit^[k]) (xs ++ [a]) = xs.rotate k ++ [a] := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, nextOrbit_concat, List.rotate_rotate]

/-- A maximal digit rotates the first n-2 symbols and fixes the last two. -/
theorem fullDigitNext_concat {α : Type*} (xs : List α) (a b : α)
    (hne : xs ≠ []) :
    fullDigitNext (xs ++ [a,b]) = xs.rotate 1 ++ [a,b] := by
  have hlen : (xs ++ [a,b]).length - 2 = xs.length := by simp
  rw [fullDigitNext, hlen]
  have hiter : (nextOrbit^[xs.length]) (xs ++ [a,b]) = (a :: xs) ++ [b] := by
    simpa [List.append_assoc, List.rotate_append_length_eq] using
      iterate_nextOrbit_concat (xs ++ [a]) b xs.length
  rw [hiter, finishOrbit_concat]
  cases xs with
  | nil => exact False.elim (hne rfl)
  | cons x xs =>
    simp [reversePrefixStep, List.rotate_cons_succ, List.append_assoc]

theorem iterate_fullDigitNext_concat {α : Type*} (xs : List α) (a b : α)
    (hne : xs ≠ []) (k : ℕ) :
    (fullDigitNext^[k]) (xs ++ [a,b]) = xs.rotate k ++ [a,b] := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih,
      fullDigitNext_concat _ a b (by simpa using hne), List.rotate_rotate]

/-- Literal return after n-2 maximal canonical digits, for every starting
word. No permutation cardinality calculation or numerical search is used. -/
theorem fullDigitNext_period {α : Type*} (xs : List α) (a b : α)
    (hne : xs ≠ []) :
    (fullDigitNext^[xs.length]) (xs ++ [a,b]) = xs ++ [a,b] := by
  rw [iterate_fullDigitNext_concat xs a b hne, List.rotate_length]

/-- These are actual permutation states at the starts of consecutive
maximal digits, not free graph labels or unspecified incidence data. -/
def fullDigitStarts {α : Type*} (p : List α) (k : ℕ) : List (List α) :=
  (List.range k).map fun j => (fullDigitNext^[j]) p

/-- No-repeat occupation forbids more than n-2 consecutive maximal digits. -/
theorem full_run_length_le {α : Type*} (xs : List α) (a b : α)
    (hne : xs ≠ []) (k : ℕ)
    (hno : (fullDigitStarts (xs ++ [a,b]) k).Nodup) :
    k ≤ xs.length := by
  by_contra h
  have hk : xs.length < k := by omega
  have hx : 0 < xs.length := List.length_pos_iff.mpr hne
  have hinj := List.inj_on_of_nodup_map hno
  have heq : (fullDigitNext^[0]) (xs ++ [a,b]) =
      (fullDigitNext^[xs.length]) (xs ++ [a,b]) := by
    simp [fullDigitNext_period xs a b hne]
  have hbad := hinj (x := 0) (List.mem_range.mpr (by omega))
    (y := xs.length) (List.mem_range.mpr hk) heq
  omega

/-- The optimistic all-maximal construction cannot exceed score n-2 when
its literal digit-start states are distinct. This is an occupation result,
not just the unconstrained score identity. -/
theorem maximal_only_score_le {α : Type*} (xs : List α) (a b : α)
    (hne : xs ≠ []) (k : ℕ)
    (hno : (fullDigitStarts (xs ++ [a,b]) k).Nodup) :
    score xs.length (List.replicate k (xs.length + 1)) 0 ≤ (xs.length : ℤ) := by
  have hk := full_run_length_le xs a b hne k hno
  have hsum : (List.replicate k (xs.length + 1)).sum = k * (xs.length + 1) := by
    simp [List.sum_replicate]
  rw [score, hsum, List.length_replicate]
  push_cast
  have hi : (k : ℤ) ≤ xs.length := by exact_mod_cast hk
  nlinarith

/-! ## Small checks and corpus inventory checks (not realization certificates) -/

namespace Tests

/-- This is the digit histogram, not a reordered realizable kernel claim. -/
def inventory5905 : List ℕ :=
  List.replicate 56 6 ++ List.replicate 12 4 ++ List.replicate 2 3

theorem inventory5905_scaling :
    inventory5905.length = 70 ∧ inventory5905.sum = 390 ∧
    deficit 5 inventory5905 = 30 ∧ score 5 inventory5905 5 = 15 ∧
    (72 : ℕ) = 6 * (2 + 5) + 30 := by
  norm_num [inventory5905, deficit, score]

/-- Inventory of the existing score-12 candidate; completion is not asserted. -/
def inventoryEightCandidate : List ℕ :=
  List.replicate 16 7 ++ List.replicate 4 5

theorem eight_candidate_scaling :
    inventoryEightCandidate.length = 20 ∧ inventoryEightCandidate.sum = 132 ∧
    deficit 6 inventoryEightCandidate = 8 ∧
    score 6 inventoryEightCandidate 0 = 12 ∧
    (15 : ℕ) = 7 * (1 + 0) + 8 := by
  norm_num [inventoryEightCandidate, deficit, score]

theorem order_seven_eight_nine_floors :
    orbitFloor 5 1 = 30 ∧ orbitFloor 6 1 = 42 ∧ orbitFloor 7 1 = 56 ∧
    vertexFloor 5 1 = 210 ∧ vertexFloor 6 1 = 336 ∧ vertexFloor 7 1 = 504 := by
  norm_num [orbitFloor, vertexFloor]

theorem eight_maximal_start_repeats :
    (fullDigitNext^[6]) [1,2,3,4,5,6,7,8] = ([1,2,3,4,5,6,7,8] : List ℕ) := by
  simpa using fullDigitNext_period ([1,2,3,4,5,6] : List ℕ) 7 8 (by simp)

theorem eight_seven_maximal_digits_rejected :
    ¬ (fullDigitStarts ([1,2,3,4,5,6,7,8] : List ℕ) 7).Nodup := by
  intro h
  have hb := full_run_length_le ([1,2,3,4,5,6] : List ℕ) 7 8 (by simp) 7 h
  norm_num at hb

end Tests

end Coeff2.Charlieplex.KernelScaling
