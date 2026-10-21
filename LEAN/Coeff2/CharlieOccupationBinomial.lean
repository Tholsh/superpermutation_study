import Coeff2.CharlieLiteralBellman
import Mathlib.Data.Nat.Choose.Sum

/-!
# Exact binomial collision moments, with a literal occupation application

This is inclusion-exclusion in the number of collision writes, not a fitted
polynomial in time. It retains all orders up to an explicit bound. The literal
application scans every window of every alphabet-valid suffix. No-repeat and
full coverage are different requirements; the last theorem keeps both explicit.
-/

namespace Coeff2.Charlieplex

set_option maxHeartbeats 50000

open Finset

def binomialDefectMoment {α : Type*} (sample : Finset α) (defect : α → ℕ)
    (order : ℕ) : ℕ :=
  ∑ outcome ∈ sample, (defect outcome).choose order

theorem alternating_binomial_zero_indicator (d cap : ℕ) (hd : d ≤ cap) :
    (∑ j ∈ range (cap + 1), (-1 : ℤ) ^ j * (d.choose j : ℤ)) =
      if d = 0 then 1 else 0 := by
  calc
    _ = ∑ j ∈ range (d + 1), (-1 : ℤ) ^ j * (d.choose j : ℤ) := by
      symm
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro j _ hj
      have hjd : d < j := by simp only [mem_range, not_lt] at hj; omega
      simp [Nat.choose_eq_zero_of_lt hjd]
    _ = _ := Int.alternating_sum_range_choose

/-- Exact zero-defect count, including every required intersection order. -/
theorem card_zero_defect_eq_binomial_moments {α : Type*}
    (sample : Finset α) (defect : α → ℕ) (cap : ℕ)
    (hcap : ∀ outcome ∈ sample, defect outcome ≤ cap) :
    ((sample.filter fun outcome => defect outcome = 0).card : ℤ) =
      ∑ j ∈ range (cap + 1), (-1 : ℤ) ^ j *
        (binomialDefectMoment sample defect j : ℤ) := by
  classical
  rw [show ((sample.filter fun outcome => defect outcome = 0).card : ℤ) =
      ∑ outcome ∈ sample, (if defect outcome = 0 then (1 : ℤ) else 0) by
        simp [Finset.sum_boole]]
  simp only [binomialDefectMoment, Nat.cast_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro outcome houtcome
  exact (alternating_binomial_zero_indicator _ _ (hcap outcome houtcome)).symm

/-- Number of repeated permutation-window writes in the literal text. -/
def literalRepeatDefect (n : ℕ) (text : List ℕ) : ℕ :=
  (literalPermutationWindows n text).length -
    (literalPermutationWindows n text).toFinset.card

theorem literalRepeatDefect_zero_iff (n : ℕ) (text : List ℕ) :
    literalRepeatDefect n text = 0 ↔ (literalPermutationWindows n text).Nodup := by
  let windows := literalPermutationWindows n text
  have hcard : windows.toFinset.card ≤ windows.length := List.toFinset_card_le windows
  have heq : windows.toFinset.card = windows.length ↔ windows.Nodup :=
    Multiset.toFinset_card_eq_card_iff_nodup (m := (windows : Multiset (List ℕ)))
  change windows.length - windows.toFinset.card = 0 ↔ windows.Nodup
  rw [← heq]
  omega

theorem literalRepeatDefect_le_length (n : ℕ) (text : List ℕ) :
    literalRepeatDefect n text ≤ text.length + 1 := by
  have hlength : (literalPermutationWindows n text).length ≤ text.length + 1 := by
    unfold literalPermutationWindows
    calc
      _ ≤ (text.tails.map (fun suffix => suffix.take n)).length := List.length_filter_le ..
      _ = _ := by simp
  exact (Nat.sub_le _ _).trans hlength

/-- Candidate suffixes have fixed literal character length, not fixed edge count. -/
def literalNoRepeatSuffixes (n horizon : ℕ) (text : List ℕ) : Finset (List ℕ) :=
  (literalSuffixes n horizon).filter fun suffix =>
    (literalPermutationWindows n (text ++ suffix)).Nodup

theorem literalNoRepeatSuffixCount_binomial (n horizon : ℕ) (text : List ℕ) :
    ((literalNoRepeatSuffixes n horizon text).card : ℤ) =
      ∑ j ∈ range (text.length + horizon + 2), (-1 : ℤ) ^ j *
        (binomialDefectMoment (literalSuffixes n horizon)
          (fun suffix => literalRepeatDefect n (text ++ suffix)) j : ℤ) := by
  have hcap : ∀ suffix ∈ literalSuffixes n horizon,
      literalRepeatDefect n (text ++ suffix) ≤ text.length + horizon + 1 := by
    intro suffix hsuffix
    have hlen := (mem_literalSuffixes n horizon suffix).mp hsuffix
    simpa [List.length_append, hlen.1] using literalRepeatDefect_le_length n (text ++ suffix)
  simpa only [literalNoRepeatSuffixes, literalRepeatDefect_zero_iff, Nat.add_assoc,
    Nat.reduceAdd] using
      card_zero_defect_eq_binomial_moments (literalSuffixes n horizon)
        (fun suffix => literalRepeatDefect n (text ++ suffix)) (text.length + horizon + 1) hcap

/-- Same identity for actual full-coverage completions with the additional
no-repeat requirement. It does not assert that all superpermutations are exact-once. -/
theorem literalExactOnceCompletionCount_binomial (n budget horizon : ℕ)
    (text : List ℕ) :
    (((literalSuccessfulSuffixes n budget horizon (literalStateOf n text)).filter
      fun suffix => (literalPermutationWindows n (text ++ suffix)).Nodup).card : ℤ) =
      ∑ j ∈ range (text.length + horizon + 2), (-1 : ℤ) ^ j *
        (binomialDefectMoment (literalSuccessfulSuffixes n budget horizon (literalStateOf n text))
          (fun suffix => literalRepeatDefect n (text ++ suffix)) j : ℤ) := by
  have hcap : ∀ suffix ∈ literalSuccessfulSuffixes n budget horizon (literalStateOf n text),
      literalRepeatDefect n (text ++ suffix) ≤ text.length + horizon + 1 := by
    intro suffix hsuffix
    have hmem := (Finset.mem_filter.mp hsuffix).1
    have hlen := (mem_literalSuffixes n horizon suffix).mp hmem
    simpa [List.length_append, hlen.1] using literalRepeatDefect_le_length n (text ++ suffix)
  simpa only [literalRepeatDefect_zero_iff, Nat.add_assoc, Nat.reduceAdd] using
    card_zero_defect_eq_binomial_moments
      (literalSuccessfulSuffixes n budget horizon (literalStateOf n text))
      (fun suffix => literalRepeatDefect n (text ++ suffix)) (text.length + horizon + 1) hcap

end Coeff2.Charlieplex
