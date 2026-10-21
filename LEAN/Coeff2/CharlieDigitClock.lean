import Coeff2.CharlieKernelScaling

/-! Exact canonical digit actions. These do not assert occupation, completion,
or that a gain-three construction lifts. The final weight-three connector is
included; a dash uses a different connector. -/
namespace Coeff2.Charlieplex.KernelScaling

def digitNext {α : Type*} (a : ℕ) (p : List α) : List α :=
  reversePrefixStep 3 (finishOrbit ((nextOrbit^[a - 1]) p))

/-- A digit first rotates the first n-1 positions. It then removes two
symbols from their front and appends them in reverse, fixing the marker. -/
theorem digitNext_concat {α : Type*} (xs : List α) (b : α) (a : ℕ) :
    digitNext a (xs ++ [b]) =
      (xs.rotate (a - 1)).drop 2 ++
        ((xs.rotate (a - 1)).take 2).reverse ++ [b] := by
  rw [digitNext, iterate_nextOrbit_concat, finishOrbit_concat]
  simp [reversePrefixStep, List.append_assoc]

/-- Moving d phases forwards before a deficient digit exactly compensates
its deficit d. No state enumeration and no restriction on the symbols. -/
theorem deficit_phase_compensation {α : Type*} (xs : List α) (b : α)
    (d : ℕ) (hd : d < xs.length) :
    digitNext (xs.length - d) (xs.rotate d ++ [b]) =
      digitNext xs.length (xs ++ [b]) := by
  rw [digitNext_concat, digitNext_concat, List.rotate_rotate]
  have h : d + (xs.length - d - 1) = xs.length - 1 := by omega
  rw [h]

/-- Explicit backwards-clock form of the same identity. Rotating r-d
places equals rotating backwards d places on a clock of length r. -/
theorem digitNext_from_shift {α : Type*} (xs : List α) (b : α)
    (d : ℕ) (hd : d < xs.length) :
    digitNext (xs.length - d) (xs ++ [b]) =
      digitNext xs.length (xs.rotate (xs.length - d) ++ [b]) := by
  have h := deficit_phase_compensation (xs.rotate (xs.length - d)) b d
    (by simpa using hd)
  simp only [List.length_rotate, List.rotate_rotate] at h
  rw [Nat.sub_add_cancel (Nat.le_of_lt hd), List.rotate_length] at h
  exact h

theorem maximal_digit_eq {α : Type*} (xs : List α) (a b : α) :
    digitNext (xs.length + 1) (xs ++ [a,b]) =
      fullDigitNext (xs ++ [a,b]) := by
  simp [digitNext, fullDigitNext]

/-- The compensated deficient digit advances the n-2 clock once, leaving
the two last symbols fixed. This is an all-n literal-list identity. -/
theorem deficit_phase_clock {α : Type*} (xs : List α) (a b : α)
    (hne : xs ≠ []) (d : ℕ) (hd : d < (xs ++ [a]).length) :
    digitNext ((xs ++ [a]).length - d) ((xs ++ [a]).rotate d ++ [b]) =
      xs.rotate 1 ++ [a,b] := by
  rw [deficit_phase_compensation _ b d hd]
  simpa only [List.length_append, List.length_singleton, List.append_assoc,
    List.singleton_append] using
      (maximal_digit_eq xs a b).trans (fullDigitNext_concat xs a b hne)

/-- Conditional inventory law for the 5905 six-block defect skeleton:
twelve deficit-two digits, two deficit-three digits, five dashes, and k
maximal digits. This does not certify any ordering of those digits. -/
theorem inventory5905_gain_three (m k : ℤ) :
    k + 14 - (12 * 2 + 2 * 3) - 5 * m = 3 * m ↔
      k = 8 * m + 16 := by omega

/-- In the tested mirrored family s of eight run pairs grow by n-7.
Exactly four pairs preserve gain three algebraically above n=7. -/
theorem mirrored_growth_gain_three (t s : ℕ) (ht : 0 < t) :
    (15 : ℤ) + (2 * s - 5) * t = 3 * (5 + t) ↔ s = 4 := by
  constructor
  · intro h
    have ht' : (0 : ℤ) < t := by exact_mod_cast ht
    have heq : ((s : ℤ) - 4) * t = 0 := by nlinarith
    have hs := (mul_eq_zero.mp heq).resolve_right (ne_of_gt ht')
    omega
  · intro h
    subst s
    ring

end Coeff2.Charlieplex.KernelScaling
