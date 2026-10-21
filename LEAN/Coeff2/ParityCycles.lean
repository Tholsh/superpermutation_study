/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Coeff2.Auxiliary
import Mathlib.GroupTheory.Perm.Fin

/-!
# Parity of weight-1 rotation cycles

A weight-1 move cyclically rotates all `n` positions.  The rotation has sign
`(-1)^(n-1)`.  Consequently:

* at odd radix, every permutation in a rotation orbit has the same sign;
* at positive even radix, every single rotation step flips sign.

Thus odd-radix `1`-cycles have two kinds, called `up` and `down` below.  The
even-radix law is retained rather than hidden: it is the parity alternation
that appears at the next level of the factorial chain.
-/

namespace Coeff2

namespace ParityCycles

abbrev Permutation (n : ℕ) := Equiv.Perm (Fin n)

/-- The positional permutation underlying a weight-1 cyclic rotation. -/
def oneStepRotation (n : ℕ) : Permutation n := finRotate n

/-! ## Bridge to the project's list-valued permutation words

The project writes a permutation as a list such as `[1, 2, 3, 4]`.  Its
weight-1 successor is `rho w = w.rotate 1`; for a nonempty list this moves
the first symbol to the end.  The definitions below turn that concrete list
into the ordinary permutation "position maps to symbol", so its sign is no
longer being computed in a parallel model.
-/

/-- `rho` in explicit list notation: move the first symbol to the end. -/
@[simp]
theorem rho_cons (a : ℕ) (t : List ℕ) : rho (a :: t) = t ++ [a] := by
  simp [rho]

/-! ## Directed weight-one incidence -/

/-- Rotation by one is injective on words.  This is the algebraic reason a
lifted vertex cannot have two different weight-one predecessors. -/
theorem rho_injective : Function.Injective rho := by
  exact List.rotate_injective 1

/-- Every permutation word has exactly one weight-one successor. -/
theorem existsUnique_weightOne_successor {n : ℕ} (hn : 1 ≤ n)
    {u : List ℕ} (hu : IsPermWord n u) :
    ∃! v : List ℕ, IsPermWord n v ∧ wt n u v = 1 := by
  refine ⟨rho u, ⟨isPermWord_rotate hu 1, wt_rho hn hu⟩, ?_⟩
  intro v hv
  exact eq_rho_of_wt_one hn hu hv.1 hv.2

/-- Two weight-one edges with the same target have the same source.  Thus a
lifted permutation vertex has at most one incoming weight-one edge. -/
theorem weightOne_predecessor_unique {n : ℕ} (hn : 1 ≤ n)
    {u v z : List ℕ} (hu : IsPermWord n u) (hv : IsPermWord n v)
    (hz : IsPermWord n z) (huv : wt n u v = 1) (hzv : wt n z v = 1) :
    u = z := by
  have h₁ : v = rho u := eq_rho_of_wt_one hn hu hv huv
  have h₂ : v = rho z := eq_rho_of_wt_one hn hz hv hzv
  exact rho_injective (h₁.symm.trans h₂)

/-- At radix at least three, a directed weight-one edge is not weight one in
reverse.  The reverse course requires the remaining `n-1` forward phases. -/
theorem weightOne_not_weightOne_reverse {n : ℕ} (hn : 3 ≤ n)
    {u v : List ℕ} (hu : IsPermWord n u) (hv : IsPermWord n v)
    (huv : wt n u v = 1) : wt n v u ≠ 1 := by
  intro hvu
  have hnpos : 1 ≤ n := by omega
  have hforward : v = rho u := eq_rho_of_wt_one hnpos hu hv huv
  have hreverse : u = rho v := eq_rho_of_wt_one hnpos hv hu hvu
  rw [hforward] at hreverse
  have hrot : u.rotate 0 = u.rotate 2 := by
    simpa [rho, List.rotate_rotate] using hreverse
  have hzero_lt : 0 < u.length := by rw [hu.length]; omega
  have htwo_lt : 2 < u.length := by rw [hu.length]; omega
  have : (0 : ℕ) = 2 := rotate_injOn_lt hu.nodup hzero_lt htwo_lt hrot
  omega

/-- The quotient rotation class of an `n`-symbol permutation has exactly `n`
distinct lifted phase representatives.  Each representative still has only
the single directed incidence proved above. -/
theorem wordOneCycle_has_exactly_n_phase_lifts {n : ℕ} (hn : 1 ≤ n)
    {u : List ℕ} (hu : IsPermWord n u) :
    {v : List ℕ | rotClass v = rotClass u}.ncard = n := by
  rw [ncard_classMembers hu.nodup (hu.ne_nil hn), hu.length]

/-! ## Exact locking of a weight-one course -/

/-- Iterating the unique weight-one successor `k` times is exactly left
rotation by `k` positions. -/
theorem rho_iterate_eq_rotate (w : List ℕ) (k : ℕ) :
    rho^[k] w = w.rotate k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      simp [rho, List.rotate_rotate]

/-- Exact return law for a permutation word: its `k`-th weight-one phase is
the initial phase exactly when the radix divides `k`. -/
theorem rho_iterate_eq_self_iff_dvd {n : ℕ} (hn : 1 ≤ n)
    {u : List ℕ} (hu : IsPermWord n u) (k : ℕ) :
    rho^[k] u = u ↔ n ∣ k := by
  rw [rho_iterate_eq_rotate, hu.nodup.rotate_eq_self_iff, hu.length]
  simp only [hu.ne_nil hn, or_false]
  exact Nat.dvd_iff_mod_eq_zero.symm

/-- The first full course of `n` weight-one moves closes. -/
theorem rho_iterate_radix_eq_self {n : ℕ} (hn : 1 ≤ n)
    {u : List ℕ} (hu : IsPermWord n u) : rho^[n] u = u := by
  exact (rho_iterate_eq_self_iff_dvd hn hu n).2 (dvd_refl n)

/-- No positive proper prefix of the `n`-phase weight-one course returns to
its initial permutation. -/
theorem rho_iterate_ne_self_before_radix {n k : ℕ} (hn : 1 ≤ n)
    {u : List ℕ} (hu : IsPermWord n u) (hkpos : 0 < k) (hk : k < n) :
    rho^[k] u ≠ u := by
  intro hreturn
  have hdvd : n ∣ k := (rho_iterate_eq_self_iff_dvd hn hu k).1 hreturn
  have hnle : n ≤ k := Nat.le_of_dvd hkpos hdvd
  omega

/-- The `n` lifted phases are pairwise distinct. -/
theorem rho_phases_injective {n : ℕ} {u : List ℕ} (hu : IsPermWord n u) :
    Function.Injective (fun phase : Fin n => rho^[phase.1] u) := by
  intro i j hij
  apply Fin.ext
  change rho^[i.1] u = rho^[j.1] u at hij
  rw [rho_iterate_eq_rotate, rho_iterate_eq_rotate] at hij
  exact rotate_injOn_lt hu.nodup
    (by rw [hu.length]; exact i.2)
    (by rw [hu.length]; exact j.2) hij

/-- **Course locking.**  A sequence of permutation words connected entirely
by weight-one edges is forced: its `k`-th word is the `k`-fold rotation of its
initial word. -/
theorem weightOne_course_forced {n : ℕ} (hn : 1 ≤ n)
    (course : ℕ → List ℕ) (hperm : ∀ k, IsPermWord n (course k))
    (hstep : ∀ k, wt n (course k) (course (k + 1)) = 1) (k : ℕ) :
    course k = rho^[k] (course 0) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hnext : course (k + 1) = rho (course k) :=
        eq_rho_of_wt_one hn (hperm k) (hperm (k + 1)) (hstep k)
      rw [hnext, ih, Function.iterate_succ_apply']

/-- A weight-one course cannot repeat a vertex during its first `n` phases. -/
theorem weightOne_course_no_repeat_before_radix {n : ℕ} (hn : 1 ≤ n)
    (course : ℕ → List ℕ) (hperm : ∀ k, IsPermWord n (course k))
    (hstep : ∀ k, wt n (course k) (course (k + 1)) = 1)
    {i j : ℕ} (hi : i < n) (hj : j < n) (hij : course i = course j) : i = j := by
  have hforced_i := weightOne_course_forced hn course hperm hstep i
  have hforced_j := weightOne_course_forced hn course hperm hstep j
  have hiter : rho^[i] (course 0) = rho^[j] (course 0) :=
    hforced_i.symm.trans (hij.trans hforced_j)
  rw [rho_iterate_eq_rotate, rho_iterate_eq_rotate] at hiter
  exact rotate_injOn_lt (hperm 0).nodup
    (by rw [(hperm 0).length]; exact hi)
    (by rw [(hperm 0).length]; exact hj) hiter

/-- Exact return law for any all-weight-one course. -/
theorem weightOne_course_returns_iff_dvd {n k : ℕ} (hn : 1 ≤ n)
    (course : ℕ → List ℕ) (hperm : ∀ j, IsPermWord n (course j))
    (hstep : ∀ j, wt n (course j) (course (j + 1)) = 1) :
    course k = course 0 ↔ n ∣ k := by
  rw [weightOne_course_forced hn course hperm hstep k]
  exact rho_iterate_eq_self_iff_dvd hn (hperm 0) k

/-- The alphabet `{1, ..., n}` used by an `IsPermWord n`. -/
def Alphabet (n : ℕ) := {x : ℕ // x ∈ Finset.Icc 1 n}

/-- Convert a symbol in `{1, ..., n}` to its zero-based `Fin n` label. -/
def alphabetEquivFin (n : ℕ) : Alphabet n ≃ Fin n where
  toFun x := ⟨x.1 - 1, by
    have hx := x.2
    simp only [Finset.mem_Icc] at hx
    omega⟩
  invFun i := ⟨i.1 + 1, by
    simp only [Finset.mem_Icc]
    omega⟩
  left_inv x := by
    apply Subtype.ext
    have hx := x.2
    simp only [Finset.mem_Icc] at hx
    simp only
    omega
  right_inv i := by
    apply Fin.ext
    simp only
    omega

/-- The symbol of a permutation word at a zero-based position. -/
def wordSymbol {n : ℕ} (w : List ℕ) (hw : IsPermWord n w) (i : Fin n) : ℕ :=
  w.get (Fin.cast hw.length.symm i)

/-- Reading a permutation word by position is an equivalence with its alphabet. -/
noncomputable def wordEquiv {n : ℕ} (w : List ℕ) (hw : IsPermWord n w) :
    Fin n ≃ Alphabet n :=
  Equiv.ofBijective
    (fun i => ⟨wordSymbol w hw i, by
      have hm : wordSymbol w hw i ∈ w := by
        exact List.get_mem w (Fin.cast hw.length.symm i)
      have hf : wordSymbol w hw i ∈ w.toFinset := List.mem_toFinset.mpr hm
      rw [hw.toFinset_eq] at hf
      exact hf⟩)
    ⟨by
      intro i j hij
      have hval : wordSymbol w hw i = wordSymbol w hw j :=
        congrArg Subtype.val hij
      have hidx : Fin.cast hw.length.symm i = Fin.cast hw.length.symm j :=
        hw.nodup.get_inj_iff.mp hval
      exact Fin.cast_injective hw.length.symm hidx,
    by
      intro x
      have hm : x.1 ∈ w := by
        rw [← List.mem_toFinset, hw.toFinset_eq]
        exact x.2
      obtain ⟨j, hj⟩ := List.mem_iff_get.mp hm
      refine ⟨Fin.cast hw.length j, ?_⟩
      apply Subtype.ext
      simpa [wordSymbol] using hj⟩

/-- The ordinary permutation encoded by a project `IsPermWord` list. -/
noncomputable def wordPermutation {n : ℕ} (w : List ℕ) (hw : IsPermWord n w) :
    Permutation n :=
  (wordEquiv w hw).trans (alphabetEquivFin n)

/-- Permutation parity for the actual list representation used by the project. -/
noncomputable def wordSign {n : ℕ} (w : List ℕ) (hw : IsPermWord n w) : ℤˣ :=
  Equiv.Perm.sign (wordPermutation w hw)

/-- The list operation `rho` and the positional permutation `finRotate` are
the same move under `wordPermutation`. -/
theorem wordSymbol_rho {n : ℕ} (w : List ℕ) (hw : IsPermWord n w) (i : Fin n) :
    wordSymbol (rho w) (isPermWord_rotate hw 1) i =
      wordSymbol w hw (oneStepRotation n i) := by
  unfold wordSymbol rho oneStepRotation
  rw [List.get_rotate]
  congr 1
  apply Fin.ext
  simp only [Fin.cast]
  rw [finRotate_apply]
  simp [Fin.add_def, hw.length]

theorem wordPermutation_rho {n : ℕ} (w : List ℕ) (hw : IsPermWord n w) :
    wordPermutation (rho w) (isPermWord_rotate hw 1) =
      wordPermutation w hw * oneStepRotation n := by
  apply Equiv.ext
  intro i
  change alphabetEquivFin n
      (wordEquiv (rho w) (isPermWord_rotate hw 1) i) =
    alphabetEquivFin n (wordEquiv w hw (oneStepRotation n i))
  congr 1
  apply Subtype.ext
  exact wordSymbol_rho w hw i

/-- A member of the weight-1 rotation orbit based at `π`. -/
def InOneCycle {n : ℕ} (π τ : Permutation n) : Prop :=
  ∃ k : ℕ, τ = π * oneStepRotation n ^ k

/-- Concrete project words lie in one weight-1 cycle when their associated
positional permutations lie in the same rotation orbit. -/
def InWordOneCycle {n : ℕ} (w : List ℕ) (hw : IsPermWord n w)
    (v : List ℕ) (hv : IsPermWord n v) : Prop :=
  InOneCycle (wordPermutation w hw) (wordPermutation v hv)

/-- The two possible parity-locked kinds of an odd-radix `1`-cycle. -/
inductive OneCycleKind
  | up
  | down
  deriving DecidableEq, Repr

/-- Name the kind of a cycle by the sign of any chosen base permutation. -/
def oneCycleKind {n : ℕ} (π : Permutation n) : OneCycleKind :=
  if Equiv.Perm.sign π = 1 then .up else .down

/-- The `up`/`down` label of a concrete project permutation word. -/
noncomputable def wordOneCycleKind {n : ℕ} (w : List ℕ) (hw : IsPermWord n w) :
    OneCycleKind :=
  oneCycleKind (wordPermutation w hw)

@[simp]
theorem sign_oneStepRotation (n : ℕ) :
    Equiv.Perm.sign (oneStepRotation n) = (-1 : ℤˣ) ^ (n - 1) := by
  change Equiv.Perm.sign (finRotate n) = (-1 : ℤˣ) ^ (n - 1)
  exact sign_finRotate n

/-- Exact parity transport for the project's concrete list operation `rho`. -/
theorem wordSign_rho {n : ℕ} (w : List ℕ) (hw : IsPermWord n w) :
    wordSign (rho w) (isPermWord_rotate hw 1) =
      wordSign w hw * (-1 : ℤˣ) ^ (n - 1) := by
  unfold wordSign
  rw [wordPermutation_rho, Equiv.Perm.sign_mul, sign_oneStepRotation]

/-- The exact sign transport law after `k` weight-1 rotations. -/
theorem sign_rotate_pow {n : ℕ} (π : Permutation n) (k : ℕ) :
    Equiv.Perm.sign (π * oneStepRotation n ^ k) =
      Equiv.Perm.sign π * (((-1 : ℤˣ) ^ (n - 1)) ^ k) := by
  rw [Equiv.Perm.sign_mul, map_pow, sign_oneStepRotation]
  rfl

/-- At odd radix the whole weight-1 orbit is parity locked. -/
theorem oneCycle_parity_locked {n : ℕ} (hn : Odd n) (π : Permutation n) (k : ℕ) :
    Equiv.Perm.sign (π * oneStepRotation n ^ k) = Equiv.Perm.sign π := by
  rw [sign_rotate_pow]
  have heven : Even (n - 1) := by
    rcases hn with ⟨r, rfl⟩
    exact ⟨r, by omega⟩
  have hrot : (-1 : ℤˣ) ^ (n - 1) = 1 := heven.neg_one_pow
  rw [hrot]
  simp

/-- Concrete-word version: at odd radix, applying the project's `rho` once
does not change permutation sign. -/
theorem odd_wordSign_rho_locked {n : ℕ} (hn : Odd n)
    (w : List ℕ) (hw : IsPermWord n w) :
    wordSign (rho w) (isPermWord_rotate hw 1) = wordSign w hw := by
  rw [wordSign_rho (w := w) (hw := hw)]
  have heven : Even (n - 1) := Nat.Odd.sub_odd hn odd_one
  have hrot : (-1 : ℤˣ) ^ (n - 1) = 1 := heven.neg_one_pow
  rw [hrot]
  simp

/-- A literal weight-1 edge between odd-length project words preserves sign.
The existing theorem `eq_rho_of_wt_one` is what identifies the target with
`rho` of the source. -/
theorem odd_weightOne_preserves_wordSign {n : ℕ} (hn : Odd n)
    {u v : List ℕ} (hu : IsPermWord n u) (hv : IsPermWord n v)
    (hedge : wt n u v = 1) : wordSign v hv = wordSign u hu := by
  have hnpos : 1 ≤ n := by
    rcases hn with ⟨r, rfl⟩
    omega
  have hvrho : v = rho u := eq_rho_of_wt_one hnpos hu hv hedge
  subst v
  exact odd_wordSign_rho_locked hn u hu

/-- Superpermutation-language form: any two vertices in one odd-radix
weight-1 cycle have the same permutation sign. -/
theorem oneCycle_all_same_sign {n : ℕ} (hn : Odd n) {π τ : Permutation n}
    (hτ : InOneCycle π τ) : Equiv.Perm.sign τ = Equiv.Perm.sign π := by
  rcases hτ with ⟨k, rfl⟩
  exact oneCycle_parity_locked hn π k

/-- The requested list-language theorem: all words in one odd-radix
weight-1 cycle have the same sign. -/
theorem wordOneCycle_all_same_sign {n : ℕ} (hn : Odd n)
    {w v : List ℕ} {hw : IsPermWord n w} {hv : IsPermWord n v}
    (hcycle : InWordOneCycle w hw v hv) : wordSign v hv = wordSign w hw := by
  exact oneCycle_all_same_sign hn hcycle

/-- Therefore the `up`/`down` label is independent of which member of an
odd-radix `1`-cycle is used to compute it. -/
theorem oneCycle_kind_locked {n : ℕ} (hn : Odd n) {π τ : Permutation n}
    (hτ : InOneCycle π τ) : oneCycleKind τ = oneCycleKind π := by
  unfold oneCycleKind
  rw [oneCycle_all_same_sign hn hτ]

theorem wordOneCycle_kind_locked {n : ℕ} (hn : Odd n)
    {w v : List ℕ} {hw : IsPermWord n w} {hv : IsPermWord n v}
    (hcycle : InWordOneCycle w hw v hv) :
    wordOneCycleKind v hv = wordOneCycleKind w hw := by
  exact oneCycle_kind_locked hn hcycle

theorem oneCycle_kind_exhaustive {n : ℕ} (π : Permutation n) :
    oneCycleKind π = .up ∨ oneCycleKind π = .down := by
  unfold oneCycleKind
  split <;> simp_all

/-! ## The gauge-corrected invariant

Raw permutation sign is locked only at odd radix.  If a rotation phase is
retained as part of the state, its known sign can be divided back out.  The
result is locked at every radix.  This is the precise sense in which the
universal parity lock is a gauge statement.
-/

/-- Remove the known sign contributed by `k` rotations. -/
def phaseCorrectedSign {n : ℕ} (π : Permutation n) (k : ℕ) : ℤˣ :=
  Equiv.Perm.sign (π * oneStepRotation n ^ k) *
    (Equiv.Perm.sign (oneStepRotation n) ^ k)⁻¹

/-- **Gauge parity is always locked.**  No oddness hypothesis is needed once
the rotation phase is included in the state. -/
theorem phaseCorrectedSign_locked {n : ℕ} (π : Permutation n) (k : ℕ) :
    phaseCorrectedSign π k = Equiv.Perm.sign π := by
  unfold phaseCorrectedSign
  rw [sign_rotate_pow, sign_oneStepRotation, Int.units_inv_eq_self]
  rw [mul_assoc, Int.units_mul_self, mul_one]

/-- At odd radix the gauge correction is trivial, so the invariant is just
the raw sign of the rotated permutation. -/
theorem odd_phaseCorrectedSign_eq_raw {n : ℕ} (hn : Odd n)
    (π : Permutation n) (k : ℕ) :
    phaseCorrectedSign π k =
      Equiv.Perm.sign (π * oneStepRotation n ^ k) := by
  rw [phaseCorrectedSign_locked, oneCycle_parity_locked hn]

/-- At positive even radix, one weight-1 move reverses parity. -/
theorem even_radix_oneStep_sign {n : ℕ} (hpos : 0 < n) (hn : Even n)
    (π : Permutation n) :
    Equiv.Perm.sign (π * oneStepRotation n) =
      -(Equiv.Perm.sign π) := by
  rw [Equiv.Perm.sign_mul, sign_oneStepRotation]
  have hodd : Odd (n - 1) := by
    rcases hn with ⟨r, rfl⟩
    have hr : 0 < r := by omega
    exact ⟨r - 1, by omega⟩
  have hrot : (-1 : ℤˣ) ^ (n - 1) = -1 := hodd.neg_one_pow
  rw [hrot]
  simp

theorem even_radix_oneStep_flips {n : ℕ} (hpos : 0 < n) (hn : Even n)
    (π : Permutation n) :
    Equiv.Perm.sign (π * oneStepRotation n) ≠ Equiv.Perm.sign π := by
  rw [even_radix_oneStep_sign hpos hn]
  exact neg_units_ne_self _

end ParityCycles

end Coeff2
