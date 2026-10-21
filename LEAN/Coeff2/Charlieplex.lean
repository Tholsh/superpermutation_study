/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Coeff2.Breaks

/-!
# Charlieplexed parity and the signed Sylvester obstruction

This file formalizes the finite combinatorics behind a proposed quotient for
marked `2`-loops.

* A canonical ride has `m - 1` orbit indices and `m` rotation phases, hence
  `m * (m - 1)` coordinates.
* The same number counts directed non-loop channels on `m` pins.  We package
  this as an equivalence of finite types.
* Reversing the difference coordinate sends `h` to `m - 2 - h`.  When `m` is
  odd, this reverses its parity sheet.
* A basic Sylvester rewrite can exchange two words of opposite inversion
  parity.  Thus ordinary Sylvester classes cannot carry permutation parity;
  a signed double cover is genuinely necessary.

The first three points are unconditional finite arithmetic.  Connecting the
coordinate sheet to the sign of the actual word `ride m x h q` remains a
separate bridge theorem about permutation sign.
-/

namespace Coeff2

namespace Charlieplex

/-! ## The explicit source--sink dictionary

The cardinality `m * (m - 1)` is not merely a numerical coincidence.  In any
additive commutative group, choosing a source and a nonzero displacement is
equivalent to choosing an ordered pair of distinct endpoints.  The cyclic
group `ZMod m` is the suffix-phase model relevant to a ride.
-/

/-- A source together with a nonzero relative displacement. -/
abbrev DifferenceCoord (A : Type*) [Zero A] :=
  Σ source : A, {displacement : A // displacement ≠ 0}

/-- An ordered source--sink channel. -/
abbrev Channel (A : Type*) :=
  Σ source : A, {sink : A // sink ≠ source}

/-- The explicit Charlieplex dictionary `(source, d) ↦ (source, source + d)`. -/
def differenceEquivChannel (A : Type*) [AddCommGroup A] :
    DifferenceCoord A ≃ Channel A where
  toFun c := ⟨c.1, ⟨c.1 + c.2.1, by
    intro hsink
    apply c.2.2
    have h := congrArg (fun z => z - c.1) hsink
    simpa [add_comm] using h⟩⟩
  invFun c := ⟨c.1, ⟨c.2.1 - c.1, sub_ne_zero.mpr c.2.2⟩⟩
  left_inv c := by
    rcases c with ⟨source, displacement⟩
    simp [add_comm]
  right_inv c := by
    rcases c with ⟨source, sink⟩
    simp [add_comm]

/-- Translating a suffix phase leaves its relative displacement unchanged. -/
def shiftDifference {A : Type*} [AddCommGroup A] (a : A) (c : DifferenceCoord A) :
    DifferenceCoord A := ⟨c.1 + a, c.2⟩

/-- Translating a channel shifts source and sink together. -/
def shiftChannel {A : Type*} [AddCommGroup A] (a : A) (c : Channel A) : Channel A :=
  ⟨c.1 + a, ⟨c.2.1 + a, fun h => c.2.2 (add_right_cancel h)⟩⟩

/-- Rotation commutes with the source--sink dictionary. -/
theorem differenceEquivChannel_shift {A : Type*} [AddCommGroup A]
    (a : A) (c : DifferenceCoord A) :
    differenceEquivChannel A (shiftDifference a c) =
      shiftChannel a (differenceEquivChannel A c) := by
  rcases c with ⟨source, displacement⟩
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  apply Subtype.ext
  dsimp [differenceEquivChannel, shiftDifference, shiftChannel]
  ac_rfl

/-- Reversing an oriented difference makes the old sink the new source. -/
def reverseDifference {A : Type*} [AddCommGroup A] (c : DifferenceCoord A) :
    DifferenceCoord A :=
  ⟨c.1 + c.2.1, ⟨-c.2.1, neg_ne_zero.mpr c.2.2⟩⟩

/-- Reverse the orientation of a source--sink channel. -/
def reverseChannel {A : Type*} (c : Channel A) : Channel A :=
  ⟨c.2.1, ⟨c.1, Ne.symm c.2.2⟩⟩

/-- Channel reversal is exactly `(q,d) ↦ (q+d,-d)`. -/
theorem differenceEquivChannel_reverse {A : Type*} [AddCommGroup A]
    (c : DifferenceCoord A) :
    differenceEquivChannel A (reverseDifference c) =
      reverseChannel (differenceEquivChannel A c) := by
  rcases c with ⟨source, displacement⟩
  simp [differenceEquivChannel, reverseDifference, reverseChannel, add_comm]

abbrev CyclicDifferenceCoord (m : ℕ) := DifferenceCoord (ZMod m)

abbrev CyclicChannel (m : ℕ) := Channel (ZMod m)

/-- The explicit cyclic Charlieplex equivalence for `m` suffix phases. -/
def cyclicDifferenceEquivChannel (m : ℕ) :
    CyclicDifferenceCoord m ≃ CyclicChannel m :=
  differenceEquivChannel (ZMod m)

/-- The primitive `one level above/below` displacements.  These are two
special channels inside the full set of nonzero displacements. -/
def IsPrimitiveDifference {A : Type*} [AddCommGroup A] [One A]
    (c : DifferenceCoord A) : Prop :=
  c.2.1 = 1 ∨ c.2.1 = -1

/-- Endpoint form of primitive cyclic adjacency. -/
def IsPrimitiveChannel {A : Type*} [AddCommGroup A] [One A]
    (c : Channel A) : Prop :=
  c.2.1 = c.1 + 1 ∨ c.2.1 = c.1 - 1

/-- `d = ±1` means exactly that the sink is one cyclic suffix level above or
below the source. -/
theorem primitiveDifference_iff_primitiveChannel {A : Type*}
    [AddCommGroup A] [One A] (c : DifferenceCoord A) :
    IsPrimitiveDifference c ↔
      IsPrimitiveChannel (differenceEquivChannel A c) := by
  rcases c with ⟨source, displacement⟩
  simp [IsPrimitiveDifference, IsPrimitiveChannel, differenceEquivChannel,
    sub_eq_add_neg]

/-- A concrete witness that the full Charlieplex space contains accumulated
displacements beyond the primitive `±1` events. -/
def gapTwo : CyclicDifferenceCoord 5 := ⟨0, ⟨2, by decide⟩⟩

theorem gapTwo_is_not_primitive : ¬ IsPrimitiveDifference gapTwo := by
  change ¬ ((2 : ZMod 5) = 1 ∨ (2 : ZMod 5) = -1)
  decide

/-- Every cyclic displacement is obtained by iterating the primitive forward
step.  Thus the `m * (m - 1)` channel space is the closure of primitive suffix
adjacency, not a claim that every channel itself has displacement `±1`. -/
theorem cyclic_displacement_generated_by_step {m : ℕ} (hm : 2 ≤ m) (d : ZMod m) :
    ∃ k : Fin m, d = k.1 • (1 : ZMod m) := by
  letI : NeZero m := ⟨by omega⟩
  refine ⟨⟨d.val, d.val_lt⟩, ?_⟩
  simpa using (ZMod.natCast_zmod_val d).symm

/-- Coordinates of a canonical ride: an orbit number and a rotation phase. -/
abbrev RideCoord (m : ℕ) := Fin (m - 1) × Fin m

/-- The geometric ride coordinate `(h,q)` has source `q` and nonzero cyclic
displacement `h+1`. -/
def rideToCyclicDifference {m : ℕ} (hm : 2 ≤ m) (c : RideCoord m) :
    CyclicDifferenceCoord m :=
  ⟨(c.2.1 : ZMod m), ⟨(c.1.1 + 1 : ℕ), by
    intro hzero
    have hdiv : m ∣ c.1.1 + 1 :=
      (ZMod.natCast_eq_zero_iff (c.1.1 + 1) m).mp hzero
    have hle : m ≤ c.1.1 + 1 := Nat.le_of_dvd (by omega) hdiv
    omega⟩⟩

/-- The corresponding ordered source--sink channel. -/
def rideToCyclicChannel {m : ℕ} (hm : 2 ≤ m) (c : RideCoord m) :
    CyclicChannel m :=
  cyclicDifferenceEquivChannel m (rideToCyclicDifference hm c)

@[simp]
theorem rideToCyclicChannel_source {m : ℕ} (hm : 2 ≤ m) (c : RideCoord m) :
    (rideToCyclicChannel hm c).1 = (c.2.1 : ZMod m) := rfl

@[simp]
theorem rideToCyclicChannel_sink {m : ℕ} (hm : 2 ≤ m) (c : RideCoord m) :
    (rideToCyclicChannel hm c).2.1 =
      (c.2.1 : ZMod m) + (c.1.1 + 1 : ℕ) := rfl

/-- A directed channel is a source pin together with a distinct sink pin. -/
abbrev DirectedChannel (m : ℕ) := Σ source : Fin m, {sink : Fin m // sink ≠ source}

theorem card_rideCoord (m : ℕ) : Fintype.card (RideCoord m) = m * (m - 1) := by
  simp [RideCoord, Nat.mul_comm]

/-! ## Fragmentation depth as a mixed-radix stack -/

/-- At fragmentation depth `r`, the active Cayley graph has radix `N-r`. -/
def radixAt (N : ℕ) (r : Fin (N - 1)) : ℕ := N - r.1

theorem radixAt_ge_two (N : ℕ) (r : Fin (N - 1)) : 2 ≤ radixAt N r := by
  simp only [radixAt]
  omega

/-- A graph-level connection is initiated at one fragmentation depth and
carries a Charlieplex coordinate in that depth's radix. -/
structure FragmentLink (N : ℕ) where
  depth : Fin (N - 1)
  illumination : RideCoord (radixAt N depth)

/-- The recursive stack of Charlieplex coordinates at radices
`N, N-1, ..., 2`. -/
def CharlieStack : ℕ → Type
  | 0 => PUnit
  | 1 => PUnit
  | n + 2 => RideCoord (n + 2) × CharlieStack (n + 1)

noncomputable instance charlieStackFintype : ∀ N : ℕ, Fintype (CharlieStack N)
  | 0 => by
      change Fintype PUnit
      infer_instance
  | 1 => by
      change Fintype PUnit
      infer_instance
  | n + 2 => by
      change Fintype (RideCoord (n + 2) × CharlieStack (n + 1))
      letI : Fintype (CharlieStack (n + 1)) := charlieStackFintype (n + 1)
      infer_instance

/-- The stack consists of two interleaved factorial chains: a source digit
and a nonzero relative-sink digit at every radix. -/
theorem card_charlieStack (N : ℕ) :
    Fintype.card (CharlieStack N) = N.factorial * (N - 1).factorial := by
  induction N using Nat.twoStepInduction with
  | zero => simp [CharlieStack]
  | one => simp [CharlieStack]
  | more n _ ih =>
      change Fintype.card (RideCoord (n + 2) × CharlieStack (n + 1)) =
        (n + 2).factorial * (n + 2 - 1).factorial
      have hpred : n + 1 - 1 = n := by omega
      have htop : n + 2 - 1 = n + 1 := by omega
      rw [hpred] at ih
      rw [Fintype.card_prod, card_rideCoord, ih, htop]
      simp only [Nat.factorial_succ]
      ring

theorem card_sink_ne (m : ℕ) (source : Fin m) :
    Fintype.card {sink : Fin m // sink ≠ source} = m - 1 := by
  classical
  rw [Fintype.card_subtype_compl (fun sink : Fin m => sink = source)]
  simp

theorem card_directedChannel (m : ℕ) :
    Fintype.card (DirectedChannel m) = m * (m - 1) := by
  classical
  simp only [DirectedChannel, Fintype.card_sigma]
  simp [card_sink_ne]

/-- The finite-type form of the Charlieplex count.  This equivalence is chosen
noncomputably from the equality of cardinalities; a later geometric bridge can
replace it with the cyclic-difference coordinate map. -/
noncomputable def rideCoordEquivDirectedChannel (m : ℕ) :
    RideCoord m ≃ DirectedChannel m :=
  Fintype.equivOfCardEq ((card_rideCoord m).trans (card_directedChannel m).symm)

/-- Reverse the nonzero difference `h + 1`.  On the zero-based orbit index this
is the reflection `h ↦ m - 2 - h`. -/
def reverseOrbit {m : ℕ} (hm : 2 ≤ m) (h : Fin (m - 1)) : Fin (m - 1) :=
  ⟨m - 2 - h.1, by omega⟩

@[simp]
theorem reverseOrbit_val {m : ℕ} (hm : 2 ≤ m) (h : Fin (m - 1)) :
    (reverseOrbit hm h : ℕ) = m - 2 - h := rfl

@[simp]
theorem reverseOrbit_involutive {m : ℕ} (hm : 2 ≤ m) (h : Fin (m - 1)) :
    reverseOrbit hm (reverseOrbit hm h) = h := by
  apply Fin.ext
  simp [reverseOrbit]
  omega

/-- On cyclic differences, the reflected orbit index is exactly orientation
reversal: `m-1-(h+1) = -(h+1)` modulo `m`. -/
theorem reverseOrbit_displacement {m : ℕ} (hm : 2 ≤ m) (h : Fin (m - 1)) :
    (((reverseOrbit hm h).1 + 1 : ℕ) : ZMod m) =
      -(((h.1 + 1 : ℕ) : ZMod m)) := by
  rw [eq_neg_iff_add_eq_zero, ← Nat.cast_add]
  have hsum : (reverseOrbit hm h).1 + 1 + (h.1 + 1) = m := by
    simp only [reverseOrbit_val]
    omega
  rw [hsum, ZMod.natCast_self]

/-- The parity sheet supplied by the number of weight-2 doors already crossed. -/
def orbitSheet {m : ℕ} (h : Fin (m - 1)) : Fin 2 := ⟨h.1 % 2, Nat.mod_lt _ (by omega)⟩

/-- **Charlieplexed parity.**  For odd `m`, the two orientations of the same
channel pair lie on opposite orbit-parity sheets. -/
theorem reverseOrbit_flips_sheet {m : ℕ} (hm : 2 ≤ m) (hodd : Odd m)
    (h : Fin (m - 1)) : orbitSheet (reverseOrbit hm h) ≠ orbitSheet h := by
  rcases hodd with ⟨k, rfl⟩
  intro heq
  have hval := Fin.ext_iff.mp heq
  simp only [orbitSheet, reverseOrbit, Fin.val_mk] at hval
  omega

/-- The complementary law: even radices preserve the door-count sheet under
channel reversal.  Hence parity transport alternates with fragmentation depth. -/
theorem reverseOrbit_preserves_sheet {m : ℕ} (hm : 2 ≤ m) (heven : Even m)
    (h : Fin (m - 1)) : orbitSheet (reverseOrbit hm h) = orbitSheet h := by
  rcases heven with ⟨k, rfl⟩
  apply Fin.ext
  simp only [orbitSheet, reverseOrbit, Fin.val_mk]
  omega

/-- A parity assignment on ride coordinates is compatible when its only
dependence on the orbit coordinate is the door-count sheet. -/
def ParityCompatible {m : ℕ} (ε : RideCoord m → Fin 2) : Prop :=
  ∃ base : Fin m → Fin 2, ∀ c, ε c = base c.2 + orbitSheet c.1

/-- Any compatible realization inherits the Charlieplex reversal law.  Only
the orbit coordinate is reversed here; the geometric channel equivalence will
specify the corresponding new phase. -/
theorem compatible_reversal_flips {m : ℕ} (hm : 2 ≤ m) (hodd : Odd m)
    (ε : RideCoord m → Fin 2) (hε : ParityCompatible ε) (h : Fin (m - 1))
    (q q' : Fin m) : ε (reverseOrbit hm h, q') ≠ ε (h, q) ∨ q' ≠ q := by
  rcases hε with ⟨base, hbase⟩
  by_cases hqq : q' = q
  · subst q'
    left
    rw [hbase, hbase]
    intro heq
    have := add_left_cancel heq
    exact reverseOrbit_flips_sheet hm hodd h this
  · exact Or.inr hqq

/-! ## Sylvester rewriting and the lost sign -/

/-- One oriented generating relation of the Sylvester congruence,
`c a v b = a c v b` for `a ≤ b < c`, closed under word contexts. -/
inductive SylvesterStep : List ℕ → List ℕ → Prop
  | mk (left middle right : List ℕ) (a b c : ℕ) (hab : a ≤ b) (hbc : b < c) :
      SylvesterStep
        (left ++ c :: a :: middle ++ b :: right)
        (left ++ a :: c :: middle ++ b :: right)

/-- A small executable inversion count for event words. -/
def inversionCount : List ℕ → ℕ
  | [] => 0
  | x :: xs => (xs.filter (· < x)).length + inversionCount xs

/-- Swapping adjacent distinct letters changes the inversion count by exactly
one, even inside an arbitrary word context. -/
theorem inversionCount_swap_adjacent (left rest : List ℕ) {a c : ℕ} (hac : a < c) :
    inversionCount (left ++ c :: a :: rest) =
      inversionCount (left ++ a :: c :: rest) + 1 := by
  induction left with
  | nil =>
      simp [inversionCount, hac, Nat.not_lt.mpr hac.le]
      omega
  | cons x xs ih =>
      simp only [List.cons_append, inversionCount]
      have hp : List.Perm (xs ++ c :: a :: rest) (xs ++ a :: c :: rest) :=
        List.Perm.append_left xs (List.Perm.swap a c rest)
      have hf :
          ((xs ++ c :: a :: rest).filter (· < x)).length =
            ((xs ++ a :: c :: rest).filter (· < x)).length :=
        List.Perm.length_eq (List.Perm.filter (fun z => z < x) hp)
      rw [hf, ih]
      omega

def inversionSheet (w : List ℕ) : Fin 2 :=
  ⟨inversionCount w % 2, Nat.mod_lt _ (by omega)⟩

/-- Every generating Sylvester relation swaps adjacent `c > a`, so it toggles
inversion parity; this is not merely a feature of the small example below. -/
theorem SylvesterStep.inversionCount_eq {u v : List ℕ} (h : SylvesterStep u v) :
    inversionCount u = inversionCount v + 1 := by
  cases h with
  | mk left middle right a b c hab hbc =>
      simpa [List.append_assoc] using
        inversionCount_swap_adjacent left (middle ++ b :: right) (lt_of_le_of_lt hab hbc)

theorem SylvesterStep.flips_inversionSheet {u v : List ℕ} (h : SylvesterStep u v) :
    inversionSheet u = inversionSheet v + 1 := by
  apply Fin.ext
  change inversionCount u % 2 = (inversionCount v % 2 + 1) % 2
  rw [h.inversionCount_eq]
  omega

theorem sylvester_basic_example : SylvesterStep [3, 1, 2] [1, 3, 2] := by
  simpa using SylvesterStep.mk [] [] [] 1 2 3 (by omega) (by omega)

theorem sylvester_basic_example_opposite_sign :
    inversionSheet [3, 1, 2] ≠ inversionSheet [1, 3, 2] := by decide

/-- Ordinary Sylvester equivalence cannot preserve inversion parity. -/
theorem sylvester_does_not_preserve_inversion_sheet :
    ∃ u v, SylvesterStep u v ∧ inversionSheet u ≠ inversionSheet v :=
  ⟨[3, 1, 2], [1, 3, 2], sylvester_basic_example,
    sylvester_basic_example_opposite_sign⟩

/-- A word in the signed double cover of the Sylvester system. -/
structure SignedWord where
  word : List ℕ
  sheet : Fin 2
  deriving DecidableEq

/-- Lift every basic Sylvester move by toggling the additional sheet. -/
def SignedSylvesterStep (u v : SignedWord) : Prop :=
  SylvesterStep u.word v.word ∧ v.sheet = u.sheet + 1

/-- Total charge combines inversion parity with the added sheet. -/
def SignedWord.charge (u : SignedWord) : Fin 2 := inversionSheet u.word + u.sheet

/-- The signed lift repairs every generating relation, not only the displayed
counterexample. -/
theorem SignedSylvesterStep.conserves_charge {u v : SignedWord}
    (h : SignedSylvesterStep u v) : u.charge = v.charge := by
  rcases h with ⟨hword, hsheet⟩
  rw [SignedWord.charge, SignedWord.charge, hword.flips_inversionSheet, hsheet]
  ac_rfl

/-- The counterexample is repaired by the signed lift: the two representatives
have the same total charge. -/
theorem signed_basic_example_conserves_charge :
    let u : SignedWord := ⟨[3, 1, 2], 0⟩
    let v : SignedWord := ⟨[1, 3, 2], 1⟩
    SignedSylvesterStep u v ∧ u.charge = v.charge := by
  dsimp only
  have hstep : SignedSylvesterStep ⟨[3, 1, 2], 0⟩ ⟨[1, 3, 2], 1⟩ := by
    constructor
    · exact sylvester_basic_example
    · decide
  exact ⟨hstep, hstep.conserves_charge⟩

end Charlieplex

end Coeff2
