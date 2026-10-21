/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Coeff2.CharlieGauge
import Mathlib.GroupTheory.FreeGroup.Basic

/-!
# Free loop words and the second Sylvester pair

This file records the algebra that follows if the two preferred admissible
parity traversals at radix `m` have lengths `2*m-2` and `2*m-1`.

It deliberately does not claim that these are the shortest admissible loops
in the superpermutation geometry.  The intended empirical claim is that the
5905 construction prefers them to deeper fragmentation; that ledger bridge
is separate.  Here we prove the consequences of the two lengths:

* reduced loop words form a free group (written additively in Lean);
* signed traversal weight is a homomorphism to the integers;
* the two weights are consecutive and generate all of `ℤ`;
* their positive sum is `4*m-3` and flips parity;
* their Frobenius expression is `4*m^2-10*m+5`.
-/

namespace Coeff2

namespace Charlieplex

/-- The two proposed preferred parity-traversal loop types. -/
inductive ParityTraversalLoop
  | evenLoop
  | oddLoop
  deriving DecidableEq, Fintype

/-- The preferred even traversal length. -/
def evenTraversalLength (m : ℕ) : ℕ := 2 * m - 2

/-- The consecutive, odd traversal length. -/
def oddTraversalLength (m : ℕ) : ℕ := 2 * m - 1

theorem traversalLengths_consecutive {m : ℕ} (hm : 1 ≤ m) :
    oddTraversalLength m = evenTraversalLength m + 1 := by
  simp only [oddTraversalLength, evenTraversalLength]
  omega

/-- Consecutive traversal lengths are coprime, so their signed subgroup is
all of the integer traversal group. -/
theorem traversalLengths_coprime {m : ℕ} (hm : 1 ≤ m) :
    Nat.Coprime (evenTraversalLength m) (oddTraversalLength m) := by
  rw [traversalLengths_consecutive hm]
  simp

/-- Integer weights are used on free-group words, because inverse loops carry
negative traversal weight. -/
def traversalGeneratorWeight (m : ℕ) : ParityTraversalLoop → ℤ
  | .evenLoop => 2 * (m : ℤ) - 2
  | .oddLoop => 2 * (m : ℤ) - 1

/-- Reduced loop words.  `FreeAddGroup` is the additive-notation version of a
noncommutative free group, not a free abelian group. -/
abbrev TraversalWord := FreeAddGroup ParityTraversalLoop

/-- Signed traversal weight extends uniquely from the two loop generators to
every reduced free-group word. -/
def traversalWeight (m : ℕ) : TraversalWord →+ ℤ :=
  FreeAddGroup.lift (traversalGeneratorWeight m)

@[simp]
theorem traversalWeight_generator (m : ℕ) (loop : ParityTraversalLoop) :
    traversalWeight m (FreeAddGroup.of loop) = traversalGeneratorWeight m loop := by
  simp [traversalWeight]

/-- The positive word using one loop of each type. -/
def pairedTraversal : TraversalWord :=
  FreeAddGroup.of .evenLoop + FreeAddGroup.of .oddLoop

/-- The paired positive traversal has length `4*m-3`. -/
theorem pairedTraversal_weight (m : ℕ) :
    traversalWeight m pairedTraversal = 4 * (m : ℤ) - 3 := by
  simp [pairedTraversal, traversalGeneratorWeight]
  ring

/-- In the free group, subtraction of the consecutive generators—not their
positive sum—is a unit traversal of signed weight one. -/
def unitTraversal : TraversalWord :=
  FreeAddGroup.of .oddLoop - FreeAddGroup.of .evenLoop

theorem unitTraversal_weight (m : ℕ) :
    traversalWeight m unitTraversal = 1 := by
  simp [unitTraversal, traversalGeneratorWeight]

/-- The two consecutive loop weights generate the entire signed traversal
group `ℤ`. -/
theorem traversalWeight_surjective (m : ℕ) :
    Function.Surjective (traversalWeight m) := by
  intro weight
  refine ⟨weight • unitTraversal, ?_⟩
  rw [map_zsmul, unitTraversal_weight]
  simp

/-- Parity is signed traversal weight reduced modulo two. -/
def traversalParity (m : ℕ) : TraversalWord →+ ZMod 2 :=
  (Int.castAddHom (ZMod 2)).comp (traversalWeight m)

@[simp]
theorem evenLoop_parity (m : ℕ) :
    traversalParity m (FreeAddGroup.of .evenLoop) = 0 := by
  simp [traversalParity, traversalGeneratorWeight,
    show (2 : ZMod 2) = 0 by decide]

@[simp]
theorem oddLoop_parity (m : ℕ) :
    traversalParity m (FreeAddGroup.of .oddLoop) = 1 := by
  simp [traversalParity, traversalGeneratorWeight,
    show (2 : ZMod 2) = 0 by decide, ZMod.neg_eq_self_mod_two]

/-- One positive loop of each kind has odd total traversal parity. -/
theorem pairedTraversal_flips_parity (m : ℕ) :
    traversalParity m pairedTraversal = 1 := by
  simp [pairedTraversal]

/-- The integer Frobenius expression for the consecutive pair
`2*m-2, 2*m-1`. -/
def traversalFrobenius (m : ℕ) : ℤ :=
  (2 * (m : ℤ) - 2) * (2 * (m : ℤ) - 1) -
    (2 * (m : ℤ) - 2) - (2 * (m : ℤ) - 1)

theorem traversalFrobenius_formula (m : ℕ) :
    traversalFrobenius m = 4 * (m : ℤ) ^ 2 - 10 * (m : ℤ) + 5 := by
  simp only [traversalFrobenius]
  ring

/-- At radix eight the proposed primitive lengths are 14 and 15, their
paired positive traversal is 29, and their Frobenius number is 181. -/
theorem traversal_eight_arithmetic :
    evenTraversalLength 8 = 14 ∧
    oddTraversalLength 8 = 15 ∧
    traversalWeight 8 pairedTraversal = 29 ∧
    traversalFrobenius 8 = 181 := by
  norm_num [evenTraversalLength, oddTraversalLength, pairedTraversal_weight,
    traversalFrobenius_formula]

end Charlieplex

end Coeff2
