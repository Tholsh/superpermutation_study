import SuperpermutationUpperBound.Transport.Blocks
import Mathlib.Tactic

/-! An exact exchange on literal source rows, for every base length >= 3.
Rephase a full row forward one position and make it short: its boundary
edge is reversed. The inverse exchange rephases a short row backward.
The cyclic base class is unchanged, but the assigned visible permutations
are NOT unchanged; their completed repair inventory must be handled by the
separate completion theorem. This is not a new upper-bound certificate.

The final potential lemma rules out a saving only when reversing a closed
subset of a fixed edge inventory. It is not a superpermutation lower bound.
Upstream Row and rotation definitions are Pantone's, Apache-2.0. -/
namespace Coeff2.Charlieplex.SourceReversal
open SuperpermutationUpperBound
open scoped BigOperators
variable {α : Type}

def fullRow (x : List α) (s : α) : Row α := ⟨x,s,x.length⟩
def shortRow (x : List α) (s : α) : Row α := ⟨x,s,x.length-2⟩

theorem full_tail (x : List α) (s : α) :
    (fullRow x s).tail = (rot x 1).take (x.length-2) := by
  change (rot x (x.length+1)).take (x.length-2) = _
  rw [show x.length+1=1+x.length by omega,rot_add_length]

theorem short_tail (x : List α) (s : α) (hx : 3 ≤ x.length) :
    (shortRow x s).tail = (rot x (x.length-1)).take (x.length-2) := by
  change (rot x (x.length-2+1)).take (x.length-2) = _
  rw [show x.length-2+1=x.length-1 by omega]

theorem full_to_short_reverses (x : List α) (s : α) (hx : 3 ≤ x.length) :
    (shortRow (rot x 1) s).head=(fullRow x s).tail ∧
    (shortRow (rot x 1) s).tail=(fullRow x s).head := by
  constructor
  · rw [full_tail]
    simp [shortRow,Row.head]
  · rw [short_tail _ _ (by simpa using hx)]
    simp only [rot_length]
    have hi := rot_inverse x 1
    rw [Nat.mod_eq_of_lt (by omega : 1 < x.length)] at hi
    rw [hi]
    rfl

theorem short_to_full_reverses (x : List α) (s : α) (hx : 3 ≤ x.length) :
    (fullRow (rot x (x.length-1)) s).head=(shortRow x s).tail ∧
    (fullRow (rot x (x.length-1)) s).tail=(shortRow x s).head := by
  constructor
  · rw [short_tail _ _ hx]
    simp [fullRow,Row.head]
  · rw [full_tail,rot_add,show x.length-1+1=x.length by omega,rot_length_self]
    simp [shortRow,Row.head]

theorem full_to_short_same_base_class (x : List α) (hx : 3 ≤ x.length) :
    CyclicEq x (rot x 1) := CyclicEq.of_rot (by intro he; simp [he] at hx) 1

theorem short_to_full_same_base_class (x : List α) (hx : 3 ≤ x.length) :
    CyclicEq x (rot x (x.length-1)) :=
  CyclicEq.of_rot (by intro he; simp [he] at hx) (x.length-1)

theorem full_charge (x : List α) (s : α) : (fullRow x s).charge=0 := by
  simp [fullRow,Row.charge]

theorem short_charge (x : List α) (s : α) (hx : 3 ≤ x.length) :
    (shortRow x s).charge=2 := by
  simp only [shortRow,Row.charge]
  omega

theorem full_to_short_charge (x : List α) (s : α) (hx : 3 ≤ x.length) :
    ((shortRow (rot x 1) s).charge : Int)-(fullRow x s).charge=2 := by
  rw [short_charge _ _ (by simpa using hx),full_charge]
  norm_num

theorem short_to_full_charge (x : List α) (s : α) (hx : 3 ≤ x.length) :
    ((fullRow (rot x (x.length-1)) s).charge : Int)-(shortRow x s).charge=-2 := by
  rw [full_charge,short_charge _ _ hx]
  norm_num

/-- An exact integer potential is a certificate against every cycle reversal
within this fixed inventory, irrespective of its size or branching. -/
theorem fixed_cycle_weight_nonnegative {E V : Type} [Fintype E]
    (p : Equiv.Perm E) (u : E → V) (weight : E → Int) (potential : V → Int)
    (hp : ∀ e, potential (u (p e)) ≤ potential (u e)+weight e) :
    0 ≤ ∑ e, weight e := by
  have hs := Finset.sum_le_sum (fun e (_ : e ∈ Finset.univ) => hp e)
  rw [Finset.sum_add_distrib,Equiv.sum_comp p (fun e => potential (u e))] at hs
  omega

theorem fixed_inventory_no_charge_reduction {E V : Type} [Fintype E]
    (p : Equiv.Perm E) (u : E → V) (weight oldCharge newCharge : E → Int)
    (potential : V → Int)
    (hp : ∀ e, potential (u (p e)) ≤ potential (u e)+weight e)
    (hc : ∀ e, newCharge e=oldCharge e+2*weight e) :
    (∑ e, oldCharge e) ≤ ∑ e, newCharge e := by
  have hw := fixed_cycle_weight_nonnegative p u weight potential hp
  simp_rw [hc]
  rw [Finset.sum_add_distrib,← Finset.mul_sum]
  omega

#print axioms full_to_short_reverses
#print axioms short_to_full_reverses
#print axioms full_to_short_charge
#print axioms short_to_full_charge
#print axioms fixed_inventory_no_charge_reduction
end Coeff2.Charlieplex.SourceReversal
