import Coeff2.CharlieSourceReversal
import SuperpermutationUpperBound.Transport.Ports

/-! Exact source-selection changes, without treating four-row packets as atomic.
Full-to-short keeps the literal head. Short-to-full is rephased TWO places
back, not the one-place reversal in CharlieSourceReversal; it keeps the tail.
Each change is a single signed boundary column. A closed circuit of those
columns preserves boundary balance and each ordinary cyclic base class.
Assigned visible permutations can change: full occupation still requires
Pantone's completion construction. No cheapness or better bound is asserted.
-/
namespace Coeff2.Charlieplex.BalancedSourceSelection
open SuperpermutationUpperBound
open Coeff2.Charlieplex.SourceReversal
open scoped BigOperators
variable {α : Type}

def boundary (φ : List α → Int) (r : Row α) : Int := φ r.head - φ r.tail

theorem full_to_short_head (x : List α) (s : α) :
    (shortRow x s).head = (fullRow x s).head := rfl

theorem short_to_rephased_full_tail (x : List α) (s : α) (hx : 3 ≤ x.length) :
    (fullRow (rot x (x.length-2)) s).tail = (shortRow x s).tail := by
  rw [full_tail, short_tail _ _ hx, rot_add]
  rw [show x.length-2+1=x.length-1 by omega]
  simp

theorem short_to_rephased_full_same_class (x : List α) (hx : 3 ≤ x.length) :
    CyclicEq x (rot x (x.length-2)) :=
  CyclicEq.of_rot (by intro he; simp [he] at hx) _

theorem full_to_short_boundary (x : List α) (s : α) (φ : List α → Int) :
    boundary φ (shortRow x s) - boundary φ (fullRow x s) =
      φ (fullRow x s).tail - φ (shortRow x s).tail := by
  unfold boundary
  rw [full_to_short_head]
  ring

theorem short_to_full_boundary (x : List α) (s : α) (hx : 3 ≤ x.length)
    (φ : List α → Int) :
    boundary φ (fullRow (rot x (x.length-2)) s) - boundary φ (shortRow x s) =
      φ (fullRow (rot x (x.length-2)) s).head - φ (shortRow x s).head := by
  unfold boundary
  rw [short_to_rephased_full_tail _ _ hx]
  ring

theorem full_to_short_charge (x : List α) (s : α) (hx : 3 ≤ x.length) :
    ((shortRow x s).charge : Int)-(fullRow x s).charge=2 := by
  rw [short_charge _ _ hx,full_charge]
  norm_num

theorem short_to_full_charge (x : List α) (s : α) (hx : 3 ≤ x.length) :
    ((fullRow (rot x (x.length-2)) s).charge : Int)-(shortRow x s).charge=-2 := by
  rw [full_charge,short_charge _ _ hx]
  norm_num

/-- A circuit of signed literal boundary columns telescopes exactly. Taking
`φ` to be the indicator of ANY ordered prefix gives its degree-balance law.
This does not require unique prefixes, a four-row packet, or a simple circuit.
-/
theorem circuit_boundary_conserved {E : Type} [Fintype E]
    (p : Equiv.Perm E) (port : E → List α) (old new : E → Row α)
    (φ : List α → Int)
    (h : ∀ e, boundary φ (new e)-boundary φ (old e)=φ (port (p e))-φ (port e)) :
    (∑ e, boundary φ (new e)) = ∑ e, boundary φ (old e) := by
  have hs := congrArg (fun f : E → Int => ∑ e, f e) (funext h)
  simp only [Finset.sum_sub_distrib] at hs
  rw [Equiv.sum_comp p (fun e => φ (port e))] at hs
  omega

/-- The cost is NOT inferred from balance: it is the signed number of changes.
This separate identity is needed before any savings claim can be made. -/
theorem circuit_charge_change {E : Type} [Fintype E]
    (old new : E → Row α) (sign : E → Int)
    (h : ∀ e, ((new e).charge : Int)-((old e).charge : Int)=2*sign e) :
    (∑ e, ((new e).charge : Int))-(∑ e, ((old e).charge : Int))=2*∑ e, sign e := by
  have hs := congrArg (fun f : E → Int => ∑ e, f e) (funext h)
  simpa only [Finset.sum_sub_distrib, Finset.mul_sum] using hs

/-- An exact potential can reject EVERY balanced subset of one fixed palette,
without enumerating its circuits. The potential inequalities must be checked
on the literal old/new rows; they are not an assumption about all selections.
-/
theorem balanced_palette_no_charge_reduction {E : Type} [Fintype E]
    (old new : E → Row α) (φ : List α → Int) (sign : E → Int)
    (hb : (∑ e, boundary φ (new e))=∑ e, boundary φ (old e))
    (hp : ∀ e, boundary φ (new e)-boundary φ (old e) ≤ sign e)
    (hc : ∀ e, ((new e).charge : Int)-((old e).charge : Int)=2*sign e) :
    (∑ e, ((old e).charge : Int)) ≤ ∑ e, ((new e).charge : Int) := by
  have hs := Finset.sum_le_sum (fun e (_ : e ∈ Finset.univ) => hp e)
  rw [Finset.sum_sub_distrib,hb,sub_self] at hs
  have hq := circuit_charge_change old new sign hc
  omega

#print axioms short_to_rephased_full_tail
#print axioms full_to_short_boundary
#print axioms short_to_full_boundary
#print axioms circuit_boundary_conserved
#print axioms circuit_charge_change
#print axioms balanced_palette_no_charge_reduction
end Coeff2.Charlieplex.BalancedSourceSelection
