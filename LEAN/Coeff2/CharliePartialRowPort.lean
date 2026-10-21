import Coeff2.CharlieClockRefraction
import Coeff2.CharlieExactSymbolTransformer
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Data.List.Rotate

/-! General-deficit row ports extend the existing ClockRefraction formula.
The local map is an actual permutation, not a free phase bit. This proves
its algebra at every radix and the ordered matrix/superoperator transport.
Literal completion-to-port correspondence is a separate premise, audited by
partial_row_port_audit.cpp; neither occupation nor cheapness follows merely
from equality of the port permutations. -/
namespace Coeff2.Charlieplex.PartialRowPort
open ClockRefraction ExactSymbolTransformer

theorem prefixTurn_lt (h k j : ℕ) (hk : 0 < k) (kh : k < h) (jh : j < h) :
    prefixTurn k j < h := by
  simp only [prefixTurn]
  split_ifs <;> omega

/-- The exceptional port turn is the inverse of the initial k-cycle. -/
theorem prefixTurn_inverse {h : ℕ} [NeZero h] (k j : Fin h) (hk : 0 < k.val) :
    ((Fin.cycleRange ⟨k.val-1, by omega⟩)⁻¹ j).val = prefixTurn k.val j.val := by
  let i : Fin h := ⟨k.val-1, by omega⟩
  let z : Fin h := ⟨prefixTurn k.val j.val,
    prefixTurn_lt h k.val j.val hk k.isLt j.isLt⟩
  have hz : Fin.cycleRange i z = j := by
    apply Fin.ext
    by_cases hj0 : j.val = 0
    · have zi : z = i := by
        apply Fin.ext
        simp [z, i, prefixTurn, hj0]
      rw [zi, Fin.cycleRange_self]
      exact hj0.symm
    · by_cases hjk : j.val < k.val
      · have zlt : z < i := by
          change prefixTurn k.val j.val < k.val-1
          simp [prefixTurn, hj0, hjk]
          omega
        rw [Fin.coe_cycleRange_of_lt zlt]
        change prefixTurn k.val j.val + 1 = j.val
        simp [prefixTurn, hj0, hjk]
        omega
      · have iz : i < z := by
          change k.val-1 < prefixTurn k.val j.val
          simp [prefixTurn, hj0, hjk]
          omega
        rw [Fin.cycleRange_of_gt iz]
        simp [z, prefixTurn, hj0, hjk]
  have hi : (Fin.cycleRange i)⁻¹ j = z := by
    apply (Fin.cycleRange i).injective
    simpa using hz.symm
  exact congrArg Fin.val hi

/-- k = K-v-1 is the clock displacement of a partial row. The order matters:
first the clock shift, then the inverse cycle on ports 0..k-1. -/
def transport {h : ℕ} [NeZero h] (k : Fin h) (hk : 0 < k.val) :
    Equiv.Perm (Fin h) :=
  (Fin.cycleRange ⟨k.val-1, by omega⟩)⁻¹ * Equiv.addRight k

theorem transport_formula {h : ℕ} [NeZero h]
    (k j : Fin h) (hk : 0 < k.val) :
    (transport k hk j).val = deeperPort h k.val j.val := by
  rw [port_factorization h k.val j.val hk k.isLt j.isLt]
  change ((Fin.cycleRange ⟨k.val-1, by omega⟩)⁻¹ (j+k)).val = _
  rw [prefixTurn_inverse k (j+k) hk]
  rfl

theorem transport_injective {h : ℕ} [NeZero h]
    (k : Fin h) (hk : 0 < k.val) : Function.Injective (transport k hk) :=
  (transport k hk).injective

theorem transport_surjective {h : ℕ} [NeZero h]
    (k : Fin h) (hk : 0 < k.val) : Function.Surjective (transport k hk) :=
  (transport k hk).surjective

theorem prefixTurn_one (j : ℕ) : prefixTurn 1 j = j := by
  simp only [prefixTurn]
  split_ifs <;> omega

/-- Short rows have no exceptional turn: they are the positive clock. Full
rows use the negative clock predecessor from ClockRefraction. -/
theorem short_row_clock (h j : ℕ) (hh : 1 < h) (hj : j < h) :
    deeperPort h 1 j = clock h 1 j := by
  rw [port_factorization h 1 j (by omega) hh hj, prefixTurn_one]

/-- Number of cyclic-class visits in the inserted slices of a row. A gap
before one of the v visible old positions contributes one extra class. -/
def insertedVisits (K v : ℕ) : ℕ :=
  ∑ j ∈ Finset.range K, (v + if j < v then 1 else 0)

theorem inserted_visits (K v : ℕ) (hv : v ≤ K) :
    insertedVisits K v = (K+1)*v := by
  have hf : (Finset.range K).filter (fun j => j < v) = Finset.range v := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  have hs : (∑ j ∈ Finset.range K, if j < v then 1 else 0) = v := by
    rw [← Finset.sum_filter, hf]
    simp
  simp only [insertedVisits, Finset.sum_add_distrib, hs]
  simp
  ring

/-- The visits lost from the inserted slices reappear in the repairs. This
counts named cyclic classes, not fresh Bellman emissions or full-word length.
The separate literal occupation audit checks their identities, not only count. -/
theorem row_visit_conservation (K v : ℕ) (hv : v ≤ K) :
    insertedVisits K v + (K-v)*(K+1) = K*(K+1) := by
  rw [inserted_visits K v hv]
  have he : K-v+v=K := Nat.sub_add_cancel hv
  nlinarith

/-- At n=m+3, one complete old loop has K(K+1) cyclic classes and the old
loop count is (K-1)!, K=m+1. All literal rotation phases are still required. -/
theorem fiber_visits_total (m : ℕ) :
    ((m+1)*(m+2))*m.factorial = (m+2).factorial := by
  simp only [Nat.factorial_succ]
  ring

/-- Spell every completed slice as a cyclic chunk: (n+1)*c+1 letters for
c class visits. Baseline slices per old loop are K; missing classes add Q
repair slices. This is the exact F3+Q ledger, uniform in n. It does not
include the cost of opening and joining the resulting closed trails. -/
theorem cyclic_ledger (m Q : ℕ) :
    ((m+4)*((m+1)*(m+2))+(m+1))*m.factorial + Q =
      (m+3).factorial + (m+2).factorial + (m+1).factorial + Q := by
  simp only [Nat.factorial_succ]
  ring

/-- The formerly excluded near-full case has identity transport at all
visible ports. This does NOT say its completed graph has no internal cycle. -/
theorem zero_displacement (h j : ℕ) (hj : j < h) : deeperPort h 0 j = j := by
  simp [deeperPort, hj]

section LiteralNearFull
variable {α : Type*}

/-- Two distinct old rows ending a,b and b,a have the same inserted port
header. Thus the unique-head graph used for ordinary rows cannot simply be
extended to near-full rows without keeping multiple slice occurrences. -/
theorem near_full_shared_header (p : List α) (a b z : α) (j : ℕ) :
    ((p.take j ++ [z] ++ p.drop j) ++ [a,b]).take (p.length+1) =
      ((p.take j ++ [z] ++ p.drop j) ++ [b,a]).take (p.length+1) := by
  have hl : (p.take j ++ [z] ++ p.drop j).length = p.length+1 := by simp; omega
  have ht (tail : List α) :
      ((p.take j ++ [z] ++ p.drop j) ++ tail).take (p.length+1) =
        p.take j ++ [z] ++ p.drop j := by
    rw [← hl, List.take_append_of_le_length le_rfl, List.take_length]
  rw [ht [a,b], ht [b,a]]

/-- Literal heads/tails of the two slices omitted by the identity port
map. A=p,a,z,b; B=b,p,a,s. Their terminal cyclic headers match in both
directions, at width |p|+1. No parity or spectrum assumption is used. -/
theorem near_full_hidden_two_cycle (p : List α) (a b s z : α) :
    ((p ++ [a,z,b]).rotate (p.length+2)).take (p.length+1) =
      (b :: (p ++ [a,s])).take (p.length+1) ∧
    ((b :: (p ++ [a,s])).rotate (p.length+4)).take (p.length+1) =
      (p ++ [a,z,b]).take (p.length+1) := by
  have ha : (p ++ [a,z,b]).rotate (p.length+2) = b :: (p ++ [a,z]) := by
    have he := List.rotate_append_length_eq (p ++ [a,z]) [b]
    simpa [List.append_assoc] using he
  have hb : (b :: (p ++ [a,s])).rotate (p.length+4) = p ++ [a,s,b] := by
    rw [List.rotate_eq_drop_append_take_mod]
    have hm : (p.length+4) % (p.length+3) = 1 := by
      have he : p.length+4 = 1+(p.length+3) := by omega
      rw [he, Nat.add_mod]
      simp [Nat.mod_eq_of_lt (show 1 < p.length+3 by omega)]
    simp [hm, List.append_assoc]
  constructor
  · rw [ha]
    simp
  · rw [hb]
    simp [List.take_append]

end LiteralNearFull

section Ordered
variable {P : Type*}

def ordered : List (Equiv.Perm P) → Equiv.Perm P
  | [] => 1
  | t :: rest => ordered rest * t

theorem ordered_append (left right : List (Equiv.Perm P)) :
    ordered (left ++ right) = ordered right * ordered left := by
  induction left with
  | nil => simp [ordered]
  | cons t rest ih => simp only [List.cons_append, ordered, ih, mul_assoc]

/-- Equal ordered operators can be replaced inside an arbitrary surrounding
port schedule. Equal cycle counts alone are deliberately insufficient. -/
theorem ordered_exchange (before after left right : List (Equiv.Perm P))
    (same : ordered left = ordered right) :
    ordered (before ++ left ++ after) = ordered (before ++ right ++ after) := by
  simp only [ordered_append, same]

theorem ordered_relabel {Q : Type*} (e : P ≃ Q) (ts : List (Equiv.Perm P)) :
    ordered (ts.map (Equiv.permCongr e)) = Equiv.permCongr e (ordered ts) := by
  induction ts with
  | nil => ext q; simp [ordered]
  | cons t rest ih =>
      simp only [List.map_cons, ordered, ih]
      ext q
      simp [Equiv.permCongr, Equiv.Perm.mul_apply]

end Ordered

section Matrix
variable {P R : Type*} [Fintype P] [DecidableEq P] [CommSemiring R]

theorem symbolMatrix_comp (f g : P → P) :
    symbolMatrix (R := R) (g ∘ f) = symbolMatrix g * symbolMatrix f := by
  ext i j
  simp [symbolMatrix, Matrix.mul_apply]

/-- Ordered port transport is the deterministic classical sector of our
existing superoperator. No simultaneous diagonalization is hypothesized. -/
theorem ordered_superoperator (ts : List (Equiv.Perm P)) (x : P → R) :
    OccupationSuperoperator.act (symbolMatrix (ordered ts)) (Matrix.diagonal x) =
      Matrix.diagonal ((symbolMatrix (ordered ts)).mulVec x) :=
  symbol_diagonal (ordered ts) x

end Matrix

/-- Already at radix seven, partial and full rows do not commute. -/
theorem noncommuting_radix7 :
    deeperPort 7 2 (predecessor 7 0) ≠ predecessor 7 (deeperPort 7 2 0) := by decide

#print axioms transport_formula
#print axioms transport_injective
#print axioms row_visit_conservation
#print axioms cyclic_ledger
#print axioms ordered_exchange
#print axioms ordered_relabel
#print axioms symbolMatrix_comp
#print axioms ordered_superoperator
#print axioms near_full_shared_header
#print axioms near_full_hidden_two_cycle
end Coeff2.Charlieplex.PartialRowPort
