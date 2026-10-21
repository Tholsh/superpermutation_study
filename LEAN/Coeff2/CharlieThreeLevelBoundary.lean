import Coeff2.CharlieLiteralReservoir

/-!
Three-symbol boundary forgetting, with exact literal occupation retained.
This does NOT assert a cheap n -> n+3 construction exists. `tower_valid`
and `tower_bound` explicitly require its as-yet-unconstructed literal lift.
No repeat restriction, matrix footprint, or corpus-specific premise is used.
-/
namespace Coeff2.Charlieplex.ThreeLevelBoundary
open LiteralReservoir

/-- The full (N-1)-symbol suffix has three omitted symbols and a core f;
N = |f|+4. After three writes it forgets those omitted symbols exactly. -/
theorem three_writes_forget (f : List ℕ) (a b c x y z : ℕ) :
    endBoundary (f.length+4) (a :: b :: c :: f) [x,y,z] = f ++ [x,y,z] := by
  simp [endBoundary, lastSymbols, List.length_append, List.append_assoc]

theorem outgoing_forgets (f rest : List ℕ) (a b c x y z : ℕ) :
    endBoundary (f.length+4) (a :: b :: c :: f) ([x,y,z] ++ rest) =
      endBoundary (f.length+4) (f ++ [x,y,z]) rest := by
  rw [endBoundary_append, three_writes_forget]

theorem occupation_split (f rest : List ℕ) (a b c x y z : ℕ) :
    emitted (f.length+4) (a :: b :: c :: f) ([x,y,z] ++ rest) =
      emitted (f.length+4) (a :: b :: c :: f) [x,y,z] ++
      emitted (f.length+4) (f ++ [x,y,z]) rest := by
  rw [emitted_append, three_writes_forget]

theorem emitted_length_le (n : ℕ) (boundary word : List ℕ) :
    (emitted n boundary word).length ≤ word.length := by
  induction word generalizing boundary with
  | nil => simp [emitted]
  | cons symbol rest ih =>
    have h := ih (lastSymbols (n-1) (boundary ++ [symbol]))
    simp only [emitted, List.length_append, List.length_cons]
    split <;> simp only [List.length_singleton, List.length_nil] <;> omega

/-- Only three occurrence windows can retain the omitted context.
Their actual identities must still be stored; a cardinality bound is not
permission to drop them from occupation. -/
theorem context_occurrences_le_three (f : List ℕ) (a b c x y z : ℕ) :
    (emitted (f.length+4) (a :: b :: c :: f) [x,y,z]).length ≤ 3 := by
  exact emitted_length_le _ _ _

/-- The reduced frame is sufficient once the seam writes have been absorbed
into the actual occupation set. This is the precise residual obligation. -/
theorem reduced_occupation (f rest : List ℕ) (a b c d e g x y z : ℕ)
    (U V : Finset (List ℕ))
    (h : U ∪ (emitted (f.length+4) (a :: b :: c :: f) [x,y,z]).toFinset =
         V ∪ (emitted (f.length+4) (d :: e :: g :: f) [x,y,z]).toFinset) :
    U ∪ (emitted (f.length+4) (a :: b :: c :: f) ([x,y,z] ++ rest)).toFinset =
    V ∪ (emitted (f.length+4) (d :: e :: g :: f) ([x,y,z] ++ rest)).toFinset := by
  rw [occupation_split, occupation_split, List.toFinset_append,
    List.toFinset_append, ← Finset.union_assoc, ← Finset.union_assoc, h]

/-- Equal outgoing suffix and equal accumulated literal occupation suffice
for equal occupation under EVERY common continuation. Repeats are allowed. -/
theorem continuation_occupation (n : ℕ) (left right : LiteralSearchState)
    (hb : left.boundary = right.boundary) (ho : left.occupied = right.occupied)
    (rest : List ℕ) :
    (literalStateRun n left rest).occupied =
      (literalStateRun n right rest).occupied := by
  rw [run_occupation, run_occupation, hb, ho]

/-- A literal replacement can differ in length and repeat history. Boundary
and occupied-rank equality alone preserve superpermutation coverage of all
future words. Alphabet legality and length must be checked separately. -/
theorem literal_replacement (n : ℕ) (hn : 1 ≤ n) (left right rest : List ℕ)
    (hb : (literalStateOf n left).boundary = (literalStateOf n right).boundary)
    (ho : (literalStateOf n left).occupied = (literalStateOf n right).occupied) :
    IsSuperperm n (left ++ rest) ↔ IsSuperperm n (right ++ rest) := by
  have h := continuation_occupation n (literalStateOf n left)
    (literalStateOf n right) hb ho rest
  rw [literalStateRun_correct n hn, literalStateRun_correct n hn] at h
  rw [← literalOccupation_covers_iff n (left ++ rest),
    ← literalOccupation_covers_iff n (right ++ rest)]
  change (∀ p, IsPermWord n p → p ∈ (literalStateOf n (left ++ rest)).occupied) ↔
    (∀ p, IsPermWord n p → p ∈ (literalStateOf n (right ++ rest)).occupied)
  rw [h]

/-- This is a literal superpermutation, not a supplied graph realization. -/
def Valid (n : ℕ) (word : List ℕ) : Prop :=
  literalAlphabetTest n word = true ∧ IsSuperperm n word

def tower (base : ℕ) (seed : List ℕ) (lift : ℕ → List ℕ → List ℕ) : ℕ → List ℕ
  | 0 => seed
  | k+1 => lift (base+3*k) (tower base seed lift k)

def allowance (base initial : ℕ) (cost : ℕ → ℕ) : ℕ → ℕ
  | 0 => initial
  | k+1 => allowance base initial cost k + cost (base+3*k)

/-- Induction closes the proposed residue-three family ONLY once a literal
occupation-preserving lift has actually been supplied and proved. -/
theorem tower_valid (base : ℕ) (seed : List ℕ) (lift : ℕ → List ℕ → List ℕ)
    (hs : Valid base seed)
    (hl : ∀ n word, Valid n word → Valid (n+3) (lift n word)) (k : ℕ) :
    Valid (base+3*k) (tower base seed lift k) := by
  induction k with
  | zero => simpa [tower] using hs
  | succ k ih =>
    have h := hl (base+3*k) _ ih
    simpa only [tower, Nat.mul_succ, Nat.add_assoc] using h

theorem tower_bound (base : ℕ) (seed : List ℕ) (lift : ℕ → List ℕ → List ℕ)
    (cost : ℕ → ℕ) (hs : Valid base seed)
    (hv : ∀ n word, Valid n word → Valid (n+3) (lift n word))
    (hc : ∀ n word, Valid n word → (lift n word).length ≤ word.length + cost n)
    (k : ℕ) :
    (tower base seed lift k).length ≤ allowance base seed.length cost k := by
  induction k with
  | zero => simp [tower, allowance]
  | succ k ih =>
    have h := hc (base+3*k) _ (tower_valid base seed lift hs hv k)
    simp only [tower, allowance]
    omega

/- Kernel-evaluated literal smoke controls, above n=7. These are boundary
tests, not full superpermutation constructions. -/
example : emitted 8 [1,2,3,4,5,6,7] [8,1,2] =
    [[1,2,3,4,5,6,7,8], [2,3,4,5,6,7,8,1], [3,4,5,6,7,8,1,2]] := by decide

example : endBoundary 9 [1,2,3,4,5,6,7,8] [9,1,2] =
    [4,5,6,7,8,9,1,2] := by decide

example : endBoundary 11 [1,2,3,4,5,6,7,8,9,10] [11,1,2] =
    [4,5,6,7,8,9,10,11,1,2] := by decide

/-- Equal reduced frames do not imply equal seam occupation. This does not
refute a period-three layer; it prevents an unsound deletion of its residual. -/
example : endBoundary 8 [1,2,3,4,5,6,7] [8,1,2] =
    endBoundary 8 [2,1,3,4,5,6,7] [8,1,2] := by decide

example : (emitted 8 [1,2,3,4,5,6,7] [8,1,2]).toFinset ≠
    (emitted 8 [2,1,3,4,5,6,7] [8,1,2]).toFinset := by decide

#print axioms three_writes_forget
#print axioms occupation_split
#print axioms context_occurrences_le_three
#print axioms reduced_occupation
#print axioms continuation_occupation
#print axioms literal_replacement
#print axioms tower_valid
#print axioms tower_bound
end Coeff2.Charlieplex.ThreeLevelBoundary
