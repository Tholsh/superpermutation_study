import Coeff2.CharlieCycleCompression
import Coeff2.CharlieJayCompletionParity
import Coeff2.CharlieDigitClock

/-!
# Reduced-alphabet accounting over literal words

The logical clean/dirty trace is computed from the existing literal Bellman
state. It is not a supplied occupation certificate or a byte-format model.
Clean symbols remain uniquely determined by the boundary; clean runs can be
suppressed by a codec, but clean REPEATS are still charged separately.

The run ledger below retains all dirty depths, repeated permutations, and
partial visits to rotation orbits. Dirty continuation is NOT synonymous with
a forced bend. The ordinary four-port completion obstruction is reused from
CharlieJayCompletionParity, not promoted to a theorem about every word.
-/
namespace Coeff2.Charlieplex.ReducedAlphabetLedger

/-- Reuse the established literal codec theorem: suppressing a clean symbol
does not suppress a choice, because there is at most one such symbol. -/
theorem clean_choice_unique {n : Nat} {boundary : List Nat} {a b : Nat}
    (ha : IsPermWord n (boundary ++ [a])) (hb : IsPermWord n (boundary ++ [b])) :
    a = b := clean_append_unique ha hb

/-- Copying the oldest symbol of the current (n-1)-context is the logical
offset +1 dirty instruction, when the current n-window is a permutation. -/
theorem oldest_copy_dirty {n first oldest : Nat} {tail : List Nat}
    (hp : IsPermWord n (first :: oldest :: tail)) :
    literalPermTest n ((oldest :: tail) ++ [oldest]) = false := by
  apply Bool.eq_false_iff.mpr
  intro clean
  have same := (clean_append_is_rotation hp).mp clean
  have distinct : first ≠ oldest := by
    intro equal
    exact (List.nodup_cons.mp hp.nodup).1 (by simp [equal])
  exact distinct same.symm

/-- The following recovery really is clean: it exchanges the two displaced
letters, rather than losing an intervening required permutation silently.
Freshness still depends on the literal cache and is deliberately not asserted. -/
theorem oldest_copy_clean_recovery {n first oldest : Nat} {tail : List Nat}
    (hp : IsPermWord n (first :: oldest :: tail)) :
    IsPermWord n (tail ++ [oldest, first]) := by
  have rearrange : (tail ++ [oldest, first]).Perm (first :: oldest :: tail) := by
    exact List.perm_append_comm.trans (List.Perm.swap _ _ _)
  exact isPermWord_iff_perm_refList.mpr
    (rearrange.trans (isPermWord_iff_perm_refList.mp hp))

def flagsFrom (n : Nat) : LiteralSearchState → List Nat → List Bool
  | _, [] => []
  | s, a :: rest => literalPermTest n (s.boundary ++ [a]) ::
      flagsFrom n (literalStateStep n s a) rest

def flags (n : Nat) (word : List Nat) : List Bool :=
  flagsFrom n (literalStateOf n (word.take (n-1))) (word.drop (n-1))

theorem flagsFrom_length (n : Nat) (s : LiteralSearchState) (tail : List Nat) :
    (flagsFrom n s tail).length = tail.length := by
  induction tail generalizing s <;> simp [flagsFrom, *]

theorem flags_length (n : Nat) (word : List Nat) :
    (flags n word).length = word.length - (n-1) := by
  simp [flags, flagsFrom_length]

/-- Every clean flag is an actual permutation-window occurrence, including
duplicates and seams. The old prefix count is retained explicitly. -/
theorem flagsFrom_clean_count (n : Nat) (hn : 1 ≤ n) (text tail : List Nat) :
    (literalPermutationWindows n (text ++ tail)).length =
      (literalPermutationWindows n text).length +
        (flagsFrom n (literalStateOf n text) tail).count true := by
  induction tail generalizing text with
  | nil => simp [flagsFrom]
  | cons a tail ih =>
      have next := ih (text ++ [a])
      rw [literalPermutationWindows_append_singleton n hn] at next
      simp only [List.length_append] at next
      rw [flagsFrom, literalStateStep_correct n hn]
      change (literalPermutationWindows n (text ++ a :: tail)).length = _
      rw [show text ++ a :: tail = (text ++ [a]) ++ tail by simp]
      rw [next]
      cases hit : literalPermTest n (lastSymbols (n-1) text ++ [a]) <;>
        simp [nextLiteralWindow, literalStateOf, hit, Nat.add_assoc,
          Nat.add_left_comm, Nat.add_comm]

theorem flags_clean_count (n : Nat) (hn : 1 ≤ n) (word : List Nat) :
    (flags n word).count true = (literalPermutationWindows n word).length := by
  have counted := flagsFrom_clean_count n hn (word.take (n-1)) (word.drop (n-1))
  have short : (word.take (n-1)).length < n := by
    have := List.length_take_le (n-1) word
    omega
  rw [List.take_append_drop, literalPermutationWindows_eq_nil_of_short n _ short] at counted
  simpa [flags] using counted.symm

theorem bool_counts (xs : List Bool) : xs.count true + xs.count false = xs.length := by
  induction xs with
  | nil => simp
  | cons b xs ih =>
      cases b with
      | false =>
          rw [List.count_cons_of_ne (by decide : false ≠ true), List.count_cons_self,
            List.length_cons]
          omega
      | true =>
          rw [List.count_cons_self, List.count_cons_of_ne (by decide : true ≠ false),
            List.length_cons]
          omega

def cleanCount (n : Nat) (word : List Nat) : Nat := (flags n word).count true
def dirtyCount (n : Nat) (word : List Nat) : Nat := (flags n word).count false
def distinctCount (n : Nat) (word : List Nat) : Nat :=
  (literalPermutationWindows n word).toFinset.card
def repeatCount (n : Nat) (word : List Nat) : Nat :=
  cleanCount n word - distinctCount n word

/-- Unrestricted literal length accounting: no row or whole-course ansatz. -/
theorem literal_length_ledger (n : Nat) (hn : 1 ≤ n) (word : List Nat)
    (long : n-1 ≤ word.length) :
    word.length = (n-1) + distinctCount n word + repeatCount n word + dirtyCount n word := by
  have counts := bool_counts (flags n word)
  rw [flags_length] at counts
  have enough : distinctCount n word ≤ cleanCount n word := by
    unfold distinctCount cleanCount
    rw [flags_clean_count n hn]
    exact List.toFinset_card_le _
  change cleanCount n word + dirtyCount n word = word.length - (n-1) at counts
  unfold repeatCount
  omega

theorem coverage_distinct_count (n : Nat) (word : List Nat) (covers : IsSuperperm n word) :
    distinctCount n word = n.factorial := by
  have same : (literalPermutationWindows n word).toFinset = permsOf (Finset.Icc 1 n) := by
    ext p
    simp only [List.mem_toFinset, mem_literalPermutationWindows_iff, mem_permsOf]
    exact ⟨fun hp => hp.1, fun hp => ⟨hp, covers p hp⟩⟩
  rw [distinctCount, same, card_permsOf]
  simp

theorem covering_length_ledger (n : Nat) (hn : 1 ≤ n) (word : List Nat)
    (long : n-1 ≤ word.length) (covers : IsSuperperm n word) :
    word.length = n.factorial + (n-1) + repeatCount n word + dirtyCount n word := by
  have counted := literal_length_ledger n hn word long
  rw [coverage_distinct_count n word covers] at counted
  omega

def bit (b : Bool) : Nat := if b then 1 else 0

def rises : Bool → List Bool → Nat
  | _, [] => 0
  | before, b :: rest => (if b && !before then 1 else 0) + rises b rest

def falls : Bool → List Bool → Nat
  | _, [] => 0
  | before, b :: rest => (if before && !b then 1 else 0) + falls b rest

def continuations : Bool → List Bool → Nat
  | _, [] => 0
  | before, b :: rest => (if !before && !b then 1 else 0) + continuations b rest

def finalBit : Bool → List Bool → Bool
  | before, [] => before
  | _, b :: rest => finalBit b rest

theorem runs_telescope (before : Bool) (xs : List Bool) :
    rises before xs + bit before = falls before xs + bit (finalBit before xs) := by
  induction xs generalizing before with
  | nil => simp [rises, falls, finalBit]
  | cons b xs ih =>
      have next := ih b
      cases last : finalBit b xs <;> cases before <;> cases b <;>
        simp [rises, falls, bit, finalBit, last] at next ⊢ <;> omega

theorem dirty_partition (before : Bool) (xs : List Bool) :
    xs.count false = falls before xs + continuations before xs := by
  induction xs generalizing before with
  | nil => simp [falls, continuations]
  | cons b xs ih =>
      have next := ih b
      cases before <;> cases b <;> simp [falls, continuations] at next ⊢ <;> omega

def cleanRuns (n : Nat) (word : List Nat) : Nat := rises false (flags n word)

/-- With a clean first window, these are exactly dirty windows after the
first window of their dirty run. This does not inspect whether a bend was forced. -/
def dirtyContinuations (n : Nat) (word : List Nat) : Nat :=
  continuations false (flags n word)

def StartsClean (n : Nat) (word : List Nat) : Prop :=
  ∃ rest, flags n word = true :: rest

def EndsClean (n : Nat) (word : List Nat) : Prop := finalBit false (flags n word) = true

theorem clean_dirty_run_ledger (n : Nat) (word : List Nat) (ends : EndsClean n word) :
    dirtyCount n word + 1 = cleanRuns n word + dirtyContinuations n word := by
  have flow := runs_telescope false (flags n word)
  have partition := dirty_partition false (flags n word)
  change finalBit false (flags n word) = true at ends
  rw [ends] at flow
  simp only [bit, Bool.false_eq_true, if_false, if_true, Nat.add_zero] at flow
  unfold dirtyCount cleanRuns dirtyContinuations
  omega

/-- Signed extra visits avoid hiding an unproved orbit-count lower bound in
natural subtraction. For a covering word they count extra clean-run visits
once the standard rotation-orbit partition is identified. -/
def extraVisits (n : Nat) (word : List Nat) : Int :=
  (cleanRuns n word : Int) - ((n-1).factorial : Int)

def reducedBudget (n : Nat) (word : List Nat) : Int :=
  extraVisits n word + dirtyContinuations n word + repeatCount n word

/-- Exact all-n F+C+R ledger for actual words, not an assumed row selection.
Start/end conditions make the run interpretation agree with the reduced codec.
No no-repeat or bounded dirty-depth hypothesis is used. -/
theorem covering_reduced_ledger (n : Nat) (hn : 2 ≤ n) (word : List Nat)
    (long : n-1 ≤ word.length) (covers : IsSuperperm n word)
    (_starts : StartsClean n word) (ends : EndsClean n word) :
    (word.length : Int) = (n.factorial : Int) + ((n-1).factorial : Int) +
      (n : Int) - 2 + reducedBudget n word := by
  have length := covering_length_ledger n (by omega) word long covers
  have runs := clean_dirty_run_ledger n word ends
  have lengthI : (word.length : Int) = (n.factorial : Int) + ((n-1 : Nat) : Int) +
      (repeatCount n word : Int) + (dirtyCount n word : Int) := by exact_mod_cast length
  have runsI : (dirtyCount n word : Int) + 1 =
      (cleanRuns n word : Int) + (dirtyContinuations n word : Int) := by exact_mod_cast runs
  have nsub : ((n-1 : Nat) : Int) = (n : Int) - 1 := by omega
  unfold reducedBudget extraVisits
  omega

theorem n7_shorter_iff (word : List Nat) (long : 6 ≤ word.length)
    (covers : IsSuperperm 7 word) (starts : StartsClean 7 word) (ends : EndsClean 7 word) :
    word.length ≤ 5904 ↔ reducedBudget 7 word ≤ 139 := by
  have ledger := covering_reduced_ledger 7 (by decide) word long covers starts ends
  norm_num [Nat.factorial] at ledger
  omega

/-- A direct accounting check against the recorded Andrei statistics; the
statistics themselves are supplied by the independent native corpus audit. -/
theorem andrei_budget_arithmetic :
    5040 + 720 + 7 - 2 + (66 + 74 + 0 : Nat) = 5905 ∧
    859 + 1 = 786 + (74 : Nat) := by decide

/-- Reuse the existing permutation enumeration proof at ANY even row count,
not only the old fixed-24 certificate. Hidden deficit-one cycles stay charged. -/
theorem four_port_trails_even (ds : List Nat) (valid : ∀ d ∈ ds, d < 5)
    (evenLength : ds.length % 2 = 0) : JayCompletionParity.trails 4 ds % 2 = 0 := by
  have hp : List.range 4 ∈ JayCompletionParity.permutations 4 := by decide
  have accumulated := (JayCompletionParity.accumulated7 ds (List.range 4) hp valid).2
  have identityCycles : JayCompletionParity.orbitCount (List.range 4) = 4 := by decide
  rw [identityCycles] at accumulated
  simp only [JayCompletionParity.trails]
  omega

theorem four_port_not_one_trail (ds : List Nat) (valid : ∀ d ∈ ds, d < 5)
    (evenLength : ds.length % 2 = 0) : JayCompletionParity.trails 4 ds ≠ 1 := by
  have parity := four_port_trails_even ds valid evenLength
  omega

/-- The ordinary N=7 source generator: rotate the five old positions, then
exchange the final two. At deficit zero the rotation is one; otherwise it
is v+1 = 6-deficit. This is the positional action in the native row step. -/
def source7 (d : Nat) : Equiv.Perm (Fin 5) :=
  (finRotate 5) ^ (if d = 0 then 1 else 6-d) * Equiv.swap 3 4

def OrdinaryDeficit7 (d : Nat) : Prop := d = 0 ∨ d = 2 ∨ d = 3 ∨ d = 4

/-- Exact tables of images, hence an equality of actions on ANY old labels,
not a test on the occupation count of one particular word. -/
theorem source7_literal_images :
    List.ofFn (fun i : Fin 5 => (source7 0 i).val) = [1,2,3,0,4] ∧
    List.ofFn (fun i : Fin 5 => (source7 2 i).val) = [4,0,1,3,2] ∧
    List.ofFn (fun i : Fin 5 => (source7 3 i).val) = [3,4,0,2,1] ∧
    List.ofFn (fun i : Fin 5 => (source7 4 i).val) = [2,3,4,1,0] := by decide

theorem source7_sign (d : Nat) : Equiv.Perm.sign (source7 d) = -1 := by
  have rotation : Equiv.Perm.sign (finRotate 5) = 1 := by norm_num [sign_finRotate]
  unfold source7
  rw [map_mul, map_pow, rotation]
  simp [Equiv.Perm.sign_swap (by decide : (3 : Fin 5) ≠ 4)]

theorem source7_product_sign (ds : List Nat) :
    Equiv.Perm.sign (ds.map source7).prod = (-1 : Intˣ) ^ ds.length := by
  induction ds with
  | nil => simp
  | cons d ds ih =>
      rw [List.map_cons, List.prod_cons, map_mul, source7_sign, ih, List.length_cons]
      exact (_root_.pow_succ' (-1 : Intˣ) ds.length).symm

/-- Closure in the literal source permutation forces even length; it is no
longer a freely supplied parity assumption in the final obstruction. -/
theorem closed_source7_even (ds : List Nat) (closed : (ds.map source7).prod = 1) :
    ds.length % 2 = 0 := by
  have signed := source7_product_sign ds
  rw [closed, map_one] at signed
  have even := (neg_one_pow_eq_one_iff_even (by decide : (-1 : Intˣ) ≠ 1)).mp signed.symm
  exact Nat.even_iff.mp even

theorem closed_ordinary_source7_not_one_trail (ds : List Nat)
    (ordinary : ∀ d ∈ ds, OrdinaryDeficit7 d)
    (closed : (ds.map source7).prod = 1) : JayCompletionParity.trails 4 ds ≠ 1 := by
  apply four_port_not_one_trail ds ?_ (closed_source7_even ds closed)
  intro d hd
  have valid := ordinary d hd
  unfold OrdinaryDeficit7 at valid
  omega

end Coeff2.Charlieplex.ReducedAlphabetLedger
