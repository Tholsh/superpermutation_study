import Coeff2.CharlieLiteralCertificate

/-!
# An exact streaming state for literal superpermutations

This state is computed from symbol strings, not supplied by a realization
predicate. All permutation windows, including duplicates and seam windows,
are accounted for one appended symbol at a time. The occupation set alone
does not remember earlier repeats or invalid symbols, so both flags are kept.
-/

namespace Coeff2.Charlieplex

def lastSymbols (count : ℕ) (text : List ℕ) : List ℕ :=
  text.drop (text.length - count)

theorem lastSymbols_of_short (count : ℕ) (text : List ℕ)
    (h : text.length ≤ count) : lastSymbols count text = text := by
  simp [lastSymbols, Nat.sub_eq_zero_of_le h]

theorem lastSymbols_cons (count symbol : ℕ) (text : List ℕ)
    (h : count ≤ text.length) :
    lastSymbols count (symbol :: text) = lastSymbols count text := by
  unfold lastSymbols
  simp only [List.length_cons]
  have heq : text.length + 1 - count = (text.length - count) + 1 := by omega
  rw [heq, List.drop_succ_cons]

theorem lastSymbols_append_singleton (count symbol : ℕ) (text : List ℕ) :
    lastSymbols count (text ++ [symbol]) =
      lastSymbols count (lastSymbols count text ++ [symbol]) := by
  by_cases hshort : text.length ≤ count
  · rw [lastSymbols_of_short count text hshort]
  · cases count with
    | zero => simp [lastSymbols]
    | succ count =>
        unfold lastSymbols
        simp only [List.length_append, List.length_singleton, List.length_drop]
        rw [List.drop_append_of_le_length (by omega :
          text.length + 1 - (count + 1) ≤ text.length)]
        rw [List.drop_append_of_le_length (by simp only [List.length_drop]; omega :
          text.length - (text.length - (count + 1)) + 1 - (count + 1) ≤
            (text.drop (text.length - (count + 1))).length)]
        rw [List.drop_drop]
        congr 2
        omega

theorem literalPermTest_false_of_short (n : ℕ) (text : List ℕ)
    (h : text.length < n) : literalPermTest n text = false := by
  apply Bool.eq_false_iff.mpr
  intro htest
  have := ((literalPermTest_eq_true n text).mp htest).length
  omega

theorem literalPermutationWindows_of_length_le (n : ℕ) (hn : 1 ≤ n)
    (text : List ℕ) (h : text.length ≤ n) :
    literalPermutationWindows n text =
      if literalPermTest n text then [text] else [] := by
  cases text with
  | nil =>
      rw [literalPermutationWindows_eq_nil_of_short n [] (by simpa using (show 0 < n by omega)),
        literalPermTest_false_of_short n [] (by simpa using (show 0 < n by omega))]
      rfl
  | cons symbol text =>
      rw [literalPermutationWindows_cons, List.take_of_length_le h,
        literalPermutationWindows_eq_nil_of_short n text (by
          simp only [List.length_cons] at h; omega)]

def nextLiteralWindow (n : ℕ) (text : List ℕ) (symbol : ℕ) : List ℕ :=
  lastSymbols (n - 1) text ++ [symbol]

/-- Appending one symbol creates at most one new permutation occurrence.
This is an equality of occurrence lists, not a deduplicated cache identity. -/
theorem literalPermutationWindows_append_singleton (n : ℕ) (hn : 1 ≤ n)
    (text : List ℕ) (symbol : ℕ) :
    literalPermutationWindows n (text ++ [symbol]) =
      literalPermutationWindows n text ++
        if literalPermTest n (nextLiteralWindow n text symbol)
        then [nextLiteralWindow n text symbol] else [] := by
  induction text with
  | nil =>
      rw [literalPermutationWindows_eq_nil_of_short n [] (by simpa using (show 0 < n by omega))]
      simp only [nextLiteralWindow, lastSymbols, List.length_nil, Nat.zero_sub,
        List.drop_nil, List.nil_append]
      exact literalPermutationWindows_of_length_le n hn [symbol] (by simpa using hn)
  | cons first text ih =>
      by_cases hshort : (first :: text).length < n
      · rw [literalPermutationWindows_eq_nil_of_short n (first :: text) hshort]
        have htail := lastSymbols_of_short (n - 1) (first :: text) (by omega)
        simp only [nextLiteralWindow, htail, List.nil_append]
        exact literalPermutationWindows_of_length_le n hn _ (by
          simp only [List.length_append, List.length_singleton]; omega)
      · have htail : nextLiteralWindow n (first :: text) symbol =
            nextLiteralWindow n text symbol := by
          unfold nextLiteralWindow
          rw [lastSymbols_cons (n - 1) first text (by
            simp only [List.length_cons] at hshort; omega)]
        have htake : (first :: (text ++ [symbol])).take n =
            (first :: text).take n :=
          List.take_append_of_le_length (l₁ := first :: text) (l₂ := [symbol])
            (i := n) (by omega)
        simp only [List.cons_append, literalPermutationWindows_cons, htake, ih, htail]
        split <;> simp

@[ext] structure LiteralSearchState where
  boundary : List ℕ
  occupied : Finset (List ℕ)
  length : ℕ
  alphabetOK : Bool
  noRepeat : Bool
deriving DecidableEq

def literalStateOf (n : ℕ) (text : List ℕ) : LiteralSearchState where
  boundary := lastSymbols (n - 1) text
  occupied := (literalPermutationWindows n text).toFinset
  length := text.length
  alphabetOK := literalAlphabetTest n text
  noRepeat := literalNoRepeatTest n text

/-- Append a symbol without retaining or rescanning the earlier string. -/
def literalStateStep (n : ℕ) (state : LiteralSearchState) (symbol : ℕ) :
    LiteralSearchState :=
  let window := state.boundary ++ [symbol]
  let hit := literalPermTest n window
  { boundary := lastSymbols (n - 1) window
    occupied := if hit then insert window state.occupied else state.occupied
    length := state.length + 1
    alphabetOK := state.alphabetOK && decide (1 ≤ symbol ∧ symbol ≤ n)
    noRepeat := state.noRepeat && (!hit || decide (window ∉ state.occupied)) }

theorem literalNoRepeatTest_append_singleton (n : ℕ) (hn : 1 ≤ n)
    (text : List ℕ) (symbol : ℕ) :
    literalNoRepeatTest n (text ++ [symbol]) =
      (literalNoRepeatTest n text &&
        (!(literalPermTest n (nextLiteralWindow n text symbol)) ||
          decide (nextLiteralWindow n text symbol ∉
            (literalPermutationWindows n text).toFinset))) := by
  rw [Bool.eq_iff_iff]
  simp only [literalNoRepeatTest_eq_true, Bool.and_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', decide_eq_true_eq, List.mem_toFinset,
    literalPermutationWindows_append_singleton n hn]
  cases hit : literalPermTest n (nextLiteralWindow n text symbol) <;>
    simp [List.nodup_append', and_comm]

/-- The streaming transition is exactly a full rescan of the extended text. -/
theorem literalStateStep_correct (n : ℕ) (hn : 1 ≤ n)
    (text : List ℕ) (symbol : ℕ) :
    literalStateStep n (literalStateOf n text) symbol =
      literalStateOf n (text ++ [symbol]) := by
  apply LiteralSearchState.ext
  · exact (lastSymbols_append_singleton (n - 1) symbol text).symm
  · change (if literalPermTest n (nextLiteralWindow n text symbol) then
        insert (nextLiteralWindow n text symbol) (literalPermutationWindows n text).toFinset
      else (literalPermutationWindows n text).toFinset) = _
    rw [literalStateOf, literalPermutationWindows_append_singleton n hn]
    cases hit : literalPermTest n (nextLiteralWindow n text symbol) <;> simp
  · simp [literalStateStep, literalStateOf]
  · simp [literalStateStep, literalStateOf, literalAlphabetTest, List.all_append]
  · exact (literalNoRepeatTest_append_singleton n hn text symbol).symm

def literalStateRun (n : ℕ) (state : LiteralSearchState) : List ℕ → LiteralSearchState
  | [] => state
  | symbol :: rest => literalStateRun n (literalStateStep n state symbol) rest

/-- Literal fragments compose by passing the resulting state to the next
fragment. Seam windows are processed normally, not replaced by set union. -/
theorem literalStateRun_append (n : ℕ) (state : LiteralSearchState)
    (left right : List ℕ) :
    literalStateRun n state (left ++ right) =
      literalStateRun n (literalStateRun n state left) right := by
  induction left generalizing state with
  | nil => rfl
  | cons symbol rest ih => simp only [List.cons_append, literalStateRun, ih]

/-- Induction over arbitrary symbol continuations, including waste runs. -/
theorem literalStateRun_correct (n : ℕ) (hn : 1 ≤ n)
    (text continuation : List ℕ) :
    literalStateRun n (literalStateOf n text) continuation =
      literalStateOf n (text ++ continuation) := by
  induction continuation generalizing text with
  | nil => simp [literalStateRun]
  | cons symbol rest ih =>
      rw [literalStateRun, literalStateStep_correct n hn, ih]
      simp only [List.append_assoc, List.singleton_append]

/-- This is the literal completion gate, evaluated from the finite state.
No-repeat remains optional: coverage alone allows repeated permutations. -/
def literalStateAccept (n budget : ℕ) (state : LiteralSearchState) : Bool :=
  state.alphabetOK && (decide (state.length = budget) &&
    (literalPermutationCatalogue n).all fun permutation =>
      decide (permutation ∈ state.occupied))

theorem literalStateAccept_correct (n budget : ℕ) (text : List ℕ) :
    literalStateAccept n budget (literalStateOf n text) =
      literalWordCompletionTest n budget text := by
  rw [Bool.eq_iff_iff]
  simp only [literalStateAccept, literalStateOf, literalWordCompletionTest,
    literalCompletionTest, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq, List.mem_toFinset, List.contains_iff_mem]

/-- Equal states have equal states after every continuation. This justifies
merging histories, without any corpus assumption or supplied realization. -/
theorem literalState_same_future (n : ℕ) (hn : 1 ≤ n)
    (left right : List ℕ) (h : literalStateOf n left = literalStateOf n right)
    (continuation : List ℕ) :
    literalStateOf n (left ++ continuation) =
      literalStateOf n (right ++ continuation) := by
  rw [← literalStateRun_correct n hn, ← literalStateRun_correct n hn, h]

/-- The same suffix succeeds from both histories, or from neither. -/
theorem literalState_same_completions (n budget : ℕ) (hn : 1 ≤ n)
    (left right : List ℕ) (h : literalStateOf n left = literalStateOf n right)
    (continuation : List ℕ) :
    literalWordCompletionTest n budget (left ++ continuation) =
      literalWordCompletionTest n budget (right ++ continuation) := by
  rw [← literalStateAccept_correct, ← literalStateAccept_correct,
    literalState_same_future n hn left right h continuation]

theorem literalState_same_repeat_status (n : ℕ) (hn : 1 ≤ n)
    (left right : List ℕ) (h : literalStateOf n left = literalStateOf n right)
    (continuation : List ℕ) :
    literalNoRepeatTest n (left ++ continuation) =
      literalNoRepeatTest n (right ++ continuation) := by
  exact congrArg LiteralSearchState.noRepeat
    (literalState_same_future n hn left right h continuation)

/-- A repeat cannot be repaired by a later continuation. This only rejects
single-use searches, not the general superpermutation problem. -/
theorem literalStateRun_repeat_stays_false (n : ℕ) (state : LiteralSearchState)
    (h : state.noRepeat = false) (continuation : List ℕ) :
    (literalStateRun n state continuation).noRepeat = false := by
  induction continuation generalizing state with
  | nil => exact h
  | cons symbol rest ih =>
      apply ih
      simp [literalStateStep, h]

theorem literalCollision_forbids_singleUse (n : ℕ) (hn : 1 ≤ n)
    (text : List ℕ) (symbol : ℕ)
    (hhit : literalPermTest n (nextLiteralWindow n text symbol) = true)
    (hseen : nextLiteralWindow n text symbol ∈ (literalStateOf n text).occupied)
    (continuation : List ℕ) :
    literalNoRepeatTest n ((text ++ [symbol]) ++ continuation) = false := by
  have hstep : (literalStateStep n (literalStateOf n text) symbol).noRepeat = false := by
    change (_ && (!(literalPermTest n (nextLiteralWindow n text symbol)) ||
      decide (nextLiteralWindow n text symbol ∉ (literalStateOf n text).occupied))) = false
    simp [hhit, hseen]
  rw [literalStateStep_correct n hn] at hstep
  have hrun := literalStateRun_repeat_stays_false n _ hstep continuation
  rw [literalStateRun_correct n hn] at hrun
  exact hrun

/-- A state-machine success is precisely an actual literal superpermutation,
with its alphabet and length checked. There is no graph-realization premise. -/
theorem literalStateRun_accept_iff (n budget : ℕ) (hn : 1 ≤ n)
    (text continuation : List ℕ) :
    literalStateAccept n budget (literalStateRun n (literalStateOf n text) continuation) = true ↔
      (∀ symbol ∈ text ++ continuation, 1 ≤ symbol ∧ symbol ≤ n) ∧
        (text ++ continuation).length = budget ∧ IsSuperperm n (text ++ continuation) := by
  rw [literalStateRun_correct n hn, literalStateAccept_correct,
    literalWordCompletionTest_eq_true]

end Coeff2.Charlieplex
