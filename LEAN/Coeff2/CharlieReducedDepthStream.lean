import Coeff2.CharlieReducedAlphabetLedger

/-!
# Logical run-depth projection of the reduced alphabet

Each dirty instruction is preceded by its clean-run depth. Consecutive dirty
instructions therefore have depth zero; the final clean run is stored apart.
This is the unbounded logical first coordinate of SPRA, not its packed byte
format. Offsets and literal symbol boundaries must still be retained to decode
the word or decide occupation. The Boolean projection is not a Bellman quotient.
-/
namespace Coeff2.Charlieplex.ReducedAlphabetLedger

def depthScan : Nat → List Bool → List Nat × Nat
  | pending, [] => ([], pending)
  | pending, true :: rest => depthScan (pending+1) rest
  | pending, false :: rest =>
      let result := depthScan 0 rest
      (pending :: result.1, result.2)

def expandDepths : List Nat → Nat → List Bool
  | [], finalClean => List.replicate finalClean true
  | d :: rest, finalClean => List.replicate d true ++ false :: expandDepths rest finalClean

theorem expand_depthScan (pending : Nat) (xs : List Bool) :
    expandDepths (depthScan pending xs).1 (depthScan pending xs).2 =
      List.replicate pending true ++ xs := by
  induction xs generalizing pending with
  | nil => simp [depthScan, expandDepths]
  | cons b xs ih =>
      cases b with
      | false =>
          simpa [depthScan, expandDepths] using
            congrArg (fun tail => List.replicate pending true ++ false :: tail) (ih 0)
      | true =>
          simpa [depthScan, List.replicate_add, List.append_assoc] using ih (pending+1)

theorem depthScan_dirty_count (pending : Nat) (xs : List Bool) :
    (depthScan pending xs).1.length = xs.count false := by
  induction xs generalizing pending with
  | nil => simp [depthScan]
  | cons b xs ih => cases b <;> simp [depthScan, ih]

theorem depthScan_clean_count (pending : Nat) (xs : List Bool) :
    (depthScan pending xs).1.sum + (depthScan pending xs).2 = pending + xs.count true := by
  induction xs generalizing pending with
  | nil => simp [depthScan]
  | cons b xs ih =>
      cases b with
      | false => simpa [depthScan, Nat.add_assoc] using congrArg (pending + ·) (ih 0)
      | true => simpa [depthScan, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih (pending+1)

/-- A zero first coordinate is exactly a dirty continuation, including the
logical initial previous=false convention from the literal ledger. A clean
first window rules out a spurious leading continuation in canonical inputs. -/
theorem depthScan_zero_count (pending : Nat) (xs : List Bool) :
    (depthScan pending xs).1.count 0 = continuations (decide (pending ≠ 0)) xs := by
  induction xs generalizing pending with
  | nil => simp [depthScan, continuations]
  | cons b xs ih =>
      cases b with
      | false =>
          by_cases zero : pending = 0 <;>
            simp [depthScan, continuations, ih, zero, Nat.add_comm]
      | true =>
          simpa [depthScan, continuations] using ih (pending+1)

def depthsOf (n : Nat) (word : List Nat) : List Nat × Nat := depthScan 0 (flags n word)

theorem logical_depth_roundtrip (n : Nat) (word : List Nat) :
    expandDepths (depthsOf n word).1 (depthsOf n word).2 = flags n word := by
  simpa [depthsOf] using expand_depthScan 0 (flags n word)

theorem zero_depths_are_dirty_continuations (n : Nat) (word : List Nat) :
    (depthsOf n word).1.count 0 = dirtyContinuations n word := by
  simpa [depthsOf, dirtyContinuations] using depthScan_zero_count 0 (flags n word)

theorem dirty_instructions_count (n : Nat) (word : List Nat) :
    (depthsOf n word).1.length = dirtyCount n word := depthScan_dirty_count 0 _

theorem omitted_clean_symbols_count (n : Nat) (word : List Nat) :
    (depthsOf n word).1.sum + (depthsOf n word).2 = cleanCount n word := by
  simpa [depthsOf, cleanCount] using depthScan_clean_count 0 (flags n word)

/-- A candidate's exact shortening target can be read from the reduced
depth coordinate, but coverage and endpoint conditions remain literal. -/
theorem n7_shorter_iff_depth_budget (word : List Nat) (long : 6 ≤ word.length)
    (covers : IsSuperperm 7 word) (starts : StartsClean 7 word) (ends : EndsClean 7 word) :
    word.length ≤ 5904 ↔ extraVisits 7 word +
      ((depthsOf 7 word).1.count 0 : Int) + repeatCount 7 word ≤ 139 := by
  rw [n7_shorter_iff word long covers starts ends, zero_depths_are_dirty_continuations]
  rfl

/-- Once both actual words cover, every length change is exactly the change
in the three reduced budgets. No fixed trail inventory is assumed. -/
theorem length_difference_eq_budget_difference (n : Nat) (hn : 2 ≤ n)
    (before after : List Nat)
    (beforeLong : n-1 ≤ before.length) (afterLong : n-1 ≤ after.length)
    (beforeCovers : IsSuperperm n before) (afterCovers : IsSuperperm n after)
    (beforeStarts : StartsClean n before) (afterStarts : StartsClean n after)
    (beforeEnds : EndsClean n before) (afterEnds : EndsClean n after) :
    (after.length : Int) - (before.length : Int) =
      reducedBudget n after - reducedBudget n before := by
  have old := covering_reduced_ledger n hn before beforeLong beforeCovers beforeStarts beforeEnds
  have new := covering_reduced_ledger n hn after afterLong afterCovers afterStarts afterEnds
  omega

end Coeff2.Charlieplex.ReducedAlphabetLedger
