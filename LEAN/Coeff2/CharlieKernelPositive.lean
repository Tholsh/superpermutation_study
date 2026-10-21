import Coeff2.CharlieKernelScaling
import Coeff2.CharlieLiteralCertificate
import Mathlib.Data.List.Sort

/-!
# An ordered, literal positive control for kernel pruning

Unlike the earlier histogram test, this file retains command order. Zero
encodes the dash command; positive entries count complete rotation orbits.
The reverse-prefix operations are the literal canonical kernel grammar.
No claim is made that this grammar covers every possible superpermutation.
-/

namespace Coeff2.Charlieplex.KernelPositive

open KernelScaling

/-- The 75-command kernel extracted from the supplied 5905 construction. -/
def commands5905 : List ℕ :=
  [4,6,6,6,4,4,6,6,6,6,0,6,6,6,6,4,6,6,6,3,6,6,6,6,0,
   6,6,6,6,4,6,6,4,6,6,6,6,0,6,6,6,6,4,6,6,4,6,6,6,6,0,
   6,6,6,6,3,6,6,6,4,6,6,6,6,0,6,6,6,6,4,4,6,6,6,4]

def rideEdges (n : ℕ) : ℕ → List ℕ
  | 0 => []
  | 1 => List.replicate (n - 1) 1
  | d + 2 => List.replicate (n - 1) 1 ++ [2] ++ rideEdges n (d + 1)

def kernelEdges (n : ℕ) : List ℕ → List ℕ
  | [] => []
  | 0 :: rest => 4 :: kernelEdges n rest
  | (d + 1) :: rest => rideEdges n (d + 1) ++
      (if rest = [] ∨ rest.headD 0 = 0 then [] else [3]) ++ kernelEdges n rest

def traceFrom (start : List ℕ) : List ℕ → List (List ℕ)
  | [] => [start]
  | weight :: rest => start :: traceFrom (reversePrefixStep weight start) rest

def vertices (n : ℕ) (commands : List ℕ) : List (List ℕ) :=
  traceFrom (List.range' 1 n) (kernelEdges n commands)

/-- A marker-last reduced state lifts to the literal next orbit start.
This is an identity of symbol lists, for arbitrary order and connector size. -/
theorem reduced_connector_lift (reduced : List ℕ) (marker k : ℕ) :
    reversePrefixStep (k + 1) (finishOrbit (reduced ++ [marker])) =
      reversePrefixStep k reduced ++ [marker] := by
  rw [finishOrbit_concat]
  simp [reversePrefixStep, List.append_assoc]

def wordCode (word : List ℕ) : ℕ := word.foldl (fun acc x => 10 * acc + x) 0

/-- Codes need not be assumed injective: distinct codes suffice to establish
distinct source words. This certificate is checked on the smaller orbit list. -/
def distinctTest (words : List (List ℕ)) : Bool :=
  decide (words.map wordCode).Nodup

theorem distinctTest_sound (words : List (List ℕ))
    (h : distinctTest words = true) : words.Nodup := by
  exact List.Nodup.of_map wordCode (of_decide_eq_true h)

/-- The existing direct-mode upper bound on additional score. -/
def scoreUpper (n remaining streak : ℕ) : ℕ :=
  remaining - (streak + remaining) / (n - 1)

def commandScore (n : ℕ) (commands : List ℕ) : ℤ :=
  (commands.sum : ℤ) - ((n - 2 : ℕ) : ℤ) * commands.length

def maximalStreak (n : ℕ) (commands : List ℕ) : ℕ :=
  (commands.reverse.takeWhile (· == n - 1)).length

abbrev prefixSurvives (n budget : ℕ) (target : ℤ) (commands : List ℕ) : Prop :=
  commands.length ≤ budget ∧ target ≤ commandScore n commands +
    scoreUpper n (budget - commands.length) (maximalStreak n commands)

def allPrefixesSurviveTest (n budget : ℕ) (target : ℤ) (commands : List ℕ) : Bool :=
  (List.range (commands.length + 1)).all fun cut =>
    decide (prefixSurvives n budget target (commands.take cut))

theorem allPrefixesSurviveTest_sound (n budget : ℕ) (target : ℤ)
    (commands : List ℕ) (h : allPrefixesSurviveTest n budget target commands = true) :
    ∀ cut ≤ commands.length, prefixSurvives n budget target (commands.take cut) := by
  intro cut hcut
  exact of_decide_eq_true (List.all_eq_true.mp h cut (List.mem_range.mpr (by omega)))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem kernel5905_inventory :
    commands5905.length = 75 ∧ commands5905.sum = 390 ∧
    commandScore 7 commands5905 = 15 := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem kernel5905_prefixes_checked :
    allPrefixesSurviveTest 7 75 15 commands5905 = true := by decide +kernel

theorem kernel5905_no_prefix_pruned :
    ∀ cut ≤ commands5905.length,
      prefixSurvives 7 75 15 (commands5905.take cut) :=
  allPrefixesSurviveTest_sound 7 75 15 commands5905 kernel5905_prefixes_checked

/-- Invert the implicit reduced weight-two connector before replacing it
with the reduced weight-three (full weight-four) dash connector. -/
def inversePrefixStep (k : ℕ) (p : List ℕ) : List ℕ :=
  (p.drop (p.length - k)).reverse ++ p.take (p.length - k)

theorem inverse_two_step (p : List ℕ) (hlen : 2 ≤ p.length) :
    inversePrefixStep 2 (reversePrefixStep 2 p) = p := by
  match p with
  | [] => simp at hlen
  | [a] => simp at hlen
  | a :: b :: rest => simp [inversePrefixStep, reversePrefixStep]

def reducedNext (p : List ℕ) : ℕ → List ℕ
  | 0 => reversePrefixStep 3 (inversePrefixStep 2 p)
  | d + 1 => reversePrefixStep 2 (p.rotate d)

def reducedRun (p : List ℕ) : List ℕ → List (List ℕ)
  | [] => []
  | d :: rest => ((List.range d).map fun phase => p.rotate phase) ++
      reducedRun (reducedNext p d) rest

def reduced5905 : List (List ℕ) := reducedRun [1,2,3,4,5,6] commands5905

theorem reducedRun_length (p : List ℕ) (commands : List ℕ) :
    (reducedRun p commands).length = commands.sum := by
  induction commands generalizing p with
  | nil => rfl
  | cons d rest ih => simp [reducedRun, ih]

/-- The full literal rotation orbit represented by a marker-last word. -/
def orbitWords (marker : ℕ) (p : List ℕ) : List (List ℕ) :=
  (List.range (p.length + 1)).map fun phase => (p ++ [marker]).rotate phase

theorem fullOrbitOccupation_length (marker n : ℕ) (states : List (List ℕ))
    (hlen : ∀ p ∈ states, p.length + 1 = n) :
    (states.flatMap (orbitWords marker)).length = states.length * n := by
  induction states with
  | nil => simp
  | cons p rest ih =>
    have hp := hlen p List.mem_cons_self
    have ht := ih (fun q hq => hlen q (List.mem_cons_of_mem p hq))
    simp [orbitWords, hp, ht, Nat.add_mul, Nat.add_comm]

theorem orbitWords_nodup (marker : ℕ) (p : List ℕ) (h : (p ++ [marker]).Nodup) :
    (orbitWords marker p).Nodup := by
  apply List.Nodup.map_on ?_ List.nodup_range
  intro i hi j hj heq
  apply rotate_injOn_lt h (by simpa using List.mem_range.mp hi)
    (by simpa using List.mem_range.mp hj) heq

theorem orbitWords_disjoint (marker : ℕ) (p q : List ℕ)
    (hp : (p ++ [marker]).Nodup) (hne : p ≠ q) :
    List.Disjoint (orbitWords marker p) (orbitWords marker q) := by
  intro word hleft hright
  obtain ⟨i, _, hi⟩ := List.mem_map.mp hleft
  obtain ⟨j, _, hj⟩ := List.mem_map.mp hright
  have hpw : List.IsRotated (p ++ [marker]) word := ⟨i, hi⟩
  have hqw : List.IsRotated (q ++ [marker]) word := ⟨j, hj⟩
  have hr := hpw.trans hqw.symm
  exact hne (isRotated_concat_inj hp hr)

/-- A duplicate-free list of reduced states certifies occupation of all
their full-order phases, not just one chosen representative per orbit. -/
theorem fullOrbitOccupation_nodup (marker : ℕ) (states : List (List ℕ))
    (hstates : states.Nodup) (hwords : ∀ p ∈ states, (p ++ [marker]).Nodup) :
    (states.flatMap (orbitWords marker)).Nodup := by
  apply List.nodup_flatMap.mpr
  refine ⟨fun p hp => orbitWords_nodup marker p (hwords p hp), ?_⟩
  apply (List.Pairwise.and_mem.mp hstates).imp
  intro p q h
  exact orbitWords_disjoint marker p q (hwords p h.1) h.2.2

end Coeff2.Charlieplex.KernelPositive
