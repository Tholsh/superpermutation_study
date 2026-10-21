import Coeff2.CharlieSharedWasteGluing

/-!
# Kernel-checked controls for the shared-waste response
These are finite literal-scanner checks, proved by kernel reduction (decide),
not native_decide. The synthetic controls are deliberately redundant dirty
buffers, NOT complete superpermutations or new record constructions.
The n=11 witness comes from the independently scanned proper-neutral-v1
experiment; this module checks its local patch identity, not a 43-million
symbol word inside Lean.
-/
namespace Coeff2.Charlieplex.SharedWasteResponseCheck
open LiteralReservoir ThreeLevelBoundary PacketAssembly SharedWasteResponse SharedWasteGluing

set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

def blockLeft (n : ℕ) : List ℕ := List.range' 1 n ++ List.replicate n 1
def blockRight (n : ℕ) : List ℕ :=
  List.replicate n 1 ++ (1 :: (List.range' 2 (n-1)).reverse)

/-- One extra symbol of dirty overlap saves exactly one character; the
actual labelled union is unchanged. The shorter overlap is a source control. -/
def SharedBufferControl (n : ℕ) : Prop :=
  IsSeam (blockLeft n) (blockRight n) n ∧
  IsSeam (blockLeft n) (blockRight n) (n-1) ∧
  charge n ∅ ((blockRight n).take n) = 1 ∧
  extraShared n ∅ (blockLeft n) (blockRight n) ((blockRight n).take n) = ∅ ∧
  interaction n ∅ (blockLeft n) (blockRight n) n = -1 ∧
  interaction n ∅ (blockLeft n) (blockRight n) (n-1) = 0 ∧
  footprint n (glue (blockLeft n) (blockRight n) n) =
    footprint n (glue (blockLeft n) (blockRight n) (n-1)) ∧
  (glue (blockLeft n) (blockRight n) n).length + 1 =
    (glue (blockLeft n) (blockRight n) (n-1)).length

theorem shared_buffer_8 : SharedBufferControl 8 := by
  unfold SharedBufferControl IsSeam
  decide
theorem shared_buffer_9 : SharedBufferControl 9 := by
  unfold SharedBufferControl IsSeam
  decide
theorem shared_buffer_11 : SharedBufferControl 11 := by
  unfold SharedBufferControl IsSeam
  decide

theorem fresh_append_control :
    appendCharge 8 [1,2,3,4,5,6,7] ∅ [8,1,2] = 0 := by decide

theorem repeat_append_control :
    appendCharge 8 [1,2,3,4,5,6,7] ∅ [8,1,2,3,4,5,6,7,8] = 1 := by decide

/-- Source alphabet 0..A is relabelled to Lean's 1..11. -/
def oldFirst : List ℕ := [11, 3, 10, 1, 4, 9, 2, 5, 7, 6, 8, 3, 11, 10, 1, 4, 9, 2, 5, 7, 6, 8, 3, 11, 1, 10]

/-- Source alphabet 0..A is relabelled to Lean's 1..11. -/
def newFirst : List ℕ := [11, 3, 10, 1, 4, 9, 2, 5, 7, 6, 8, 3, 11, 1, 10]

/-- Source alphabet 0..A is relabelled to Lean's 1..11. -/
def oldSecond : List ℕ := [11, 10, 3, 1, 4, 9, 2, 5, 7, 6, 8, 3, 5, 1, 2, 4, 9, 10, 11]

/-- Source alphabet 0..A is relabelled to Lean's 1..11. -/
def newSecond : List ℕ := [11, 10, 3, 1, 4, 9, 2, 5, 7, 6, 8, 3, 11, 10, 1, 4, 9, 2, 5, 7, 6, 8, 3, 5, 1, 2, 4, 9, 10, 11]

/-- The real neutral exchange preserves joint coverage and exterior frames,
not the footprint or occurrence multiplicity of each patch separately. -/
theorem literal_neutral_control :
    footprint 11 oldFirst ∪ footprint 11 oldSecond =
      footprint 11 newFirst ∪ footprint 11 newSecond ∧
    (footprint 11 oldFirst ∪ footprint 11 oldSecond).card = 15 ∧
    oldFirst.take 10 = newFirst.take 10 ∧
    oldSecond.take 10 = newSecond.take 10 ∧
    lastSymbols 10 oldFirst = lastSymbols 10 newFirst ∧
    lastSymbols 10 oldSecond = lastSymbols 10 newSecond ∧
    oldFirst.length + oldSecond.length = newFirst.length + newSecond.length ∧
    oldFirst.length = newFirst.length + 11 ∧
    newSecond.length = oldSecond.length + 11 ∧
    footprint 11 oldFirst ≠ footprint 11 newFirst ∧
    (literalPermutationWindows 11 oldFirst).length +
        (literalPermutationWindows 11 oldSecond).length =
      (literalPermutationWindows 11 newFirst).length +
        (literalPermutationWindows 11 newSecond).length + 1 := by decide

#print axioms SharedWasteResponse.bit_union
#print axioms SharedWasteResponse.diff_mul
#print axioms SharedWasteResponse.front_union
#print axioms SharedWasteResponse.literal_front_update
#print axioms SharedWasteResponse.appendCharge_nonnegative
#print axioms SharedWasteResponse.charge_nonnegative
#print axioms SharedWasteResponse.fresh_partition
#print axioms SharedWasteResponse.fresh_union_card
#print axioms SharedWasteResponse.appendCharge_append
#print axioms SharedWasteResponse.appendCharge_potential
#print axioms SharedWasteResponse.footprint_mono
#print axioms SharedWasteResponse.footprint_long_shared
#print axioms SharedWasteResponse.footprint_glue
#print axioms SharedWasteResponse.interaction_general
#print axioms SharedWasteResponse.interaction_factor
#print axioms SharedWasteResponse.negative_interaction_iff
#print axioms SharedWasteGluing.advance_append
#print axioms SharedWasteGluing.response_compose
#print axioms SharedWasteGluing.best_response_compose
#print axioms SharedWasteGluing.charge_glue_factor
#print axioms SharedWasteGluing.sharedWaste_shorter_in_context
#print axioms SharedWasteGluing.coordinated_shorter
#print axioms ContextReplacement.replace_masked
#print axioms CoordinatedExchange.literal_exchange
#print axioms PacketAssembly.assembled_covers
#print axioms shared_buffer_8
#print axioms shared_buffer_9
#print axioms shared_buffer_11
#print axioms fresh_append_control
#print axioms repeat_append_control
#print axioms literal_neutral_control
end Coeff2.Charlieplex.SharedWasteResponseCheck

