import Coeff2.CharlieFragmentBendGate
import Coeff2.CharlieReducedDepthStream
import Coeff2.CharliePartialRowPort
import Coeff2.CharlieBalancedSourceSelection
import Coeff2.CharlieOccupationRecoveryClock
import Coeff2.CharlieSharedWasteResponseCheck
import Coeff2.CharlieBellmanJointFrontier
import Coeff2.CharlieRestrictedRowConstruction

/-! A curated entry point, not a new construction theorem.
The original modules retain their names and exact source bytes. These
checks expose the relevant statements, including their hypotheses.
The finite 27-row control checks the declared PORT MODEL only. -/
namespace OccupationTransportPublic
open Coeff2 Coeff2.Charlieplex

-- Literal occupation, not an abstract graph-realization assumption.
#check literalStateRun_accept_iff
#check LiteralReservoir.emitted_append
#check BellmanExactQuotient.literal_bellman_bridge
#check BellmanExactQuotient.summary_same_bellman
#check FragmentBendGate.freshAvailable_insert_iff
#check FragmentBendGate.gate_insert

-- Rows: algebra, ordered transport, and completion hypotheses stay separate.
#check PartialRowPort.transport_formula
#check PartialRowPort.row_visit_conservation
#check PartialRowPort.cyclic_ledger
#check PartialRowPort.ordered_exchange
#check PartialRowPort.near_full_hidden_two_cycle
#check BalancedSourceSelection.circuit_boundary_conserved
#check BalancedSourceSelection.circuit_charge_change
#check RestrictedCircleAssembly.exists_restricted_word

-- Literal gluing and shared labelled coverage.
#check PacketAssembly.assembled_covers
#check SharedWasteResponse.interaction_general
#check SharedWasteResponse.negative_interaction_iff
#check SharedWasteGluing.response_compose
#check SharedWasteGluing.best_response_compose
#check SharedWasteGluing.sharedWaste_shorter_in_context
#check SharedWasteGluing.coordinated_shorter
#check BellmanJointFrontier.union_allocation
#check BellmanJointFrontier.frontier_dominance

-- Integer clock recovery conditional on supplied transport balance.
#check OccupationRecoveryClock.coupled_recovery
#check OccupationRecoveryClock.closed_charge_solver
#check OccupationRecoveryClock.fresh_write_cost
#check OccupationRecoveryClock.unallocated_repeat_cost

-- Exact reduced accounting is not a choice of an optimal selection.
#check ReducedAlphabetLedger.covering_reduced_ledger
#check ReducedAlphabetLedger.logical_depth_roundtrip
#check ReducedAlphabetLedger.length_difference_eq_budget_difference

/-- Jakub Halfar's published ordinary row-length pattern. -/
def halfar27 : List Nat :=
  [2,6,6,6,4,6,6,6,4,6,6,6,4,6,6,4,6,6,6,4,6,6,6,4,6,6,6]

theorem halfar27_length : halfar27.length = 27 := by decide
theorem halfar27_charge : (halfar27.map (6 - ·)).sum = 16 := by decide

theorem halfar27_port_map :
    JayCompletionParity.run 5 (halfar27.map (6 - ·)) (List.range 5) =
      [4,0,3,1,2] := by decide

/-- In the defined five-port model, this deficit sequence returns with one
port cycle. This does NOT check the literal 27-loop source walk, the disjoint
four-copy packing, or the complete 46,174/46,173-character word. -/
theorem halfar27_one_port_cycle :
    JayCompletionParity.trails 5 (halfar27.map (6 - ·)) = 1 := by decide

-- The forbidden inference: a clean/dirty trace is NOT an occupation quotient.
theorem boolean_trace_not_occupation :
    ReducedAlphabetLedger.flags 3 [1,2,3] = ReducedAlphabetLedger.flags 3 [1,3,2] ∧
    (literalStateOf 3 [1,2,3]).occupied ≠ (literalStateOf 3 [1,3,2]).occupied := by decide

#print axioms halfar27_one_port_cycle
#print axioms boolean_trace_not_occupation
end OccupationTransportPublic
