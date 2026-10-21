# Claims, with the hypotheses left visible

All local symbol-level definitions use the alphabet `1,...,n`. Native n=8
files use `0,...,7`; the corresponding relabeling is `a -> a+1`.
No whole corpus word is asserted to have been checked inside Lean here.
Unless fully qualified, declaration names below assume
`open Coeff2 Coeff2.Charlieplex`, as in `PublicClaims.lean`.
Within a group, a bare theorem name abbreviates the namespace of that group's
qualified reference. `PublicClaims.lean` supplies copyable qualified checks.

Notation: n is the final symbol count; K=n-2 is the ordinary source-row
length; v is a chosen row's visible length; Q sums K-v over selected rows
(a detached fibre is not charged as a fictitious v=0 row). For completion
ports h=n-3, whereas the unrestricted literal boundary has n-1 symbols.
Those two boundary widths must not be identified without a proved quotient.
P(w) below is the set of literal permutation windows of w, not a count or
phase histogram. U is the set already occupied before the operation.

## 1. Literal occupation really is occupation

`CharlieLiteralBridge.lean` defines `literalPermutationWindows` by scanning actual
contiguous symbol windows. `literalStateRun_correct` and
`literalStateRun_accept_iff` connect symbol-by-symbol replay to those windows,
the original `IsSuperperm`, alphabet validity, and length. Repeated occurrences
remain visible. No graph-realization axiom replaces the word.

`FragmentBendGate.freshAvailable_insert_iff` and `FragmentBendGate.gate_insert` prove
that occupying a fresh permutation removes its own prefix from the fresh
availability gate. Dirty alternatives there change from voluntary fragments
to forced dirty steps. This is local reclassification, not a proof that future
cost depends only on that prefix. Dirty continuation in the codec is NOT the
history-dependent forced-bend statistic.

## 2. Row transport and selection are different obligations

`PartialRowPort.transport_formula` factors the defined general-deficit
port permutation as clock transport followed by an exceptional prefix turn.
`ordered_append`, `ordered_exchange`, and `ordered_superoperator` retain
composition order. `noncommuting_radix7` is a finite counterexample to
commutation. Equal histograms, total charge, or cycle counts are not enough.

`row_visit_conservation` proves the count

    (K+1)v + (K-v)(K+1) = K(K+1),   v <= K.

It does NOT prove that every named literal permutation in two completions
agrees. `cyclic_ledger` proves the factorial arithmetic yielding `F3(n)+Q`,
where `F3(n)=n!+(n-1)!+(n-2)!`; it does NOT include opening/joining overhead.
The port-formula-to-arbitrary-literal-partial-row bridge is still a separate
obligation, currently exercised by the native partial-row auditor.

`near_full_shared_header` and `near_full_hidden_two_cycle` explain why an
identity visible port map does not license discarding internal cycles or
duplicate headers. The native joint DP still excludes that near-full case.

`BalancedSourceSelection.circuit_boundary_conserved` certifies balance
WHEN the individual literal boundary differences form the stated circuit.
`circuit_charge_change` separately totals the signed full/short changes.
These theorems do not prove arbitrary row palettes can be packed or completed.
They principally cover full/short changes, not every v=2 partial-row exchange.

Pantone's imported row-completion proofs and
`RestrictedCircleAssembly.exists_restricted_word` construct words
under explicit closed-path, circle-cover, alphabet and endpoint hypotheses.
The latter is a conditional restricted-endpoint assembly theorem, not a
certificate of Halfar's concrete partial-row selection at n=8.

The `OccupationTransportPublic.halfar27_*` declarations in `PublicClaims.lean`
check: 27 row lengths, Q=16, return map
`[4,0,3,1,2]`, and its single cycle `(0 4 2 3 1)` in the defined five-port
completion model. It does not prove that these rows form
the literal source walk, that four disjoint copies exist, or their uniqueness.

## 3. What certifies phase opening and joining

`PacketAssembly.glue_length`, `assembled_length`, and `assembled_covers`
state the literal principle: if the supplied opened pieces cover all labels
and every supplied seam matches actual symbols, then the assembled word covers
all labels, with length equal to the piece-length sum minus seam overlaps.
Repeats are allowed; crossing windows can add coverage, not remove it.

This is the correct generic validator for boundary-phase moves. It does not
automatically prove that an arbitrary shorter cyclic opening retains the
piece's full footprint. That opening-footprint premise and the concrete seam
data have not been exported as a whole n=8 Lean certificate here.

For any valid overlap k, `SharedWasteResponse.interaction_general`
retains crossing-window contributions. With footprint P, initial occupied U,
and `charge(w)=|w|-(n-1)-|P(w)\U|`, it proves

    interaction = (n-1)-k + |(P(a) intersect P(b))\U| - |bridgeFresh|.

`bridgeFresh` is the set of newly covered labels created across the seam,
outside U and both individual footprints. The formula is an accounting
identity, not existence of a negative interaction.

The cleaner `SharedWasteResponse.interaction_factor`,
`SharedWasteResponse.negative_interaction_iff`, and
`SharedWasteGluing.sharedWaste_shorter_in_context` require k >= n-1. **Do not apply that
long-overlap simplification to the winning n=8 overlaps of width <= 5.**
The general identity and literal assembly law apply there instead.

`SharedWasteGluing.coordinated_shorter` permits different occupation in two separate patches
when their JOINT labelled emitted union agrees and both exterior states match.
It requires actual witness strings and a literal length gain, not just charge.
The included n=11 neutral patch is a finite local control, not a full record.

## 4. The actual occupation/transport coupling

For a clock of width w=m+1, prescribed charge b and lower copy floor u,
`OccupationRecoveryClock.coupled_recovery` proves exactly

    R(b,u) = sum u + Gamma(b - partial u).

Here `(partial x)_j=x_j-x_(j-1)` cyclically, and
`Gamma(z)=max_r sum_j (((r-j) mod w) * z_j)` is the sawtooth readout defined
by `ClockBalanceElimination.score`/`gamma`. In the Lean theorem the charge
argument is named `h`; it is not the scalar port width h=n-3 above.

`closed_charge_solver` constructs a least integer copy vector for a supplied
zero-sum charge. Fresh/allocated-repeat/unallocated-repeat theorems distinguish
the three recovery cases. They do NOT choose the dirty attachment ledger,
prove its connectedness, or lift a clock-feasible answer to a short word.

This is why “separate rules” must mean separately stated constraints inside
ONE problem, not independent minimizations whose optima can be added.

## 5. What DP is justified, and what remains native

`BellmanExactQuotient.literal_bellman_bridge` proves that bounded
symbol-level Bellman feasibility is equivalent to an actual alphabet-valid
continuation covering all permutations. `summary_same_bellman` gives a genuine
horizon-dependent quotient WHEN occupation agrees inside the entire literal
continuation cone and the outside-coverage obligations agree. It does not
prove that calculating that cone or quotient is cheap.

`SharedWasteGluing.response_compose` and `best_response_compose` prove
exact feasible/minimum profile composition retaining the literal coverage state

    (boundary, labelled occupied set).

Cost carries the length information, and the response predicate separately
checks the appended alphabet. This pair is not all the fields of
`LiteralSearchState`; in particular these repeat-permitting response laws do
not assert a no-repeat flag or repair an already invalid prefix alphabet.

Their additive cost is `appendCharge` (length minus fresh writes), not an
unexplained matrix entry. `SharedWasteResponse.appendCharge_potential` gives the exact conversion
to literal length when initial/final occupation are fixed.

`BellmanJointFrontier.union_allocation`, `joint_budget_split`, and
`frontier_dominance` permit joint coverage responsibility and superset
dominance, with boundary compatibility left in the allowed-option hypotheses.
`emitted_three` explicitly includes the retained middle and both seams.

The implemented interval DP instead stores a required fibre prefix and a
literal suffix. Its finite-family merge is safe by a COVERAGE CONTRACT: every
future block must independently cover its assigned fibres, regardless of
incidental seam hits, and repeats remain allowed. This is not equality of
actual occupied sets. **No theorem here proves the native program refines
that contract or that the interval dictionary is globally exhaustive.**

Also, different incidental occupied sets can change fragment/forced-bend
classification later. The native merge is therefore not automatically valid
for optimizing a history-dependent fragment/bend penalty. Its objective is
literal length under mandatory coverage contracts, not such a penalty.

## 6. Exact objectives are not construction rules

For n >= 2 and an actual covering word that starts and ends clean,
`ReducedAlphabetLedger.covering_reduced_ledger` proves

    L = n! + (n-1)! + n - 2 + F + C + R.

F is signed extra clean-run count, C is dirty-continuation count, R is repeated
permutation occurrence count. `CharlieReducedDepthStream` proves the logical
depth trace round trip, not the SPRA byte format. A finite negative control
shows equal Boolean traces can have different literal occupation.

This budget must NOT be confused with the construction-specific Q plus
opening/join overhead. Neither scalar is itself a sufficient state quotient.

## Missing concrete bridge, stated as work rather than implied complete

To kernel-certify the actual Halfar/phase-improved word one still needs to
export and prove: the 120 labelled fibres and partition; the chosen rows and
closed source paths; literal partial-row completion footprints; the completed
trail inventory; the chosen cyclic openings with footprint preservation; and
every realized seam and final length. Alternatively a full literal Lean scan
could certify just the final word, without proving the optimizer.

These are certificate obligations, not evidence that the construction is wrong.
The native corpus checks are strong empirical checks but not substitutes for
the missing Lean application theorem. No minimality or new all-n construction
claim follows from this bundle.
