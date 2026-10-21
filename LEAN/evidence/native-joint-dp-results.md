# Actual coupled row-selection / boundary-phase DP

2026-10-20. The existing `tools/row_selection/selection.cpp` was upgraded
with a separate `--joint-dp` mode in `joint_dp.h`. This is not another
fixed-row recut or a proxy-selector/assembler handoff.

## Recurrence and what stays live

The DP state is `(covered fibre prefix, literal suffix, row-change flag)`.
An outgoing construction option selects the rows of a fibre interval,
compiles their complete trails, and jointly chooses the opening phases
and internal trail order with the incoming literal boundary. The next
prefix is reached at the actual spelled length, subtracting literal joins.
Q is already present in those literal lengths. It is not optimized first.

Every option's complete required fibre footprint and cyclic length ledger
are checked before insertion. All options for the same interval cover the
same required permutation set, so merging equal suffix states at its end
does not discard a distinct future occupation obligation in this family.
The flag is retained separately when a changed-row control requires it.

The dictionary includes original closed row blocks, a detached alternative
for every fibre (including originally occupied fibres), and all enumerated
single closed source walks covering a contiguous fibre interval. All starting
rotations and ordinary row lengths are offered. Multi-trail completions of
one option use their own exact subset/order/phase DP before returning to the
outer DP. Neither higher Q nor a larger trail count automatically rejects
an option; endpoint-dependent costs are retained.

## Complete first neighborhood

Final binary: `selection-joint-v5.exe`; source snapshot: `source-v5/`.
Control template: the original `n8-46173.plan` on `probe27-control-v1/base.txt`.

The run `v5-complete-27` enumerated the entire declared interval dictionary
through interval size 27 in this particular fibre ordering:

- 120 source fibres; 434 construction options; 903 cached cyclic models.
- 18,174,309 source-enumeration nodes; no dictionary limit hit.
- 7,476,934 phase queries; peak outer layer 18,130 boundary/change states.
- 6,495,978 traceback nodes.
- 8.58 seconds total, one native CPU process; no GPU.
- Best length **46,173**, Q=64, original rows retained.

The dictionary includes baseline long blocks even in the smaller interval
tests. A final output using unchanged rows does not mean rows were frozen:
the forced-change controls below require different rows in their traceback.

## Controls and counterfactual row selections

| Case | Length | Q | Opening/join overhead | Changed rows |
|---|---:|---:|---:|---:|
| Published order, frozen rows / full phase DP | 46,174 | 64 | 25 | 0 |
| Our order, frozen rows / full phase DP | 46,173 | 64 | 24 | 0 |
| Joint interval dictionary through 8 | 46,173 | 64 | 24 | 0 |
| Require changed rows, interval dictionary through 8 | 46,197 | 48 | 64 | 18 |
| Require changed rows, retained partial dictionary through part of 23 | 46,181 | 64 | 32 | 4 |
| Require changed rows, complete interval dictionary through 27 | 46,179 | 70 | 24 | 7 |
| Joint complete interval dictionary through 27 | 46,173 | 64 | 24 | 0 |

Here `L = 46,085 + Q + overhead`. The Q=48 choice is substantially worse
after attachment is charged. The Q=64/four-row counterfactual has the same
row-length histogram as the control, but its completion has 21 trails,
versus 16: ordered connectivity, not histogram or charge alone, changes.
The Q=70 counterfactual is two characters shorter than that Q=64 one,
despite paying six extra row characters. These are concrete examples of
why row choices must be compared using their boundary responses.

They do not establish a universal penalty formula or an improvement below
46,173. The dictionary offers many possibilities; the best changed-row
path remains longer than the unchanged control in this family.

## Verification

- 10,000 bucket queries compared against dense min-plus transitions.
- Positive engine control: a locally longer response wins after its join.
- Internal multi-trail order DP and row-change state separation controls pass.
- Frozen-row/forced-change negative control returns exit 2 and writes no word.
- A one-node dictionary guard reports incomplete enumeration, not optimality
  over the requested larger dictionary; its retained-family word is verified.
- Old HiGHS mode regression: frozen Q64/D12 selection admitted, four port
  cycles and objective 80, unchanged by adding the new mode.
- Every completed reported word passed both existing independent whole-word
  scanners; all 40,320 permutations occur. Single-deletion scans also ran.
- The existing independent partial-row auditor accepted all reported selected
  row sets, including the changed-row outputs, checking source flow, the
  literal endpoint graph, cyclic-class coverage, and ordered port cycles.
- Halfar's independent `geng.py` regenerated the changed-row bases, including
  the seven-row Q70 case. Source/port/literal completion counts agree.
- Final v5 and v4 complete-27 outputs agree byte-for-byte.

The new 46,173 phase traceback has 40,377 clean occurrences (57 repeats),
not 40,376 as in our earlier saved 46,173. Its SHA-256 including LF is
`ad2ed178710e2d39b7589715cff38d308b0d79e1a70ceb80254a6a2b6f6837a5`.
No novelty up to relabeling/reversal is claimed for this tied spelling.

## Exact scope, not global minimality

The fibre order is inherited from a control template. New source walks must
cover contiguous intervals in that order; arbitrary noncontiguous walks are
not enumerated, and completed trails of different options cannot interleave.
Near-full rows K-1 are unsupported. These are construction-family restrictions,
not laws of all superpermutations. The native implementation is not a completed
Lean reflection proof.

The earlier `interval-31` runs with a two-million-node guard, and the wider
twenty-million-node 31 run, retained partial dictionaries. Their result files
correctly mark that truncation. The complete-27 run was specifically added
to finish a precisely stated dictionary rather than imply a larger search
was exhausted.

There is now a working **joint** DP for this finite family, but no new shorter
word or unrestricted row-selection optimum. No original corpus word, current
LaTeX source, or healthy search worker was overwritten. No Git, SSH, GPU,
automation, or external publication was used. All native runs have finished.

See `tools/row_selection/JOINT-DP.md` for build/CLI details, `panel-v3.json`,
`final-verification.json`, per-case `options.tsv` and `arguments.tsv`, and the
two independent row-audit JSONL files for receipts. A compile error from the
first build was repaired; its log is retained rather than hidden.
