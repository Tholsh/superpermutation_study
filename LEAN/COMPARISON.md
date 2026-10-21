# Why our selection lags the published Halfar selection

The comparison is with the pinned n=8 construction README in
`evidence/halfar-n8-pinned-README.md`, not a claim about Jakub's private
understanding or his latest unpublished code.

## His construction exposes the right tradeoff

At n=8, K=6 and endpoint width h=5. Halfar's ordinary source system has 120
cyclic orders of the six ordinary symbols. His search packs low-cost closed
walk types over these loops and refines the selection with parallel tempering.
The README says an integer program optimizes the trail order and joins for
each selection. Thus he already understands that selection and attachment
cost interact; we have not discovered that fact on his behalf.

The selected four 27-loop walks each have Q=16 and one completed trail. Twelve
loops are detached. He reports a unique four-copy packing up to symmetry and
a Klein-four action. These structural packing statements are his results;
this bundle does not independently prove them.

The published ledger is `L=46085+Q+J`: his selection has Q=64, J=25. His README
also explains why a restriction to joins of overlap >=3 concealed it earlier.
Those are two specific selection/attachment freedoms that matter in practice.

## What we actually changed, and why there is no contradiction

Our saved 46,173 phase plan keeps his rows and all sixteen whole trails.
Three large-trail openings use a shorter wrap (g=2 rather than g=3). In the
same bookkeeping the length is

    46085 + Q + A + J = 46085 + 64 + 3 + 21 = 46173.

A is the extra opening length relative to the common h=5 ledger, and J is
the residual seam bill. The parent's A+J was 0+25; ours is 3+21=24.
Paying three symbols inside pieces buys four symbols at joins.

This does not refute his declared optimum for a fixed set of whole pieces:
the admissible opened pieces can differ. Nor does a parent with g=3 prove
that his search “forgot phase.” We have not audited the exact IP's complete
opening-variable domain. Its whole-piece optimum and our expanded opening
experiment must not be silently identified.

## Why the new joint DP did not supply a better selection

Our DP admits original closed blocks, detached alternatives, and single
closed source walks on contiguous intervals of a fibre order inherited from
his control. It jointly minimizes rows, internal order and boundary phase
inside that family. The complete interval-through-27 run covered 434 options
and 903 cyclic models; it retained the original rows at length 46,173.

That is much narrower than freely packing compatible low-cost walks across
all 120 fibres. We still exclude noncontiguous row walks, cross-option trail
interleaving, cross-interval source edges, near-full rows, and original
templates with several completed trails per source walk. The DP is an exact
local-family solver, not a replacement for his selection discovery process.

The forced-change controls prove rows were not merely frozen:

| Native candidate | Q | Opening/join overhead | Length |
|---|---:|---:|---:|
| Original rows, phase optimized | 64 | 24 | 46173 |
| Changed rows, shallow dictionary | 48 | 64 | 46197 |
| Changed rows, partial larger dictionary | 64 | 32 | 46181 |
| Changed rows, complete interval <=27 | 70 | 24 | 46179 |

The Q=48 selection loses badly at its boundaries. The Q=70 selection beats
the Q=64 changed-row example by two despite paying six more row symbols.
Charge alone does not select a good construction. The native result files
and detailed limitations are retained in `evidence/`; no non-result is called
a global obstruction.

Nor does an abstract return-port permutation by itself specify every literal
join. Actual endpoint labels and valid openings are still needed. Our native
DP retains the n-1-symbol suffix for this reason; it does not derive a cheap
global attachment schedule from the smaller n-3-port map alone.

## What the Lean adds to this discussion

The useful formal contribution is a reusable specification/certification
layer: literal occupation, ordered port composition, conditional balance,
stateful response composition, exact cost/coverage replacement, and clear
distinctions between fresh, repeated and dirty writes. It permits changes
that preserve JOINT coverage rather than requiring per-piece ownership.

This is compatible with Halfar's construction, not demonstrated to be a
strictly more powerful selection theory. Fourier or superoperator language
does not by itself produce the missing walk packing, remove occupation, or
prove cheapness. The literal realization and native-code refinement gaps
are enumerated in `CLAIMS.md` rather than concealed by terminology.

The most useful next collaboration is to connect his concrete row/packing
certificate to these literal interfaces, while sharing exact domains for
the selection and opening optimizers. Until that is done, say “generic
validation lemmas plus native witnesses,” not “Lean proved the new word.”
