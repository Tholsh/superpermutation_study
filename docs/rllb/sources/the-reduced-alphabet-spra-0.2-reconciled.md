# The Reduced Alphabet: Encoding Superpermutations by Transport Events

*Reconciled with SPRA 0.2, 21 November 2026. Revision of the original June 2026 manuscript, not a separate construction report.*

## 1. The central idea

Let an order-\(n\) word be \(S=s_1\cdots s_L\) on \(n\) distinct symbols. A superpermutation contains all \(n!\) permutations as length-\(n\) contiguous windows. The raw word displays every appended symbol, but many append operations are dictated by clean rotation. We therefore distinguish **course**, **1-cycle**, **fragmentation**, and **bend** before discussing compression.

The original claim, "encode choices, not deterministic consequences," remains correct. The revision is that our original two-coordinate diagnostic \([d:t]\) was *not* a definition of the current SPRA fields. SPRA 0.2 encodes the amount of clean running **before** each dirty window and the signed backward-copy offset **at** that window. It does not print an intrinsic fragmentation level or a bend type. Fragmentation and bending must be inferred from the literal walk and its course-orbit occupation.

## 2. Clean and dirty windows

With positions numbered from 1, write

\[
W_p=s_{p-n+1}\cdots s_p,\qquad n\le p\le L.
\]

A window is **clean** if all \(n\) letters are distinct, and **dirty** otherwise. Define \(C(S)\), \(D(S)\), and \(R(S)\) as the numbers of clean windows, dirty windows, and clean windows repeating a permutation previously encountered. Then

\[
L-n+1=C(S)+D(S),\qquad C(S)=P(S)+R(S),
\]

where \(P(S)\) is the number of distinct permutations covered. For a validated superpermutation \(P(S)=n!\), hence the exact identity

\[
\boxed{L=(n-1)+n!+R(S)+D(S).}
\tag{1}
\]

Thus dirty windows contribute literal length, but they are not the only source of excess length: clean repetitions contribute too. A dirty **run** is a maximal consecutive sequence of dirty windows; its length is not a fragmentation level.

## 3. Course, course orbit, and a 1-cycle

For a clean window \(w=x_1x_2\cdots x_n\), define the **course operator**

\[
\boxed{c(w)=x_2x_3\cdots x_nx_1.}
\]

A **course** is *one application* of \(c\): one legal one-symbol shift to the unique clean successor of an already clean window. It is an edge, not an entire orbit. The elementary weight-one operator \(\sigma_1\) in canonical-cycle language is this \(c\). The term **1-cycle** here means an orbit of \(\sigma_1\), *not* a length-one cycle in the disjoint-cycle notation for a permutation.

Since all symbols in \(w\) are distinct,

\[
c^n(w)=w,\qquad c^k(w)\ne w\quad(0<k<n).
\]

Consequently the **1-cycle of \(w\)** is

\[
\mathcal O_1(w)=\{w,c(w),c^2(w),\ldots,c^{n-1}(w)\}.
\]

It has exactly \(n\) clean vertices connected by \(n\) course edges, including the closing edge back to \(w\). The \(n!\) permutation windows partition into exactly \((n-1)!\) disjoint 1-cycles. At \(n=7\), the numbers are 5,040 vertices and **720 1-cycles**. Visiting all \(n\) vertices of one 1-cycle takes an initial vertex plus \(n-1\) successive courses; actually taking the \(n\)th course closes the orbit and repeats the starting permutation.

**Discrete course example, \(n=3\).** The literal word `123123` has four windows:

```text
window ending at p:     3    4    5    6
clean window:          123  231  312  123
course transition:       c    c    c
```

The first three windows are the three distinct members of one 1-cycle; the last is the closure. No dirty window occurs. SPRA's `paint-waste -m 3` therefore prints **no** `reduced_alphabet_words` tokens. This is why a 1-cycle cannot be treated as a single Course command: it is constructed by successive course steps.

A 1-cycle is a mathematical orbit, **not necessarily a contiguous segment of the literal superpermutation**. A word may traverse part of it, depart, and revisit the remaining phases later. Its partial occupation is the proper object for discussing fragmentation.

## 4. The *modern* SPRA logical event tuple

The current `tools/paint_waste.cpp` and `tools/reduced_codec.cpp` agree on one logical tuple for **each dirty window**, printed in human-readable form as

\[
\boxed{[d:o],\qquad d=\#\{\text{immediately preceding consecutive clean windows}\},\qquad o=n-(p-q).}
\tag{2}
\]

Here \(p\) is the position of the appended symbol that creates the dirty window, and \(q<p\) is the position of the **nearest previous occurrence** of that same symbol. Thus \(p-q\) is the copy distance, and \(o\) is a signed offset from distance \(n\). The first depth counts *clean windows*, not necessarily the same number of course edges: a run of \(d\) clean windows has \(d-1\) internal course edges. It also is **not** a fragmentation depth.

For instance, at \(n=7\), `[7:1]` means seven clean windows have just preceded a dirty one, and the repeated symbol is copied from six positions back. `[7:2]` means copy distance five. `[0:0]` means a dirty window immediately followed another dirty window, and the new symbol comes from exactly seven positions back. This is possible because the previous window is already dirty. A **literal** `[0:0]` is not an SPRA RLE instruction; the codec uses special **positive-depth**, zero-offset tokens as repeat markers, but `paint-waste` prints uncompressed logical tuples.

The tuple list alone is not a complete literal word. SPRA decoding also needs the initial \(n-1\)-symbol seed and total decoded length (which sets the final clean run). Physical SPRA 0.2 adds mandatory RLE and bit packing; the painted logical pairs do not contain those physical control tokens. Both `-m` painting and the reduced tuple listing work through \(n=9\); above \(n=9\), `paint-waste` provides statistics only.

**Correction to the earlier notation.** The June 2026 draft interpreted an older `[d:t]` trace as a fragmentation/suffix-depth coordinate and a transport-history index, using \(n\) as a neutral value in both. The modern `[depth:offset]` tuple is **not** a relabeling of that object. In particular, modern `[7:1]` is not a distinguished "baseline fragmentation token" for the same reason that old `[7:7]` was. We cannot convert a historical `[7:6][0:8]` report into modern tuples without replaying its *original literal word*. Likewise, an originally proposed small alphabet \(\{0,\ldots,\lceil n/2\rceil-1\}\) is a possible theoretical quotient, not a claim about the set of current SPRA logical pairs.

## 5. Fragmentation: an interrupted 1-cycle

There are two levels that the earlier manuscript inadvertently merged.

1. A **one-window seam** is a dirty run of length one between clean runs. This is a local, directly paintable fact.
2. A **fragmented 1-cycle** is a rotation orbit \(\mathcal O_1(w)\) whose members occur in two or more separated clean runs of a given traversal. This is a global *occupation* fact. Its phase portions are visited at different times, sometimes after substantial transport through other 1-cycles.

A one-window seam may exit a 1-cycle, but it does **not** in itself prove that that orbit is fragmented. Conversely, a fragmented orbit can have portions rejoined through many different local seams. To detect fragmentation formally, assign each clean permutation \(w\) its rotation-orbit key \(\kappa(w)=\min_{0\le j<n}c^j(w)\) (for a fixed alphabet ordering), and count how many disjoint maximal clean runs contain windows with that key. Fragmentation means this count exceeds one.

**Discrete seam example from SPRA's documented test**, with \(n=3\):

```sh
printf '%s\n' '123121321' | ./build/paint-waste -m 3
```

```text
painted word:            12312[1]321
reduced_alphabet_words: [3:1]
length:                 9
clean:                  6
dirty:                  1
valid_superpermutation: 1
```

The windows are `123, 231, 312` (clean), `121` (dirty), then `213, 132, 321` (clean). The printed `[3:1]` says three preceding clean windows, with the dirty `1` copied at distance \(3-1=2\). The local cut changes rotation orbit; no two-window bend is present. This word covers both 1-cycles of \(S_3\), so it is a complete superpermutation.

**Literal re-entry example in Egan's \(n=7\), length-5908 word.** One complete 1-cycle is occupied in separated pieces:

```text
p = 15,16,17,18,19:
2345617 -> 3456172 -> 4561723 -> 5617234 -> 6172345

p = 61,62:
1723456 -> 7234561

closing course: 7234561 -> 2345617
```

All seven windows are rotations of the same cyclic word. The first five consecutive members and final two consecutive members are each linked by courses, but their **occurrences** are separated in the superpermutation. Algebraically they form one 1-cycle; temporally they are fragmented, then repaired. The last arrow is the mathematical closing edge of the orbit and is **not** an assertion that those two occurrences are adjacent in the literal word.

## 6. Bending: extended dirty transport

For this paper a **bend** is a local dirty excursion of at least two windows which enters from a clean window, passes through a connected dirty run, and returns to a clean window, changing the available rotation phase/orbit or its transport frame. The *observable bend candidate* is a dirty run of length \(\ge 2\); to establish its transport interpretation one also examines the literal entry and exit windows. This definition is operational and does **not** claim that every multi-window dirty run is a mathematically indispensable bend or that modern SPRA prints a `bend` opcode.

In the current format, the first dirty window in an excursion has `[d:o]` with \(d\) preceding clean windows. The second and later dirty windows in the same run necessarily have depth zero, because **no** clean window intervened. The run is therefore visible as

\[
[d:o_1][0:o_2]\cdots[0:o_r].
\]

The \(o_i\) are signed backward-copy offsets, not independent bend depth parameters. This local multi-window geometry is **different from** the global question of whether a particular 1-cycle's clean vertices are split across runs. A word may exhibit both kinds of structure.

## 7. Modern SPRA examples: Egan's 5908 versus a 5906 word

The following counts are obtained by applying the documented `paint-waste` logical-window rules to the **literal repository words** listed under Sources. Each word was separately checked for 5,040 distinct clean permutations. These are reproducible *SPRA-format logical diagnostics*, not the old `[d:t]` report. In particular, the 5906 witness is the explicitly identified `nsk...2SYMM_FS.txt` corpus entry, not an assertion about every 5906 witness.

| Property | Egan 5908 | Selected 5906 |
|:--|--:|--:|
| Literal length | 5908 | 5906 |
| Clean windows | 5040 | 5040 |
| Repeated clean permutation windows | 0 | 0 |
| Dirty windows | 862 | 860 |
| Dirty runs | 862 | 837 |
| Maximum dirty-run length | 1 | 2 |
| Two-window dirty runs | 0 | 23 |
| Distinct 1-cycles visited | 720 | 720 |
| 1-cycles split across multiple clean runs | 143 | 116 |
| All permutations covered | yes | yes |

The 5908 word has **only isolated dirty seams**. In the modern SPRA output its full dirty-event histogram is:

```text
[7:1] × 577
[5:1] ×  70
[4:1] ×  72
[3:1] ×  72
[2:1] ×  71
sum       862
```

For example, its first dirty event is at position 14:

```text
p=13: W=7123456   clean
p=14: W=1234561   dirty    [7:1]
p=15: W=2345617   clean
```

At position 14, the appended `1` is copied six places backward, so \(o=7-6=1\). There are seven preceding clean windows. This is one dirty seam, **not** an orbit-depth number 7.

The 5906 word contains some isolated seams, but also exactly 23 two-window dirty excursions. Its first bend has this literal window trace:

```text
p=53: W=7612345   clean
p=54: W=6123451   dirty    [7:2]
p=55: W=1234516   dirty    [0:0]
p=56: W=2345167   clean
p=57: W=3451672   clean  (one Course after p=56)
```

The first append copies `1` from distance five, so \(o_1=2\). The next append copies `6` from distance seven, so \(o_2=0\), but this **does not make that window clean**: `1234516` still repeats `1`. The clean exit is `2345167`, which belongs to a different rotation orbit from the clean entry `7612345`. In the literal painted string the two dirty symbols appear adjacent as `[1][6]`. This is an explicit nontrivial two-window bend, not two independent one-window fragmentations.

The 5906 word's logical tuple histogram is:

```text
[7:1] × 584     [7:2] × 19     [0:0] × 23
[5:1] ×  51     [5:2] ×  1
[4:1] ×  62     [3:2] ×  3
[3:1] ×  61     [2:1] × 56
sum 860 dirty windows = 837 runs + 23 additional dirty windows
```

The two-symbol length difference follows **exactly** from equation (1): both words cover all 5,040 permutations without clean repeats, but their dirty counts are 862 and 860. This fact does not by itself prove that introducing bends always saves symbols; that would require an optimization or exchange theorem on the allowed entry/exit frames.

## 8. An excursion longer than two windows

Bends need not have length two. The repository's ordinary recursive \(n=5\), length-153 superpermutation gives:

```text
p=77: W=54312  clean
p=78: W=43121  dirty   [5:3]
p=79: W=31213  dirty   [0:1]
p=80: W=12134  dirty   [0:-1]
p=81: W=21345  clean
```

The three dirty symbols print in `paint-waste -m 5` as `[1][3][4]` in the corresponding segment. The offsets correspond to nearest copy distances 2, 4, and 6 respectively, since \(o=5-\text{distance}\). A negative offset therefore has an ordinary interpretation: its copy source is **farther** than \(n\) letters back, not an inverse fragmentation level. The full word has 120 clean windows, 29 dirty windows in 23 runs, longest dirty run 3, and covers all 120 permutations.

## 9. Phase, transport, and the original bending argument

The older distinction is still mathematically useful after we remove the false coordinate equivalence. A 1-cycle \(\mathcal O_1(w)\) comes with a **phase** \(j\in\mathbb Z/n\mathbb Z\), the current rotation index; a course increments this phase modulo \(n\). The orbit identifier \(\kappa(w)\) specifies *which* 1-cycle we occupy. Dirty excursions change the accessible clean orbit and entry phase; a bend can compose more than one dirty step before the next clean vertex appears.

A useful transport-state abstraction is

\[
(\kappa,j)\xrightarrow{\ c\ }(\kappa,j+1\bmod n),
\]

with each dirty excursion represented as an edge from its **last clean** state to its **first subsequent clean** state, carrying an integer dirty-window cost. It may be annotated with SPRA's observed copy-offset sequence. A seam is an excursion of cost 1; a multi-window bend has cost \(r\ge2\). Whether a transport edge has nontrivial holonomy is a property of the endpoint frames and their composition, not merely of the numerical value of the first tuple.

A fragmentation is then a property of the *occupation trace* on the same graph: phases of one orbit are distributed over multiple clean-run visits. The two concepts coexist without contradiction. Bending offers additional transports between ports, while fragmentation determines how and when the compulsory vertices of a 1-cycle are paid for. This is the correct modern reading of the older assertion that 5906 can use a richer grammar than Egan 5908.

The reported split-cycle counts above illustrate the distinction: Egan's witness has 143 1-cycles visited in multiple clean runs, despite having **zero** multi-window bends; the selected 5906 witness has 116 such split orbits and **23** two-window bends. It is therefore incorrect to identify "fragmentation" with "depth positive" in SPRA or "bending" with "offset nonzero." These are measurements on different levels of the traversal.

## 10. Event reconstruction and reproducibility

For a literal word, the following reconstruction suffices to repeat the present examples and distinguish all the objects in this paper:

1. Scan all length-\(n\) windows, recording whether each is clean or dirty and ranking each clean permutation.
2. Group clean permutations by the canonical rotation-orbit key \(\kappa\); for each orbit record the clean-run IDs and phase positions of all occurrences. More than one run ID is a fragmented 1-cycle.
3. Partition dirty windows into maximal runs. Emit one logical SPRA `[depth:offset]` pair for each dirty window using equation (2); a run of \(r\) windows is a cost-\(r\) excursion.
4. Inspect the last clean entry and first clean exit of each dirty run. Verify whether a multi-window run really changes the orbit/phase frame, rather than interpreting its tuple values as preassigned operation names.
5. Independently verify coverage \(P(S)=n!\), counts of clean repetitions, and equation (1).

To reproduce the human-readable format from the SPRA repository:

```sh
mkdir -p build
g++ -std=c++20 -O2 tools/paint_waste.cpp -o build/paint-waste
./build/paint-waste -m 3 <<< '123121321'
./build/paint-waste -m 7 < words/7/5908/5908-egan.txt
./build/paint-waste -m 7 < words/7/5906/7_5906/7_5906_nsk666366466646646664663666_2SYMM_FS.txt
./build/paint-waste -m 5 < words/5/153/153-recursive.txt
```

`-s` suppresses the event pairs and printed word, leaving coverage statistics. The machine-readable pair stream below `reduced_alphabet_words:` is decimal with signed offsets. The short snippets above list actual logical pairs as recomputed from the repository's literal words by the same depth/nearest-prior-copy rules; the C++ executable itself was not run while preparing this revision.

## 11. Historical 200-symbol trace and notation boundary

The original manuscript included a separate \(n=7\), 200-symbol fragment with 166 clean and 28 dirty windows, and an older event report whose sample tokens included `[7:7]`, `[5:7]`, `[2:7]`, `[4:7]`, and the repeated pattern `[7:6][0:8]`. These old labels are useful evidence of the original **hypothesis** that ordinary fragmentation and displaced bend transport played different roles. They are **not** SPRA 0.2 outputs. In particular, a historical token `[7:7]` must not be assigned modern copy distance zero or interpreted as a dirty window copied from position \(p\). The raw 200-symbol word and original reporting implementation would be needed for a faithful conversion. The verified examples in Sections 5–8 instead use the current repository's literal witnesses and the precise modern tuple definitions.

## 12. What the two-symbol difference proves—and does not prove

The observation that the 5906 superpermutation uses two-window bends whereas the Egan 5908 word uses only isolated seams **survives**, with much clearer definitions. The stronger claim that a nonneutral transport index *alone* proves a bend does **not** survive. Nor do the old claims that a particular first coordinate measures fragmentation depth or that the raw `[d:t]` traces can be compared directly with SPRA 0.2.

Equation (1) explains the literal length difference after validation. The course-orbit partition explains the compulsory clean occupation. The bend/fragmentation split describes how the construction arranges that occupation. A possible future optimization theorem would compare alternative collections of transport edges and phase-port matchings **while holding the obligation to visit every orbit phase fixed**. Such a theorem would need to account for repeated clean windows and globally split orbits, not only local dirty-run costs.

## 13. Working principle

\[
\boxed{\text{A Course is one clean edge; a 1-cycle is an orbit of successive Courses.}}
\]

\[
\boxed{\text{Fragmentation splits the occupation of that orbit; bending transports between its clean pieces.}}
\]

The reduced word is a state-dependent transport description. Its cheap part—the clean evolution—is deterministic once the phase and course orbit are known. The expensive part is the choice and placement of excursions, along with the obligation to complete missing course phases. The modern SPRA tuple stream makes the literal cost of dirty windows observable; the course-orbit quotient makes the unfulfilled occupation observable. Neither replaces the other.

### Sources and provenance

- Original June 2026 manuscript: *The Reduced Alphabet: Encoding Superpermutations by Transport Events* (user's Library file `the-reduced-alphabet.md`). The previous `[d:t]` trace is retained as historical context, not used to prove current SPRA tuple semantics.
- [SPRA 0.2 paint-waste guide](https://github.com/Tholsh/SPRA/blob/main/docs/paint_waste.md), [SPRA binary/logical tuple specification](https://github.com/Tholsh/SPRA/blob/main/docs/spra.md), and [paint_waste.cpp](https://github.com/Tholsh/SPRA/blob/main/tools/paint_waste.cpp), read 21 November 2026.
- [Egan 5908 corpus word](https://github.com/Tholsh/SPRA/blob/main/words/7/5908/5908-egan.txt), blob `f3b3ef371448af6e7ae6b54cb86b3db7d402f400`.
- [Selected 5906 corpus word](https://github.com/Tholsh/SPRA/blob/main/words/7/5906/7_5906/7_5906_nsk666366466646646664663666_2SYMM_FS.txt), blob `638fd5db6bb131c1329c4047ed57d85c998ffd2e`.
- [Recursive order-5 corpus word](https://github.com/Tholsh/SPRA/blob/main/words/5/153/153-recursive.txt), blob `9b643d51d7f17ad5a42432ea420f984ce774a08b`.
