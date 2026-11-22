# n=13: 48-hybrid selection, mask/phase screening round 2

2026-11-22. **Selection-stage certificate. No record-beating literal word is claimed.**

## Construction

Starting from the archived complete n=13 48-hybrid selection (mask 38 in each residual (7,4) fiber), enumerate the 56 minimum-floor packet variants from the 8 independent Step1-to-N balanced exchange circuits (1 circuit of 161 classes and 7 of 14). Each local variant is a **complete valid (7,4) packet** with Q=2443, D=406, five active walks, 20 active completion trails, and T=426. Each includes the n=11 A-like (7,3) port monodromy on one of its walks. Each variant's uncompressed 5040-row packet and completed 57883 slice-port graph were independently regenerated.

For every variant, compute (i) the relaxed maximum directed matching of 9-, 8-, and 7-symbol port overlaps across the local trails, (ii) the restricted phase-coupled trie dual, (iii) a phase-consistent, cycle-free greedy path cover with restart seeds, and (iv) 8/9-overlap opportunities against the fixed global core for each of the 48 fiber positions. The trial path cover is an **achievable subset of links in a local packet** but is NOT a full word, a rigorous lower bound on its joining cost, or a proof of optimal mask choice.

All 56 variants have exactly the same relaxed matchings (413 of 426 at depth 9; 426 at depth 8; 426 at depth 7), the same arc counts (1581 at depth 9), and the same local restricted dual value. On the 48 fiber-core boundaries, depth-8/9 interface **counts** are also invariant across these masks; mask differences can still affect coupled phases and specific joining paths.

For local greedy path-cover screening with 3500 restarts, mask 186 scored a total 2348 overlap symbols (252 9-overlap links and 10 8-overlap links), versus 2328 for mask 38 in the same trial. A separate 12000-restart run under another seed scored 2332 versus 2325. These results are heuristic, vary with seed, and do not establish a proven completion advantage. Mask 186 was chosen as a promising follow-up candidate; it is not certified optimal.

The new **mask186 × 48** selection differs in 2688 native row assignments from the mask38 × 48 control (56 changes per fiber). The linked compiler generated the full 3,628,800-class native selection from the existing verified full selection by only making these local balanced exchanges.

## Full selection certification

| Metric | Value |
|---|---:|
| Native classes | 3,628,800, each once |
| Native row balance defects | 0 |
| Charge Q | 1,812,288 |
| Detached classes D | 19,488 |
| Active row walks | 1,032 |
| Active completion trails | 8,676 |
| Total completed trails T | 28,164 |
| Completed slices | 41,729,088 |
| Native cyclic length | 6,747,751,488 |
| Completed degree-13 cyclic classes | 479,001,600 distinct |
| Missing / repeated classes | 0 / 0 |
| SHA-256 of uncompressed selection | 625578681003f29bd4fe5ef02156b0293fe973115f6beef2d018544b350ddd0d |

The C++ `verify_generic_selection` recomputed the native row-transition/port-monodromy counts; `generate_trails_generic` built the entire completed slice/end-point graph and verified its balance; `check_classes` independently checked the complete 479,001,600-class factorial bitmap.

## Selection gate and global overlap screening

For the one-intact-weight-3-cut-per-trail model,

    F3(13) = 13! + 12! + 11! = 6,745,939,200
    L >= F3 + Q + T + 9 = 6,747,779,661.

This necessary structural floor is **20,494 below the cited 6,747,800,155 comparison word**. The n=12-style global phase-coupled connector-trie relaxation over all 41,729,088 cut states returned a conservative length lower bound 6,747,779,651, ten below (thus weaker than) the simple bound. It therefore **did not reject** mask186, but it did NOT establish that the required overlaps are globally realizable in one word. Weight-2 cuts, trail splitting, redundant clean windows and other unrestricted operations are outside this gate.

The native structural value Q+T is unchanged from mask38 × 48. The only reason to prefer mask186 for the next experiment is its *local heuristic phase-compatible path cover*; the global resulting word could be better, equal, or worse. Full connection-aware selection/placement remains necessary.

## Reproduce

This ZIP bundles the full selected native `.selection.xz`, the prior mask38 control `.selection.xz`, mask186 local packet, the original Step1 block and exact Step1->N 259-choice encoding, 48-fiber map, generation scripts, and independent C++ validators. The small 56-variant rank tables and per-fiber 8/9-core overlap metrics are included. The ~400MB full `heads.bin`/`slices.bin` intermediates are omitted but regenerable.

From a directory with the listed source files and both selections uncompressed:

    g++ -O3 -std=c++20 -pthread verify_generic_selection.cpp -o verify_native
    ./verify_native n13_kernel_mask186_48.selection
    g++ -O3 -std=c++20 -pthread generate_trails_generic.cpp -o generate
    ./generate n13_kernel_mask186_48.selection n13_kernel_mask186_48
    g++ -O3 -std=c++20 -pthread check_classes.cpp -o audit
    ./audit n13_kernel_mask186_48.slices.bin
    g++ -O3 -std=c++20 -pthread direct_kraft_screen.cpp -o trie
    ./trie n13_kernel_mask186_48 12 .04

Run `build_mask186_48.py` inside `/mnt/data/n13_work` layout to reconstruct the chosen native selection from the provided mask38 control, mask186 local packet and fiber map.
