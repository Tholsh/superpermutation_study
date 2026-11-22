# Notes for your chat: what I have worked on over the last few days

Jakub, 21 Nov 2026. You share your chat logs with me and they keep moving my work forward, so here is the same thing in the other direction: what I did, what came out of it, the numbers, and where I am stuck. Maybe something here moves your side forward too.

## 1. The model and the words I use

Everything below works inside Jay Pantone's construction. A selection of slices on the 2-loops is computed at a small alphabet size and transported up to n - 1 symbols. The last letter completes it into closed trails on n symbols. The closed trails are then cut, joined (connector cycles, overlaps) and ordered into one word. I split the work into two layers and attack them separately.

| term | meaning here |
|---|---|
| K | n - 2, the number of letters in a 2-loop of the selection |
| slice | Pantone's S(x, s; L): the first L cyclic classes of the 2-loop of (x, s); full = the whole 2-loop, short = one class less |
| selection | which slice (full, short, other length or none) every 2-loop gets; it fixes the charge Q, the 2-loops without a slice and the closed trails |
| transport | Jay's map that carries a selection from K to K + 1 |
| arrangement | how the closed trails are cut open, joined and ordered into one word |
| floor | Q + the 2-loops without a slice + the number of closed trails, in units of (n - 3)!: the selection's price before any arrangement |
| walk | a closed walk of slices in the selection; small walks give small closed trails |
| fiber block | the 2-loops above one 2-loop left without a slice (your and Jay's blocks) |
| core | a large literal stretch outside the fiber blocks |
| square flip | Jay's local change of a selection (section 5.2) |

## 2. Records now (Almanac) and where each comes from

| n | length | id | by | how |
|---|---:|---|---|---|
| 8 | 46,173 | W-0078 | you | my 16 closed trails in a new order with new openings |
| 9 | 408,717 | W-0103 | me | Jay's W-0099 construction with another choice of the four square flips |
| 10 | 4,034,855 | W-0062 | me | rumstd's word structure on a new selection with 350 closed trails instead of 364 |
| 11 | 43,930,517 | W-0133 | Jay | from your construction: 48 fibers + 2 cores, Hamiltonian paths inside fibers, Euler-flow order model |
| 12 | 522,736,409 | W-0128 | Jay | my selection E, his constant-temperature searches with five-cut segment insertion |
| 13 | 6,747,791,494 | W-0129 | Jay | my selection N with a better (7,4) block that Jay found by running my block search further, then rounds with equal moves |
| 14 | 93,904,739,772 | W-0135 | me | Jay's W-0127, reordered with his move from W-0107 over chains and zones, then 74 redundant letters removed |

The current records at n = 12, 13 and 14 all sit on my selections; Jay's gains there came from the arrangement and from blocks. At n = 11 the last three records came from your fiber-block construction.

The n = 11 race of 20-21 Nov, for the record:

| word | length | from |
|---|---:|---|
| your W-0131 | 43,930,529 | Kraft-scored (7,2) packet |
| your W-0132 | 43,930,527 | same line |
| our joint word (not on the Almanac) | 43,930,520 | your block method widened with block templates from about 50 other n = 11 words, all 24 permutations of the new letters, reversal, re-cut variants |
| Jay's W-0133 | 43,930,517 | Euler-flow order + Hamiltonian paths inside fibers |

## 3. n = 11: the order is tight, the room is elsewhere

I took W-0133 and wrote its ordering problem as exact integer programmes (flow and path-cover models with subtour cuts) over its closed trails. A trail may be cut open at other weight-3 steps ("openings") and placed anywhere, as one segment or split into several with other trails inside. "Delta D" keeps the openings whose cheapest possible joins are within D letters of the trail's best.

| family | size | result |
|---|---:|---|
| weight-4 pieces, any order | 1,159 pieces | optimal 43,930,517 (two programs) |
| one segment per trail, delta 0 | 22,465 openings | optimal 43,930,517 |
| one segment, delta 1 for every trail | 52,739 | optimal 43,930,517 |
| one segment, delta 2 for every trail | 91,476 | optimal 43,930,517 |
| one segment, all 24,881 openings of the 1,108 small trails | 45,262 | optimal 43,930,517 |
| several segments, delta 0 | 22,465 pieces | optimal 43,930,517 (two programs) |
| several segments, delta 1 for the small trails | 25,736 | optimal 43,930,517 |
| several segments, delta 2 for the small trails | 32,937 | open: bound 43,930,461, no better order found |
| block 1 cut at every weight-2 step | 6,183 pieces | open: bound 43,930,507, no better order found |

"Optimal" means Gurobi closed the model with no gap. The same models give exactly 4,034,873 on rumstd's n = 10 word, as they should.

Second test: one fiber block of W-0133 at a time is freed and may be replaced by any of the 336 relabellings of any block word of 61,051 letters (7 classes; W-0133 uses three of them, 18 + 19 + 11 blocks), with every trail opened and placed anywhere. All 14 sub-runs closed: no relabelling of any class gives a shorter word. The 541 longer block shapes (61,052 letters and up) were not run, since each costs at least one letter.

Third test: an exact frame DP over regions of up to 60 2-loops says the published n = 11 selection is optimal in all 11 regions of 50-60 2-loops I tried.

So going below 517 needs a different selection, or blocks that cost more letters inside but join much better. A better order will not get there.

## 4. n = 10: real prices of a selection

I built words from many candidate selections with an arrangement optimiser that starts from the base word alone. It returns 4,034,855 on the selection in use on three seeds out of three, so it is fair. From the built words, in letters:

| part of the word | cost |
|---|---:|
| complete orbit of seven small closed trails | about 10.0 (a run of 6 + a join of 4) |
| big closed trail | about 1.15 |
| group of 2 or 3 small trails that is not a whole orbit | about 7 |

The selection in use has 48 complete orbits and 14 big trails. Every other candidate with the same structure gave exactly 855; the others were 3 to 150 letters longer. A selection with 48 complete orbits and only 3 big trails would give about 4,034,842, 13 below the record. I do not know whether one exists.

Lower side: a flow model over 18 block shapes (26,213 states) has a proved bound of 4,034,850, so inside that model the record is at most 5 letters from optimal. New runs with stronger cuts stalled at 4,034,829, so the 850 bound came from a lucky branching order and needs better cuts to reproduce.

## 5. Selections: where I think the room is

### 5.1 What does not work, with reasons

| idea | result | status |
|---|---|---|
| perfect treble design: one plain treble course covering every 2-loop once | impossible at K = 9, 11, 13, 15 (certificate) | proved |
| packings of plain treble courses | 80 % at K = 7 (optimal), about 30 % found at K = 9 and 11, far from break-even | computed |
| LP bound over closed walks (Dantzig-Wolfe, column generation) | equals N x (best cost per 2-loop of one walk), so it cannot bound selections | proved |
| selections invariant under letter-fixing groups | K = 8: AGL(1,7) and PSL(2,7) make the floor worse; K = 9: the empty selection is optimal for AGL(3,2), PSL(2,7), AGL(1,8) | computed (exact) |
| grammatical evolution of selection rules (after M. Slazynski's work on Noodle) | transport is an isolated optimum among the rules found; no rule predicts a gain | computed, not exhaustive |
| fresh selections from scratch with an annealer on the card | no build beat the selection in use so far | computed, still running |

### 5.2 A move that keeps a selection closed

Jay's square flip, written as a 2-exchange of successors. Two slices A1 -> T1 and A2 -> T2 swap targets. A1 gets the out-letter x with hop(A1, x) = T2, and A2 the y with hop(A2, y) = T1. T1 and T2 change their mobile letter but keep their out-letters, so their successors stay. A2 is forced (it is the predecessor of T2), the selection stays closed by construction, and exchanges on disjoint walks commute.

The n = 10 selection behind W-0062 is exactly Jay's transport plus 8 walk-disjoint exchanges of this kind. At K = 8 the transport has 336 disjoint candidate places, at K = 9 1,680.

### 5.3 Toward your "liftable algorithm"

A short uniform rule reproduces the walk structure that was found level by level (by an exact search at each level, and by Jay at K = 9): transport, then two exchange passes at every level.

1. Exchange where the anchor slice is short and the newest letter T1 stands 3 places before the letter just before T2.
2. Exchange where the parent slice is short and T1 stands K - 2 places after the anchor's out-letter.

| level | selection | walks | closed trails |
|---|---|---:|---:|
| K = 8 | rule (pass 1) = the selection in use | 2 | 14 |
| K = 9 | rule (passes 1 + 2) = Jay's K = 9 count | 14 | 112 |
| K = 10 | transport of Jay's base, no exchanges | 224 | 2,016 |
| K = 10 | the rule applied at every level | 124 | 1,116 |
| K = 10 | exchanges once at K = 8, then plain transport twice | 112 | 1,008 |

So the rule lifts cleanly for two levels and then loses to plain transport. I scanned all single conditions of this form; pairs of conditions and non-greedy choices of the exchange places are not tried yet. Each walk joined at K = 10 saves 9 closed trails, and K = 10 is the part of the n = 12 selection outside the blocks.

## 6. n = 13 and n = 14 now

n = 13: I replay Jay's W-0129 recipe from his block. Polishing W-0129 itself gave nothing (reordering 6 lines x 3 h, kicks, about 20 segment-insertion passes): he ran these moves until they stopped.

| start | start plan | now |
|---|---:|---:|
| Jay, W-0129 | 6,747,792,540 | 6,747,791,494 |
| me, same block | 6,747,792,471 | 6,747,791,504 (10 above) |

n = 14: W-0135 above. The reordering keeps finding shorter orders; the next run starts from W-0135 tonight.

## 7. Asymptotics

| bound | exponent of the error term after n! + (n-1)! + (n-2)! + 2(n-4)! | valid for | status |
|---|---|---|---|
| L-0031 | n^(-1/32) | n >= 8.4e39 | submitted |
| new | 183 (n-4)! (ln n)^(3/29) n^(-1/29) | n >= 1.006e39 | proved in Lean, about to be submitted |
| new, clean power | 180 (n-4)! n^(-1/30) | n >= 1.51e39 | proved in Lean |

The gain comes from a sharper count in Jay's packing step: target frames are sorted, so most witnesses give the same target, and the degree drops from 64 r^8 to 192 r^7. Each power of r is worth 3 in the exponent. Getting to 1/16 would need a packing theorem of degree about r^3 that survives the repairs.

## 8. Tools

One C++ codebase now replaces most of my C tools. It writes the same words and plans byte for byte, checked on golden runs at n = 10-13.

| step | before | now |
|---|---|---|
| n = 13 render (write the word of a plan) | 294 s, 8.1 GB | 253 s, 2.0 GB |
| cut -> loop -> render chain at n = 13 | 843 s in three programs | 468 s in one process |
| rank kernel (Lehmer codes), batched + prefetched + AVX-512 | 29-35 s | 4.3-4.9 s |
| closed-trail search | 1x | 3.4-3.6x faster, same output |
| segment insertion | CPU | CUDA backend with equal moves |
| ordering (subtour LP) | LKH-3, EAX tried | LP is exact and fastest up to about 55,000 pieces |

The new pipeline is still being built: it reads any word, rebuilds its structure (selection, blocks, trails), runs every move as a step in one process with pause and resume, and checks coverage in a single pass.

## 9. What is running now, and what is parked with a date

Selection lines that are running tonight (ideas, not results yet):

| line | idea | first numbers |
|---|---|---|
| selections from the back | like the n = 7 lower-bound work: write the built length as F3(n) + Q + price x (2-loops without a slice) + price x trails + constant, let a target length fix the budget, look for lower bounds on c1 x shorts + c2 x empty 2-loops that hold for every selection, then build only what still fits | model written, runs in progress |
| nuclei | start from a selection invariant under a letter-fixing group, solve it exactly on the orbit quotient, then free search around it with the fitted prices | K = 8: PSL(2,7) exact floor 2,898 but 171.6 above the selection in use at fitted prices; PGL(2,5) 3,064 |
| annealer on the card | replica exchange over selections, moves: re-route, merge / split walks, create, delete, flip a forced alternating chain; optional symmetric mode | running at K = 7-9, nothing better built yet |
| both layers exact at n = 7-9 | selection and arrangement solved together at permutation level | n = 7: the construction gives 5,907, one local rewrite (repair 2-cycles of one 2-loop hung inside split 1-cycles of an inserted slice) gives 5,906, 5,905 not reached; n = 8: your 46,173 is locally optimal, every one of the 120 fibers and every adjacent pair tested rewritten with all slices free gives 46,173 again |
| n = 11 blocks x openings | longer block shapes (61,052 letters and up) joined with free openings | running |
| n = 13 block search | the (7,4) block search 4x longer and with equal-price moves, on Jay's block and on another one | running, no gain in the first rounds |

Parked items, each with a trigger and a date (so nothing waits forever):

| item | why it is open | what would decide it | by |
|---|---|---|---|
| exchanges at one level K = 10 (the n = 12 part outside the blocks) | scan written, not run | 3 greedy passes; a walk joined saves 9 trails | 24 Nov |
| pairs of exchange conditions, non-greedy choice | only single conditions scanned | the same scan with conjunctions | 26 Nov |
| n = 10 exact bound 850 vs 855 | new runs stalled at 829 | exact max-flow cuts inside the LP + symmetry breaking for relabelled states | 26 Nov |
| W-0129 with 600x more equal moves | earlier passes on it used a small budget | today's card settings from W-0129 itself | 23 Nov |

## 10. About your n = 12 packet lift (from the shared chat)

I read the chat where your n = 11 packets (Q = 22 / T = 30 and Q = 29 / T = 24, against my Q = 38 / T = 16) are lifted into the 504-loop (7,3) space and compared with my selection E. Three things from my side that bear on it directly:

1. Price trails at what they really cost, not at 1. The floor Q + T counts every closed trail as one letter. In built words they cost more: at n = 10 a small trail that is not part of a complete orbit costs about 7 letters in its group, a complete orbit of seven about 10, a big trail about 1.15; fitted over many builds at n = 10 and 11, a trail costs about 1.5-1.7 and an empty 2-loop about 1.8-1.9. When I searched selections with the plain floor as the objective, the search kept trading charge for trails and every "better floor" built longer. Lift B looks like the same trade: Q 184 against 266 (-82), T 125 against 55 (+70), floor -12, but joining cost 379 against 140. With measured trail prices that floor gain turns into a loss unless the extra trails are big or join almost for free.
2. Which loops stay empty matters more than how many. Your chat's last idea (optimize which loops remain rowless) matches what moved n = 13: Jay's W-0129 block has 70 empty loops in 14 chains against 266 in 84 chains in the block before it, and that block alone took 14,542 letters off the start plan. Long chains of empty loops are cheap; scattered ones are not.
3. I can give you real lengths instead of a bound. If you send me the validated full n = 12 selection with Lift B (and the compound one), I can build the n = 12 word from it with my tools and run the same arrangement passes that produced E's records, so you get an actual length to compare with 522,736,409 rather than a restricted Kraft bound.
4. Lift B is in a part of the space my search never covered. E's (7,3) block is proved optimal in my block-search model (price Q + P x empty loops + chain terms, P = 2.9) but only among rotation-symmetric blocks. Your lifted packets are asymmetric, so they are outside the class where E is known to be best.
5. Which score predicts the built length at n = 12. I calibrated block scores against built n = 12 words (the word's own order found by your exact-order DP). Rank correlation with the built length: 0.90 for the priced score (empty loops at 2.9, chains counted), 0.61 for the plain floor Q + T. So the floor is a weak screen at n = 12; the priced score is a much better one, and all of its top 5 were copies of E.

Your projection lift (delete the new symbol, keep the parent walk) is close to question 2 below: my transport + exchange rule keeps the parent walks too and works for two levels only. If your lift carries the packet's relation to its empty loops along, that could be the missing piece.

## 11. Open questions, the ones I would most like ideas on

1. Is there a selection at K = 8 (n = 10) with 48 complete orbits of seven small trails and about 3 big trails? Or a proof that 14 big trails is the minimum?
2. A lifting rule for selections that beats plain transport at every level, not only at K = 8 and 9. The data in 5.3 is what I have.
3. Something between "every 2-loop covered once by one course" (impossible) and the current transport: which combinatorial object should a good selection at K = 9-11 be?
4. Below 517 at n = 11, given that the order is tight: which part of the selection, or which longer block shape, would you change first?
5. Your compound lift at n = 12: can it keep the empty loops in long chains while it lowers the charge? That is the trade section 10 is about.

## 12. Files your chat can load

All public in github.com/jhalfar/superpermutations (folder `selection/`):

| file | what it is |
|---|---|
| `selection/README.md` | the selection model, the block table and the commands that rebuild every block |
| `selection/gcore.py` | the step rule, slices, ports and the closed-trail count of a selection (the written rule the generators follow) |
| `selection/gsegip.py` | the block search (the one Jay ran further to get the W-0129 block): price Q + P x empty loops + chain and walk terms, LNS over sub-regions |
| `selection/block_grb.py`, `selection/gblock.py` | exact block models (Gurobi) for (7,2) and (7,3) |
| `selection/data/block_7_2_n11.txt` | my n = 11 (7,2) block: Q = 38, 14 empty loops in 3 chains |
| `selection/data/block_7_3_n12.txt` | E's n = 12 (7,3) block: Q = 266, 49 empty loops |
| `selection/data/block_7_4_n13.txt` | my n = 13 (7,4) block before Jay's: Q = 2,611, 266 empty loops in 84 chains |
| `selection/lit_block.py`, `selection/hybrid3.py` | write a block out literally / put a (7,3) block into a full n = 12 selection |
