# N=13 RLLB selection studies

This is a research directory, not a record directory. **No completed recursive lift or new N=13 record is claimed.** The [paper](rllb_n13.pdf), [LaTeX source](rllb_n13.tex), [notes](NOTES.md), [source inventory](source-import.json), and retained `data/n13/rllb/` reports distinguish native selections, restricted bounds, and literal words.

## First computational chain: current RLLB

For a complete experimental selection extracted from the supplied archive:

```sh
make rllb rllb-ports
mkdir -p build/n13-rllb
xz -dc /path/to/n13_kernel_hybrid_48.selection.xz > build/n13-rllb/selection.txt
./build/rllb-ports --n 13 build/n13-rllb/selection.txt build/n13-rllb/selection
./build/rllb build/n13-rllb/selection 1812288 build/n13-rllb/score.json 6 12 .04 6747800155 - - --n 13 --grouped
```

The scorer to run is the new [`search/rllb.cpp`](../../../search/rllb.cpp), not an archived replay script. The target is the experiment's historical comparison length. Full-key pricing is available by omitting `--grouped`; that changes the price family. A full N=13 graph has tens of millions of ports and needs substantial RAM and disk. This current repository session did not rerun the complete N=13 native experiment or construct its literal word.

## Exact archived advancements

- The Step1-to-N difference has 259 changed 2-loops in eight balanced switches: one 161-loop component and seven 14-loop components. All 256 switch combinations were enumerated; 56 attain minimum local `Q+T=2,869` in this family.
- A 42-row patch gives a complete (7,4) packet with `Q=2,443`, 406 loops without a row, five active row walks, and 426 completed trails. One 288-row walk has monodromy cycles `(7,3)`. This is a finite valid packet, not a general lift theorem.
- Applying the packet in 48 residual fibers gives the archived full native totals `Q=1,812,288`, `D=19,488`, `T=28,164`. The intact weight-3 analytical floor is 6,747,779,661. The archived grouped trie gave 6,747,779,651, which is weaker; it did not establish an achievable word below the comparison length.
- Mask 186 preserves those structural totals while changing 2,688 native row assignments. Its preference over mask 38 comes from seed-dependent local path-cover heuristics, not a certified global arrangement advantage.
- The conservative whole-walk-demotion experiment reached a complete native selection with `Q=1,786,938`, `T=81,970`, but its intact weight-3 floor 6,747,808,117 misses the stated target. A monodromy-correct partial motif did not by itself solve cheap integration into a full selection.
- The selection-first compound-core checkpoint lowers `Q+T` by 780 on the retained N-block control. Its 48-Step1 variant improves the structural floor by 1,836 relative to that experiment's Halfar-N baseline. These are selection-stage changes, not literal-length records.

The retained reports, patches, profiles and original native-check logs are evidence of what the archive reported. Their factorial **cyclic-class** completion counts are not a newly scanned 6.7-billion-symbol word. New word/lift claims would require the missing constructive arrangement step and its own checked witness.
