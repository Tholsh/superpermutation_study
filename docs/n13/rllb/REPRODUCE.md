# Reproduce the N=13 selection screens

This directory records research, not a new record or a completed lift. The [research account](README.md), [paper](rllb_n13.pdf), [personal notes](NOTES.md), and [source inventory](source-import.json) describe exactly which statements come from archived reports.

## Chain 1: the new C++ RLLB

The file to run is [`search/rllb.cpp`](../../../search/rllb.cpp), built as `build/rllb`. Extract a complete experimental native selection from the supplied RLLB archive first; large native selections are not duplicated in this repository's record corpus.

```sh
make rllb rllb-ports
mkdir -p build/n13-rllb
xz -dc /path/to/n13_kernel_hybrid_48.selection.xz > build/n13-rllb/selection.txt
./build/rllb-ports --n 13 build/n13-rllb/selection.txt build/n13-rllb/selection
./build/rllb build/n13-rllb/selection 1812288 build/n13-rllb/score.json 6 12 .04 6747800155 - - --n 13 --grouped
```

Expected archived native totals for this input are `Q=1,812,288`, 19,488 loops without rows, 28,164 completed trails, and 41,729,088 ports. The target is the experiment's historical comparison length. The intact weight-3 analytical floor is 6,747,779,661; a grouped-price result may be weaker. Neither passing the screen nor a low structural score supplies an achievable full word.

Full-key pricing is available by omitting `--grouped`; this changes the price family. Weight-2 openings, splits, and full occupation constraints require their own treatment. The complete graph has tens of millions of ports and needs substantial RAM and disk.

## Archived native evidence and next stage

Original small patches, profiles, reports and native-check logs are preserved under `data/n13/rllb/`. Full native selections and their original generators remain in the supplied archive, SHA-256 `5da9268ea1d6ff2b5b50a0cc0a4f629016684fccc1a3fbf876ef847d61996c86`.

This repository session checked the fast N=13 grouped scorer on a local packet, not the complete N=13 selection or a new 6.7-billion-symbol word. The next constructive stage is a globally feasible arrangement; no completed word or recursive lift is inferred from the archived selection certificates.
