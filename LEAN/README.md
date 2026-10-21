# Occupation and transport: an auditable Lean handoff

This is a source-only, standalone subset of Theo's Superperm Lean development,
prepared for discussion with Jakub Halfar. It includes the transitive source
dependencies of eight relevant entry modules, not the entire research project.
Names, proof hypotheses, author headers and original source bytes are retained.

**What it contributes:** exact literal occupation updates, ordered port
transport, row-balance identities, conditional integer clock recovery, and
coverage-preserving gluing/composition laws. These explain how an already
specified change can be certified. They do not select a globally best row
system, prove that phase determines attachment, or prove a new all-n bound.

**What is not certified here:** the complete 27-loop source walk and its
four-copy packing, any entire 46,174/46,173-character word, or correctness and
exhaustiveness of the native C++ optimizer. Those currently have native
checks/receipts, not a complete Lean data certificate in this bundle.

Start with [COMPARISON.md](COMPARISON.md) for the selection question and
[CLAIMS.md](CLAIMS.md) for theorem names, hypotheses, and remaining gaps.
`PublicClaims.lean` is the curated Lean entry point. The only added finite
mathematical checks are the published 27-row pattern's charge/port-cycle
calculation and a counterexample to identifying occupation from a Boolean mask.

## Build

Use Lean **4.31.0**, pinned by `lean-toolchain`. Mathlib is pinned to
`fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`. A complete dependency lock is
included. With Elan and Lake available, from this directory:

```sh
lake exe cache get
lake build PublicClaims AxiomAudit
```

To rerun the axiom gate even when Lake considers the build cached:

```sh
lake env lean AxiomAudit.lean
```

Initial dependency download can be large. There are no bundled object files,
Mathlib caches, executables, private keys, or corpus words.

Copy this entire directory into your public repository as a nested standalone
Lean project. Do not overwrite another project's `Coeff2` or
`SuperpermutationUpperBound` files blindly: compare `sources.json` hashes first.
The preserved namespaces make theorem correspondence clear, but they also mean
that divergent copies need a deliberate merge rather than automatic replacement.

For a source-clean serial rebuild using an existing Mathlib cache on Windows:

```powershell
./Verify.ps1 -DependencyProject /path/to/existing/lean-project `
  -Lean /path/to/lean.exe -OutputDirectory build-my-audit
```

This borrows only third-party dependency objects from `.lake/packages`.
Every bundled module is rebuilt, in `build-order.txt` order, into a fresh
object directory. One compiler process/thread runs at a time with a 6 GiB cap.
It invokes neither Git nor Lake. A fresh output directory is required.

`AxiomAudit.lean` examines every declaration, including private declarations,
in the imported bundled modules and rejects every axiom except `propext`,
`Classical.choice`, and `Quot.sound`. Missing or failed checks are errors,
not a proof of impossibility. It also audits the imported source dependencies,
not only the curated headline statements.

The 2026-10-20 local rebuild **passed**: 163 dependency modules plus the two
public entry/audit modules, in 1,606.8 seconds (about 26 minutes 47 seconds).
The final audit inspected 6,787 declarations, including 5,295 theorems, in
the imported bundled sources and `PublicClaims`. Only `propext`,
`Classical.choice`, and `Quot.sound` occurred as axioms. All 163 dependency
source hashes matched the originals. A source scan found no placeholder
proofs, custom axiom declarations, native proof evaluation, or IO/process
commands in those dependency modules.

Receipts are in `evidence/lean-verification.json`, `evidence/axiom-audit.log`,
and `evidence/build-progress.json`. These record an actual serial source rebuild.
The portable Lake commands are supplied for independent reproduction; they
are not claimed to have been run with a fresh network download here.

## Attribution and scope

See `NOTICE` and `sources.json`. The foundational Coeff2 development credits
Uku Raudvere. Pantone's imported construction files are unmodified at the
pinned revision. Halfar's selection and construction description remain his;
our use of phase openings does not make his row selection our invention.

The copied Halfar README is a historical, pinned source, not a claim about
the current world record. `evidence/native-*.json` are numerical experiment
receipts, deliberately separated from the Lean verification evidence.
The verbatim historical experiment note references some original-workspace
files that are not bundled. The Lean source/build closure is standalone;
the full native search campaign is not included or claimed independently
reproducible from those summary receipts alone.

There is no mathematical predicate named “Albion” in this handoff. That is
our informal picture of coupled occupation and transport, not an additional
proved classification or an optimality invariant.
