# Audit result, 2026-10-20

Passed: all 163 bundled dependency source modules rebuilt with Lean 4.31.0,
followed by PublicClaims and AxiomAudit. No original project object directory
was on LEAN_PATH. Only the pinned third-party Mathlib dependency caches were
borrowed. Compilation ran serially, one thread, with a 6 GiB memory cap.

The audit imported 164 bundled modules including PublicClaims. 163 of these
define declarations (Coeff2.Defs is an import-only umbrella). It inspected
6,787 declarations, including 5,295 theorems. Every axiom dependency was in
{propext, Classical.choice, Quot.sound}. No placeholder/native/compiler-trust
axiom was accepted. All 165 compiler invocations exited successfully.

The finite 27-row control passes: length 27, row charge 16, port return map
[4,0,3,1,2], one cycle (0 4 2 3 1). This is a check of the defined port model,
not a certificate of the four-copy literal packing or of a full record word.

All 163 dependency file SHA-256 values match the original source snapshots.
Pantone's 69 included source files are unmodified. Original author headers
and Apache-2.0 notices are retained. The other two Lean files are new public
entry/audit wrappers; no source theorem from the existing development was
changed in order to make this audit pass.

Static inspection found no sorry/admit proofs, custom axiom declarations,
native_decide proofs, IO.Process, IO.FS, run_cmd or #eval commands in the 163
dependency modules. Two raw placeholder-keyword matches were ordinary comments.
AxiomAudit itself intentionally uses run_cmd to inspect the environment; it
does not use that command to establish a mathematical theorem.

Compiler/linter warnings in legacy sources were retained; success does not
mean warning-free. Full per-module logs and the compiler objects remain in
the research workspace outside this public source bundle. The compact
receipts here include exit codes, timings, exact public signatures, and the
complete declaration axiom gate result.

There is still no end-to-end Lean certificate for the native joint DP or the
full 46,173-character output in this bundle. Native scan receipts are separate
evidence, not part of the kernel proof. See CLAIMS.md and COMPARISON.md for the
specific application and selection-domain limitations.
