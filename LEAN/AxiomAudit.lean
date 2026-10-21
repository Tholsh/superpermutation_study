import PublicClaims
import Lean.Util.CollectAxioms

/-! Inspect EVERY declaration in the imported bundled modules, including
private declarations. Only Lean's usual three mathematical axioms pass.
This gate is a build-time audit; it is not used as a mathematical premise. -/
open Lean Elab Command

run_cmd do
  let env ← getEnv
  let imported := env.header.moduleNames.filter fun n =>
    (`Coeff2).isPrefixOf n || (`SuperpermutationUpperBound).isPrefixOf n || n == `PublicClaims
  unless imported.size == 164 do
    throwError "Incomplete bundled import closure: expected 164 modules, got {imported.size}"
  let mut checked := 0
  let mut theorems := 0
  let mut modules : Std.HashSet Name := {}
  for (name, info) in env.constants.toList do
    let moduleName := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx.toNat]!
      | none => Name.anonymous
    let bundled := (`Coeff2).isPrefixOf moduleName ||
      (`SuperpermutationUpperBound).isPrefixOf moduleName || moduleName == `PublicClaims
    if bundled then
      modules := modules.insert moduleName
      checked := checked + 1
      if info matches .thmInfo _ then theorems := theorems + 1
      let axs ← Lean.collectAxioms name
      for ax in axs do
        unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
          throwError "Nonstandard axiom in {name}: {ax}"
  unless checked > 0 && theorems > 0 do
    throwError "Empty declaration audit"
  logInfo m!"AXIOM_AUDIT_PASS imported_modules={imported.size} declaring_modules={modules.size} declarations={checked} theorems={theorems} allowed=[propext, Classical.choice, Quot.sound]"
