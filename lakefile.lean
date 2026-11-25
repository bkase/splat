import Lake

open Lake DSL

package LeanLearn where
  allowNonModules := true
  leanOptions := #[
    ⟨`warningAsError, true⟩,
    ⟨`weak.linter.unusedVariables, false⟩,
    ⟨`weak.linter.unusedSectionVars, false⟩,
    ⟨`weak.linter.unusedSimpArgs, false⟩,
    ⟨`weak.linter.unnecessarySimpa, false⟩,
    ⟨`weak.linter.unusedTactic, false⟩,
    ⟨`weak.linter.unreachableTactic, false⟩,
    ⟨`weak.linter.unnecessarySeqFocus, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.36.0"

@[default_target]
lean_lib Succinct

@[default_target]
lean_lib Challenge

@[default_target]
lean_lib Solution
