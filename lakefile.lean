import Lake

open Lake DSL

package LeanLearn where
  allowNonModules := true
  leanOptions := #[
    ⟨`warningAsError, true⟩,
    ⟨`linter.unusedVariables, false⟩,
    ⟨`linter.unusedSectionVars, false⟩,
    ⟨`linter.unusedSimpArgs, false⟩,
    ⟨`linter.unnecessarySimpa, false⟩,
    ⟨`linter.unusedTactic, false⟩,
    ⟨`linter.unreachableTactic, false⟩,
    ⟨`linter.unnecessarySeqFocus, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.36.0"

@[default_target]
lean_lib Succinct
