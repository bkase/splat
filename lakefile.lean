import Lake

open Lake DSL

package LeanLearn

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.24.0"

@[default_target]
lean_lib Succinct
