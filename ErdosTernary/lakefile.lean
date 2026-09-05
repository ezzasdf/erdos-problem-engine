import Lake
open Lake DSL

package erdosTernary where
  leanOptions := #[]

@[default_target]
lean_lib ErdosTernary where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.12.0"
