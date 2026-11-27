/-
Copyright (c) 2026 Ezzeldin Ashraf Mohamed Shafey Wahba. All rights reserved.
Released under the PolyForm Strict License 1.0.0 as described in the file LICENSE-CODE.
Authors: Ezzeldin Ashraf Mohamed Shafey Wahba
-/

import Lake
open Lake DSL

package erdosTernary where
  leanOptions := #[]

@[default_target]
lean_lib ErdosTernary where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.12.0"
