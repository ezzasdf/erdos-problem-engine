/-
Copyright (c) 2026 Ezzeldin Ashraf Mohamed Shafey Wahba. All rights reserved.
Released under the PolyForm Strict License 1.0.0 as described in the file LICENSE-CODE.
Authors: Ezzeldin Ashraf Mohamed Shafey Wahba
-/

import Mathlib.Tactic
import ErdosTernary.Narkiewicz

open Narkiewicz

-- Test j=15: max residue ~28697813 (the hardest case: s=8, k%3=2, j=15)
example : digit₃ (2^28697813 : Nat) 15 = 1 := by norm_num [digit₃]
