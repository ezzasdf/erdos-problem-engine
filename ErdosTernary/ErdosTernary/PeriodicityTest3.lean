/-
Copyright (c) 2026 Ezzeldin Ashraf Mohamed Shafey Wahba. All rights reserved.
Released under the PolyForm Strict License 1.0.0 as described in the file LICENSE-CODE.
Authors: Ezzeldin Ashraf Mohamed Shafey Wahba
-/

import Mathlib.Tactic
import ErdosTernary.Narkiewicz

open Narkiewicz

-- Test j=13: max residue ~3188645
example : digit₃ (2^3188645 : Nat) 13 = 1 := by norm_num [digit₃]
