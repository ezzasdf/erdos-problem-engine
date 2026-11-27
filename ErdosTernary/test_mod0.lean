/-
Copyright (c) 2026 Ezzeldin Ashraf Mohamed Shafey Wahba. All rights reserved.
Released under the PolyForm Strict License 1.0.0 as described in the file LICENSE-CODE.
Authors: Ezzeldin Ashraf Mohamed Shafey Wahba
-/

import Mathlib.Tactic

#eval (5 : Nat) % 0
#check @Nat.mod_zero
#check @Nat.zero_mod

example : (5 : Nat) % 0 = 0 := by native_decide
