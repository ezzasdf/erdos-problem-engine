import Mathlib.Tactic

#eval (5 : Nat) % 0
#check @Nat.mod_zero
#check @Nat.zero_mod

example : (5 : Nat) % 0 = 0 := by native_decide
