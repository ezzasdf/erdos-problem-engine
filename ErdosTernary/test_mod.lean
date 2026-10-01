import Mathlib.Tactic

#check @Nat.mul_mod
#check @Nat.mod_mul_mod
#check @Nat.mul_mod_mod
#check @Nat.mod_self

example (a b m : Nat) : (a * (b % m)) % m = (a * b) % m := by
  rw [Nat.mul_comm a (b % m), Nat.mod_mul_mod, Nat.mul_comm b a]

-- Alternative approach: just use simp
example (a b m : Nat) : (a * (b % m)) % m = (a * b) % m := by
  simp [Nat.mul_mod, Nat.mod_mod_of_dvd, Nat.mod_lt]
