import Mathlib.Tactic
import ErdosTernary.Narkiewicz

open Narkiewicz

-- Local definitions matching SayeLemma (independent of its broken theorems).
def u (k : Nat) : Nat := 2 * 3 ^ (k - 1)
def d1 (j : Nat) : Nat := (2 ^ j / 3 ^ 0) % 3

-- CLAIM (corrected version of the Density.lean comment):
--   digit₃(2^(i·u_k + j)) k = (digit₃(2^j) k + i·d1(j)) % 3
-- for ALL i (the comment claimed step u_{k+1}; I claim step u_k, and i can be up to 8).
example : digit₃ (2 ^ (1 * u 1 + 0)) 1 = (digit₃ (2 ^ 0) 1 + 1 * d1 0) % 3 := by
  native_decide
example : digit₃ (2 ^ (5 * u 1 + 0)) 1 = (digit₃ (2 ^ 0) 1 + 5 * d1 0) % 3 := by
  native_decide
example : digit₃ (2 ^ (8 * u 1 + 0)) 1 = (digit₃ (2 ^ 0) 1 + 8 * d1 0) % 3 := by
  native_decide
example : digit₃ (2 ^ (2 * u 2 + 1)) 2 = (digit₃ (2 ^ 1) 2 + 2 * d1 1) % 3 := by
  native_decide
example : digit₃ (2 ^ (7 * u 2 + 3)) 2 = (digit₃ (2 ^ 3) 2 + 7 * d1 3) % 3 := by
  native_decide
example : digit₃ (2 ^ (4 * u 3 + 5)) 3 = (digit₃ (2 ^ 5) 3 + 4 * d1 5) % 3 := by
  native_decide
example : digit₃ (2 ^ (8 * u 3 + 1)) 3 = (digit₃ (2 ^ 1) 3 + 8 * d1 1) % 3 := by
  native_decide