import Mathlib.Tactic
import ErdosTernary.Narkiewicz

open Narkiewicz

/-! Test whether norm_num can handle digit₃ of large powers of 2 -/

-- Test 1: Basic norm_num on digit₃
example : digit₃ (2^48 : Nat) 0 = 1 := by norm_num [digit₃]
example : digit₃ (2^48 : Nat) 1 = 0 := by norm_num [digit₃]

-- Test 2: norm_num on 2^N % 3^M for large N
example : (2^486 : Nat) % 729 = 1 := by norm_num
example : (2^162 : Nat) % 243 = 1 := by norm_num

-- Test 3: Can norm_num handle digit₃ of 2^N for N up to ~1500?
-- (This tests whether the periodicity approach is feasible for j=6)
example : digit₃ (2^1457 : Nat) 6 = 1 := by norm_num [digit₃]

-- Test 4: Larger
example : digit₃ (2^4373 : Nat) 7 = 1 := by norm_num [digit₃]

-- Test 5: Even larger
example : digit₃ (2^13121 : Nat) 8 = 1 := by norm_num [digit₃]
