import Mathlib.Tactic
import ErdosTernary.Narkiewicz

open Narkiewicz

-- Test j=9: max residue ~39365
example : digit₃ (2^39365 : Nat) 9 = 1 := by norm_num [digit₃]

-- Test j=10: max residue ~118097
example : digit₃ (2^118097 : Nat) 10 = 1 := by norm_num [digit₃]

-- Test j=11: max residue ~354293
example : digit₃ (2^354293 : Nat) 11 = 1 := by norm_num [digit₃]

-- Test j=12: max residue ~1062881
example : digit₃ (2^1062881 : Nat) 12 = 1 := by norm_num [digit₃]
