import ErdosTernary.Narkiewicz
import ErdosTernary.BridgeCompute

open ErdosTernary.BridgeCompute
open Narkiewicz

example (dj : Nat) (hdj : dj < 7) : 2 ^ (162 * 59049) % 3 ^ (dj + 6) = 1 := by
  interval_cases dj <;> norm_num [Nat.pow]
