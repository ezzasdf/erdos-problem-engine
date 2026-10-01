import Mathlib.Tactic
import ErdosTernary.BridgeCompute
import ErdosTernary.Mass1Dynamics

open ErdosTernary.BridgeCompute
open ErdosTernary.OstrowskiFormLemma

-- For each K=8..16, check all mass-1 candidates j∈[10,20]:
-- either Q(j)+ℓ ≥ uK K (excluded by range), or hasTrailingDigit2 = true
#eval Id.run do
  let mut violations : List (Nat × Nat × Nat × Nat) := []
  for K in [8:17] do
    for j in [10:21] do
      for ℓ in [0:19] do
        let c := Q Al32 j + ℓ
        if c < uK K then
          let pow2r := 2 ^ c % 3 ^ K
          if !hasTrailingDigit2 pow2r K then
            violations := violations ++ [(K, j, ℓ, c)]
  return violations
