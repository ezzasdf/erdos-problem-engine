import Mathlib.Tactic
import ErdosTernary.BridgeCompute

open ErdosTernary.BridgeCompute

-- Key: for i < K-1, the i-th ternary digit of (v % 3^(K-1)) equals that of v
-- because v % 3^(K-1) and v agree on digits 0..K-2

-- hasTrailingDigit2 v K checks digits 0..K-1 of v in base 3
-- If v has no digit 2 in 0..K-1, then v % 3^(K-1) has no digit 2 in 0..K-2

-- Check: does Q(10) + ℓ get excluded from N_10 for all ℓ ≤ 18?
#eval (List.range 19).map fun ℓ => 
  let c := 24727 + ℓ  -- Q(10) = 24727
  let pow2r := 2 ^ c % 3 ^ 10
  (ℓ, c, hasTrailingDigit2 pow2r 10)

-- Check uK values
#eval uK 7   -- should be 1458
#eval uK 8   -- should be 4374
#eval uK 9   -- should be 13122
#eval uK 10  -- should be 39366
