import Mathlib.Tactic
import ErdosTernary.BridgeCompute

open ErdosTernary.BridgeCompute

-- Q(9) + 18 = 1072 < 1458 = uK 7

-- Check Q values
#eval Q 0 9  -- should be 1054

-- The key bound: for mass-1 r = Q(j) + ℓ with j ≤ 9, ℓ ≤ 18:
-- r ≤ Q(9) + 18 = 1072 < 1458 = uK 7 ≤ uK (K-1) for K > 7

-- For j ≥ 10, K ≤ 9: Q(10) = 24727 > uK K (since uK 9 = 13122)
-- So r ≥ 24727 > uK K, contradicting r < uK K from r ∈ computeNK K

-- For j ≥ 10, K = 10: Q(10) + ℓ ∈ [24727, 24745], uK 10 = 39366
-- But these all have hasTrailingDigit2 = true, so they're not in N_10

-- For j ≥ 10, K ≥ 11: uK (K-1) ≥ uK 10 = 39366 > 24745 ≥ Q(10) + 18
-- So r < uK (K-1)
