import Mathlib.Tactic
import ErdosTernary.BridgeCompute
import ErdosTernary.OstrowskiFormLemma
import ErdosTernary.Mass1Dynamics

open ErdosTernary.BridgeCompute
open ErdosTernary.OstrowskiFormLemma
open Narkiewicz
open ErdosTernary.Mass1Dynamics

-- Check: for K=8..11, is mass1_in_NK K empty?
-- mass1_in_NK K = (computeNK K).filter fun r => decide (isMassOneForm r)
-- These use computeNK which is slow for large K...

-- Actually, the direct approach: for K > 7, j >= 10:
-- Either c >= uK(K) or hasTrailingDigit2 (2^c % 3^K) K
-- We've verified this for K=8..25 with j up to 27.

-- For the proof, the key insight is:
-- For K >= 8 and j >= 10: 
--   Q(10)+18 = 24745
--   For K=8: uK(8) = 4374 < 24745, so all j>=10 candidates are out of range
--   For K=9: uK(9) = 13122 < 24745, so all j>=10 candidates are out of range
--   For K >= 10: all j>=10 candidates that are in range have digit 2

-- So the proof for no_births_after_K7 is:
-- 1. Take p = r
-- 2. Show r < uK(K-1): since j <= 9 (j >= 10 impossible), r <= 1072 < 1458 = uK(7) <= uK(K-1)
-- 3. Show ¬hasTrailingDigit2 (2^r % 3^(K-1)) (K-1): follows from ¬hasTrailingDigit2 (2^r % 3^K) K

-- For step 3, we need: ¬hasTrailingDigit2 v K → ¬hasTrailingDigit2 (v % 3^(K-1)) (K-1)
-- This is the trail_subset lemma.

-- Let me verify: for K=8,9: uK(K) < Q(10) = 24727
#eval (uK 8 < Q Al32 10 : Bool)
#eval (uK 9 < Q Al32 10 : Bool)

-- So for K=8,9 and j >= 10: c = Q(j)+l >= Q(10) > uK(K), so c >= uK(K)
-- This means r ∉ computeNK(K), contradiction.
-- For K >= 10 and j >= 10: need digit 2 (verified for K=10..25)

-- For K >= 10: the simplest proof is to use mass1Excluded
-- mass1Excluded checks j=5..20, l=0..18
-- But mass1Excluded K = true would mean ALL mass-1 elements are excluded
-- Including j <= 9, which are NOT excluded!

-- Wait, mass1Excluded checks: decide (uK K <= c) || hasTrailingDigit2 (pow2Mod c (3 ^ K)) K
-- For j=5..9 and l=0..18: c = Q(j)+l <= Q(9)+18 = 1072 < uK(K) for K >= 8
-- So the size check fails, and we need digit 2. But j<=9 elements DON'T have digit 2
-- (they're in N_K). So mass1Excluded K = false for K >= 8.

-- Hmm, so we can't use mass1Excluded directly.

-- The key is to use mass1_j_ge_10_excluded which only checks j >= 10.
-- We verified mass1_j_ge_10_excluded K = true for K = 8..25.

-- For K >= 26: we need to argue differently.
-- But actually, for K >= 26, the hypothesis r ∈ computeNK(K) with isMassOneForm r
-- and j >= 10 is vacuously false because:
-- - For j <= 20: mass1_j_ge_10_excluded 25 = true, and by monotonicity, digit 2 at K >= 25
-- - For j >= 21: Q(j) grows fast, and for K <= 25, either out of range or digit 2
-- - For K >= 26 and j >= 21: need separate argument

-- Actually, the critical observation is:
-- For K >= 10 and j >= 10, c = Q(j)+l < uK(K):
--   c mod 3^10 determines 2^c mod 3^10, which has digit 2 (verified for c < uK(10))
--   But c might be > uK(10), so c mod 3^10 might not be < uK(10)

-- Let me check: does 2^c mod 3^10 always have digit 2 for c >= Q(10)?
-- Q(10) = 24727. uK(10) = 39366. 
-- 2^24727 mod 3^10 -- does it have digit 2?
-- mass1_j_ge_10_excluded 10 = true, so yes for c = Q(10)+l with l <= 18.

-- But what about c = Q(11) = 50508? Is 2^50508 mod 3^10 digit-2?
-- mass1_j_ge_10_excluded 10 checks j=10..20, so Q(11)+l is checked.
-- Q(11)+0 = 50508 > uK(10) = 39366, so excluded by size at K=10.
-- For K=11: uK(11) = 118098 > 50508. mass1_j_ge_10_excluded 11 = true.
-- So digit 2 at K=11 for c = 50508.

-- The general pattern: for c = Q(j)+l with j >= 10, l <= 18:
-- Find the smallest K0 where c < uK(K0). Then mass1_j_ge_10_excluded K0 = true
-- (verified for K0 = 10..25). Digit 2 at K0 implies digit 2 at all K >= K0.

-- For K0 > 25: we haven't verified mass1_j_ge_10_excluded.
-- But for K0 > 25 and K >= K0: c < uK(K0) <= uK(K). 
-- We need digit 2 at K0, which we haven't verified.

-- Hmm, but actually, for the proof of no_births_after_K7, we need:
-- For K > 7, if r ∈ computeNK(K) and isMassOneForm r, then j <= 9.
-- Because for j >= 10: either r >= uK(K) (not in range) or has digit 2 (not in N_K).

-- For K <= 25: verified by mass1_j_ge_10_excluded.
-- For K >= 26: we need digit 2 for all j >= 10, l <= 18 with c < uK(K).

-- Actually wait, let me reconsider. For the proof, I can use a different strategy:
-- Instead of proving j >= 10 is impossible, I can directly prove r < uK(K-1).

-- For j <= 9: r <= 1072 < uK(7) <= uK(K-1) for K > 7. ✓
-- For j >= 10: r ∉ computeNK(K) (contradiction). ✓

-- So the proof only needs:
-- 1. For j >= 10 and K > 7: r ∉ computeNK(K)
-- 2. trail_subset: ¬hasTrailingDigit2 v K → ¬hasTrailingDigit2 (v % 3^(K-1)) (K-1)

-- For (1): we need to handle K >= 26 too.
-- But actually, for K >= 26 and j >= 10: if c < uK(K), we need digit 2.
-- We can prove this by observing that for c = Q(j)+l with j >= 10, l <= 18:
-- c >= Q(10) = 24727. For K >= 10: 3^K is huge.
-- The key: 2^c mod 3^K has K ternary digits. For K >= 10, the first 10 digits
-- of 2^c mod 3^K are the same as 2^c mod 3^10.
-- And 2^c mod 3^10 has digit 2 (verified for c = Q(j)+l with j=10..20, l=0..18).

-- But for j > 20: c > uK(10), so 2^c mod 3^10 might differ.
-- Actually, 2^c mod 3^10 depends on c mod order(2, 3^10).
-- order(2, 3^10) = 2*3^9 = 39366 (since 2 is a primitive root mod 3^k).

-- Hmm wait, 2 is NOT a primitive root mod 3^k for k >= 3.
-- Actually, 2 is a primitive root mod 3, and by lifting, 2 is a primitive root mod 3^k for all k.
-- So order(2, 3^10) = φ(3^10) = 2*3^9 = 39366.

-- So 2^c mod 3^10 = 2^(c mod 39366) mod 3^10.
-- For c = Q(j)+l: c mod 39366 = (Q(j)+l) mod 39366.

-- This is getting too complex. Let me just use a simpler approach.

-- THE SIMPLEST APPROACH:
-- For K > 7 and j >= 10: 
--   If K <= 9: c >= Q(10) > uK(K), so r ∉ computeNK(K). ✓
--   If K >= 10: mass1_j_ge_10_excluded K = true for K=10..25. For K >= 26:
--     We know mass1_j_ge_10_excluded K0 = true for some K0 <= 25 with c < uK(K0).
--     Since 3^K0 | 3^K, digit 2 at K0 implies digit 2 at K.
--     
--     But we need c < uK(K0) for some K0 <= 25.
--     For j <= 20: c = Q(j)+l <= Q(20)+18 = 135797356. uK(17) = 86093442.
--     Q(20)+18 > uK(17). uK(18) = 258280326 > Q(20)+18. So K0 = 18.
--     mass1_j_ge_10_excluded 18 = true. ✓
--     
--     For j = 21: c = Q(21)+l = 220632925+l. uK(18) = 258280326 > c. K0 = 18. ✓
--     For j = 22: c = Q(22)+l = 356430281+l. uK(18) = 258280326 < c. uK(19) = 774840978 > c. K0 = 19.
--     mass1_j_ge_10_excluded 19 = true. ✓
--     
--     For j >= 23: need to find K0 <= 25.
--     Q(23) = 577063206 < uK(19) = 774840978. K0 = 19. ✓
--     Q(24) = 933493487 > uK(19). uK(20) = 2324522934 > Q(24)+18. K0 = 20. ✓
--     Q(25) = 1510556693 < uK(20). K0 = 20. ✓
--     Q(26) = 2444050180 < uK(20). K0 = 20. ✓
--     Q(27) = 3954606873 > uK(20). uK(21) = 6973568802 > Q(27)+18. K0 = 21.
--     mass1_j_ge_10_excluded 21 = true. ✓
--     
--     Q(28) = 6398657053 < uK(21). K0 = 21. ✓
--     Q(29) = 10353263926 > uK(21). uK(22) = 20920706406 > Q(29)+18. K0 = 22.
--     mass1_j_ge_10_excluded 22 = true. ✓
--     
--     Q(30) = 16751920979 < uK(22). K0 = 22. ✓
--     Q(31) = 27105184905 > uK(22). uK(23) = 62762119218 > Q(31)+18. K0 = 23.
--     mass1_j_ge_10_excluded 23 = true. ✓
--     
--     Q(32) = 43857105884 < uK(23). K0 = 23. ✓
--     Q(33) = 70962290789 > uK(23). uK(24) = 188286357654 > Q(33)+18. K0 = 24.
--     mass1_j_ge_10_excluded 24 = true. ✓
--     
--     Q(34) = 114819396673 < uK(24). K0 = 24. ✓
--     Q(35) = 185781687462 > uK(24). uK(25) = 564859072962 > Q(35)+18. K0 = 25.
--     mass1_j_ge_10_excluded 25 = true. ✓
--     
--     Q(36) = 300601084135 < uK(25). K0 = 25. ✓
--     Q(37) = 486382771597 < uK(25). K0 = 25. ✓
--     Q(38) = 786983855732 > uK(25). 
--     uK(26) = 1694577218886 > Q(38)+18. K0 = 26.
--     But mass1_j_ge_10_excluded 26 is NOT verified!

-- Hmm, so for j=38 and K >= 26: c = Q(38)+l < uK(26). Need digit 2 at K=26.
-- But we haven't verified mass1_j_ge_10_excluded 26.

-- However, mass1_j_ge_10_excluded only checks j_off in [0,15] (j in [10,25]).
-- For j=38: j_off = 28, which is NOT in range.
-- So mass1_j_ge_10_excluded doesn't even check j=38!

-- Wait, but for the proof of no_births_after_K7, we need:
-- For K > 7, if r ∈ computeNK(K) and isMassOneForm r, then j <= 9.
-- For j >= 10: r ∉ computeNK(K).
-- We've shown this for j in [10,25] and K = 8..25.
-- For j >= 26: we need a different argument.

-- For j >= 26: Q(j) >= Q(26) = 2444050180.
-- For K <= 22: uK(K) <= uK(22) = 20920706406 < Q(26).
-- So for K <= 22 and j >= 26: c >= Q(26) > uK(K). r ∉ range. ✓
-- For K >= 23: need digit 2.
-- Q(26)+18 = 2444050198 < uK(23) = 62762119218. In range.
-- But mass1_j_ge_10_excluded only checks j up to 25.

-- For j=26: c = Q(26)+l. 2^c mod 3^K for K >= 23.
-- We need hasTrailingDigit2 (2^c mod 3^K) K = true.
-- This is NOT directly verified.

-- Hmm, but we CAN verify it by checking that for c = Q(26)+l, 
-- 2^c mod 3^23 has digit 2. Let me check.

-- Actually, wait. mass1_j_ge_10_excluded K checks j_off in [0,15] → j in [10,25].
-- For j=26: j_off = 26-10 = 16, which is NOT in range [0,15].
-- So j=26 is NOT checked by mass1_j_ge_10_excluded.

-- But mass1_j10_27 checks j_off in [0,17] → j in [10,27]. So j=26 IS checked.
-- mass1_j10_27 K = true for K = 10..25 (verified). ✓

-- For j=27: j_off = 17, in range [0,17]. Checked. ✓
-- For j=28: j_off = 18, NOT in range [0,17].

-- So for j >= 28: not checked by mass1_j10_27.
-- For j=28: Q(28)+18 = 6398657071.
-- For K <= 21: uK(K) <= uK(21) = 6973568802 > Q(28)+18. In range for K=21.
-- For K=21: mass1_j_ge_10_excluded 21 checks j up to 25. j=28 not checked.

-- OK, so we need mass1_j_ge_10_excluded to check j up to at least 38 for K up to 25.
-- Or we need a different argument.

-- ALTERNATIVE APPROACH: Instead of using mass1_j_ge_10_excluded,
-- use the fact that for j >= 10 and K >= 10, 2^(Q(j)+l) mod 3^K always has digit 2.

-- This follows from: for j >= 10, the Ostrowski representation of Q(j) has
-- a specific structure that forces digit 2 in 2^Q(j) mod 3^K.

-- But proving this requires the Ostrowski theory, which is complex.

-- PRACTICAL APPROACH: For the Lean proof, use a sorry for the general case,
-- and rely on the computational verification for K <= 25.

-- Actually, I just realized: for the proof of no_births_after_K7,
-- we can use a MUCH simpler approach:

-- For K > 7 and j >= 10:
-- If r = Q(j)+l ∈ computeNK(K), then r < uK(K) and ¬hasTrailingDigit2 (2^r % 3^K) K.
-- We need to show this is impossible.
--
-- Case 1: K <= 9. Then r >= Q(10) = 24727 > uK(9) >= uK(K). So r >= uK(K). Contradiction. ✓
-- Case 2: K >= 10. 
--   Sub-case 2a: j <= 25. Then r = Q(j)+l <= Q(25)+18 = 1510556711.
--     We need K0 <= 25 with r < uK(K0) and mass1_j_ge_10_excluded K0 = true.
--     For each j in [10,25], such K0 exists (as shown above). ✓
--   Sub-case 2b: j >= 26.
--     Q(26) = 2444050180. For K <= 22: uK(K) <= uK(22) = 20920706406.
--     Wait, uK(22) = 2*3^21 = 2*10460353203 = 20920706406 > Q(26)+18. So r < uK(22).
--     mass1_j_ge_10_excluded 22 = true. ✓

--     For K = 23: uK(23) = 2*3^22 = 62762119218. r < uK(23).
--     mass1_j_ge_10_excluded 23 = true. ✓

--     For K = 24: uK(24) = 188286357654. r < uK(24).
--     mass1_j_ge_10_excluded 24 = true. ✓

--     For K = 25: uK(25) = 564859072962. r < uK(25).
--     mass1_j_ge_10_excluded 25 = true. ✓

-- But wait, mass1_j_ge_10_excluded only checks j in [10,25] (j_off in [0,15]).
-- For j=26 and K=22: mass1_j_ge_10_excluded 22 does NOT check j=26.
-- So we can't conclude digit 2 at K=22 for j=26.

-- Hmm, this is the fundamental gap. mass1_j_ge_10_excluded doesn't check j >= 26.

-- Let me check: can we extend mass1_j_ge_10_excluded to check j up to 38?
-- That's 29 j values * 19 l values = 551 candidates.
-- Each needs pow2Mod c (3^K) for c up to ~800B and K up to 25.
-- This might be too slow for Lean.

-- Actually, for K=25: 3^25 = 847288609443. pow2Mod c (3^25) for c up to 800B
-- requires about 40 modular squarings (since 2^40 > 800B). This should be fast.

-- Let me try a different function that checks j up to 40 for K=10..25.
