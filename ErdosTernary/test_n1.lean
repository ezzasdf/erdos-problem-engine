import ErdosTernary.RotationDecomp

open ErdosTernary.ContinuedFraction

-- Master pattern for power comparisons:
-- log3_2 > p/q iff 3^p < 2^q
-- log3_2 < p/q iff 2^q < 3^p

private lemma logb3_2_gt (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (h : (3:ℝ)^p < (2:ℝ)^q) : (↑p : ℝ) / ↑q < Real.logb 3 2 := by
  have h3p : Real.logb 3 ((3:ℝ)^p) = (↑p : ℝ) := by
    rw [Real.logb_pow (by norm_num : (0:ℝ) < 3),
        show Real.logb 3 3 = 1 from Real.logb_self_eq_one (by norm_num : (1:ℝ) < 3),
        mul_one, Nat.cast_id]
  have h2q : Real.logb 3 ((2:ℝ)^q) = (↑q : ℝ) * Real.logb 3 2 := by
    rw [Real.logb_pow (by norm_num : (0:ℝ) < 2)]; push_cast; ring
  have h1 := Real.logb_lt_logb_iff (by norm_num : (1:ℝ) < 3)
    (by positivity) (by positivity) |>.mpr h
  rw [h3p, h2q] at h1
  rw [div_lt_iff (by positivity : (0:ℝ) < ↑q)] at h1
  linarith

private lemma logb3_2_lt (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (h : (2:ℝ)^q < (3:ℝ)^p) : Real.logb 3 2 < (↑p : ℝ) / ↑q := by
  have h3p : Real.logb 3 ((3:ℝ)^p) = (↑p : ℝ) := by
    rw [Real.logb_pow (by norm_num : (0:ℝ) < 3),
        show Real.logb 3 3 = 1 from Real.logb_self_eq_one (by norm_num : (1:ℝ) < 3),
        mul_one, Nat.cast_id]
  have h2q : Real.logb 3 ((2:ℝ)^q) = (↑q : ℝ) * Real.logb 3 2 := by
    rw [Real.logb_pow (by norm_num : (0:ℝ) < 2)]; push_cast; ring
  have h1 := Real.logb_lt_logb_iff (by norm_num : (1:ℝ) < 3)
    (by positivity) (by positivity) |>.mpr h
  rw [h2q, h3p] at h1
  rw [lt_div_iff (by positivity : (0:ℝ) < ↑q)] at h1
  linarith

-- Prove: 1/2 < log3_2 via 3^1 < 2^2
example : (1/2 : ℝ) < log3_2 := by unfold log3_2; push_cast; exact logb3_2_gt 1 2 (by omega) (by omega) (by norm_num)

-- Prove: log3_2 < 2/3 via 2^3 < 3^2
example : log3_2 < (2/3 : ℝ) := by unfold log3_2; push_cast; exact logb3_2_lt 2 3 (by omega) (by omega) (by norm_num)

-- Prove: 3/5 < log3_2 via 3^3 < 2^5
example : (3/5 : ℝ) < log3_2 := by unfold log3_2; push_cast; exact logb3_2_gt 3 5 (by omega) (by omega) (by norm_num)

-- Prove: 5/8 < log3_2 via 3^5 < 2^8
example : (5/8 : ℝ) < log3_2 := by unfold log3_2; push_cast; exact logb3_2_gt 5 8 (by omega) (by omega) (by norm_num)

-- Prove: log3_2 < 12/19 via 2^19 < 3^12
example : log3_2 < (12/19 : ℝ) := by unfold log3_2; push_cast; exact logb3_2_lt 12 19 (by omega) (by omega) (by norm_num)
