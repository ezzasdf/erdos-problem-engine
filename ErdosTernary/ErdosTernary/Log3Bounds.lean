import Mathlib

set_option linter.unusedVariables false in
set_option linter.unusedTactic false in

-- Power comparison lemmas for log₃(2) convergent bounds.
-- These are proved here (with a lighter import context) so norm_num
-- doesn't time out when the full ErdosTernary file is loaded.

private lemma logb3_2_h3p (p : ℕ) : Real.logb 3 ((3:ℝ)^p) = (↑p : ℝ) := by
  rw [Real.logb_pow (by norm_num : (0:ℝ) < 3),
    show Real.logb 3 3 = 1 from Real.logb_self_eq_one (by norm_num : (1:ℝ) < 3), mul_one]

private lemma logb3_2_h2q (q : ℕ) : Real.logb 3 ((2:ℝ)^q) = (↑q : ℝ) * Real.logb 3 2 := by
  rw [Real.logb_pow (by norm_num : (0:ℝ) < 2)]

private lemma logb3_2_gt (p q : ℕ) (_hp : 0 < p) (hq : 0 < q)
    (h : (3:ℝ)^p < (2:ℝ)^q) : (↑p : ℝ) / ↑q < Real.logb 3 2 := by
  have h1 := Real.logb_lt_logb_iff (by norm_num : (1:ℝ) < 3)
    (by positivity) (by positivity) |>.mpr h
  rw [logb3_2_h3p p, logb3_2_h2q q] at h1
  rw [div_lt_iff' (by positivity : (0:ℝ) < ↑q)]; exact h1

private lemma logb3_2_lt (p q : ℕ) (_hp : 0 < p) (hq : 0 < q)
    (h : (2:ℝ)^q < (3:ℝ)^p) : Real.logb 3 2 < (↑p : ℝ) / ↑q := by
  have h1 := Real.logb_lt_logb_iff (by norm_num : (1:ℝ) < 3)
    (by positivity) (by positivity) |>.mpr h
  rw [logb3_2_h2q q, logb3_2_h3p p] at h1
  rw [lt_div_iff' (by positivity : (0:ℝ) < ↑q)]; exact h1

-- Bounds needed for xi chain steps ξ₉ through ξ₁₅
-- These use the convergent denominators of the CF of log₃(2).

-- c₈ = 306/485 < log3_2 < c₉ = 665/1054
lemma log3_2_gt_306_485 : Real.logb 3 2 > (306:ℝ) / 485 :=
  logb3_2_gt 306 485 (by omega) (by omega) (by norm_num : (3:ℝ)^306 < (2:ℝ)^485)
lemma log3_2_lt_665_1054 : Real.logb 3 2 < (665:ℝ) / 1054 :=
  logb3_2_lt 665 1054 (by omega) (by omega) (by norm_num : (2:ℝ)^1054 < (3:ℝ)^665)

-- c₉ = 665/1054 > log3_2 > c₈ = 306/485, for ξ₉ floor
lemma log3_2_gt_971_1539 : Real.logb 3 2 > (971:ℝ) / 1539 :=
  logb3_2_gt 971 1539 (by omega) (by omega) (by norm_num : (3:ℝ)^971 < (2:ℝ)^1539)

-- c₁₀ = 15601/24727 < log3_2, for ξ₁₀ floor lower bound
lemma log3_2_gt_15601_24727 : Real.logb 3 2 > (15601:ℝ) / 24727 :=
  logb3_2_gt 15601 24727 (by omega) (by omega) (by norm_num : (3:ℝ)^15601 < (2:ℝ)^24727)

-- c₁₁ = 31867/50508 > log3_2, for ξ₁₁ floor
lemma log3_2_lt_31867_50508 : Real.logb 3 2 < (31867:ℝ) / 50508 :=
  logb3_2_lt 31867 50508 (by omega) (by omega) (by norm_num : (2:ℝ)^50508 < (3:ℝ)^31867)

-- Additional bound for ξ₁₁ upper
lemma log3_2_gt_47468_75235 : Real.logb 3 2 > (47468:ℝ) / 75235 :=
  logb3_2_gt 47468 75235 (by omega) (by omega) (by norm_num : (3:ℝ)^47468 < (2:ℝ)^75235)

-- c₁₂ = 79335/125743 < log3_2, for ξ₁₂ and ξ₁₃
lemma log3_2_gt_79335_125743 : Real.logb 3 2 > (79335:ℝ) / 125743 :=
  logb3_2_gt 79335 125743 (by omega) (by omega) (by norm_num : (3:ℝ)^79335 < (2:ℝ)^125743)

-- c₁₃ = 111202/176251 > log3_2, for ξ₁₃ upper and ξ₁₄
lemma log3_2_lt_111202_176251 : Real.logb 3 2 < (111202:ℝ) / 176251 :=
  logb3_2_lt 111202 176251 (by omega) (by omega) (by norm_num : (2:ℝ)^176251 < (3:ℝ)^111202)

-- c₁₄ = 190537/301994 < log3_2, for ξ₁₅
lemma log3_2_gt_190537_301994 : Real.logb 3 2 > (190537:ℝ) / 301994 :=
  logb3_2_gt 190537 301994 (by omega) (by omega) (by norm_num : (3:ℝ)^190537 < (2:ℝ)^301994)

-- Additional bounds for ξ₁₅ floor=55
lemma log3_2_lt_10590737_16785921 : Real.logb 3 2 < (10590737:ℝ) / 16785921 :=
  logb3_2_lt 10590737 16785921 (by omega) (by omega) (by norm_num : (2:ℝ)^16785921 < (3:ℝ)^10590737)

lemma log3_2_gt_10781274_17087915 : Real.logb 3 2 > (10781274:ℝ) / 17087915 :=
  logb3_2_gt 10781274 17087915 (by omega) (by omega) (by norm_num : (3:ℝ)^10781274 < (2:ℝ)^17087915)

-- Additional bounds for intermediate xi floors
-- ξ₁₀ upper: x < 16266/25781
lemma log3_2_lt_16266_25781 : Real.logb 3 2 < (16266:ℝ) / 25781 :=
  logb3_2_lt 16266 25781 (by omega) (by omega) (by norm_num : (2:ℝ)^25781 < (3:ℝ)^16266)

-- ξ₁₄ upper: x < 301739/478245
lemma log3_2_lt_301739_478245 : Real.logb 3 2 < (301739:ℝ) / 478245 :=
  logb3_2_lt 301739 478245 (by omega) (by omega) (by norm_num : (2:ℝ)^478245 < (3:ℝ)^301739)
