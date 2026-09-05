/-
  Rotation Decomposition

  Proves the fundamental identity relating Ostrowski representation to
  the fractional rotation:

    r * α = (Σ bₖ * Aₖ) + (Σ bₖ * εₖ)

  where:
    - bₖ are the Ostrowski coefficients of r
    - Aₖ = log3_2_cf.nums k are the convergent numerators
    - εₖ = Bₖ * α - Aₖ are the convergent errors (alternating, small)

  Since Σ bₖ * Aₖ is an integer, this gives:

    {r * α} = {Σ bₖ * εₖ}
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Irrational
import ErdosTernary.Ostrowski
import ErdosTernary.OstrowskiFormLemma
import ErdosTernary.ContinuedFraction.Log3
import ErdosTernary.LeadingDigits
import ErdosTernary.Log3Bounds

set_option lang.lemmaCmd true

namespace ErdosTernary.RotationDecomp

open ErdosTernary.Ostrowski
open ErdosTernary.OstrowskiFormLemma
open ErdosTernary.ContinuedFraction
open ErdosTernary.LeadingDigits

/-! ## Convergent Errors -/

/-- The convergent error: εₖ = Bₖ * α - Aₖ, where Aₖ, Bₖ are the continuants
    of the continued fraction of log₃(2). This equals Bₖ * (α - Aₖ/Bₖ). -/
noncomputable def epsilon (k : ℕ) : ℝ :=
  (log3_2_cf.dens k : ℝ) * α - (log3_2_cf.nums k : ℝ)

/-! ## Proved Lemmas -/

/-- dens k > 0 for all k. -/
theorem cf_dens_pos (k : ℕ) : 0 < (log3_2_cf.dens k : ℝ) := by
  have hmono : ∀ m, log3_2_cf.dens m ≤ log3_2_cf.dens (m + 1) :=
    fun m => GenContFract.of_den_mono
  have h1 : 1 ≤ log3_2_cf.dens k := by
    induction k with
    | zero => simp [GenContFract.zeroth_den_eq_one]
    | succ k ih => exact le_trans ih (hmono k)
  exact_mod_cast (lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) (by exact_mod_cast h1))

/-- Convergent error equals dens * (α - convs). -/
theorem epsilon_eq_mul_sub (k : ℕ) :
    epsilon k = (log3_2_cf.dens k : ℝ) * (α - log3_2_cf.convs k) := by
  simp only [epsilon, GenContFract.convs]
  have hd : (log3_2_cf.dens k : ℝ) ≠ 0 := ne_of_gt (cf_dens_pos k)
  field_simp
  ring

/-! ## Key Bridge Lemma -/

/-- The continued fraction numerators of GenContFract.of are integer-valued.
    Base: nums 0 = h = ⌊log₃(2)⌋ = 0 ∈ ℤ, nums 1 = 1 ∈ ℤ.
    Step: nums(k+2) = bₖ₊₁ * nums(k+1) + nums(k) ∈ ℤ by IH,
    since bₖ₊₁ ∈ ℤ (partial denominator of CF). -/
theorem nums_is_integer (k : ℕ) : ∃ z : ℤ, (z : ℝ) = (log3_2_cf.nums k : ℝ) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    cases k with
    | zero =>
      -- nums 0 = h = ⌊log₃(2)⌋ = 0
      use 0
      rw [show (log3_2_cf.nums 0 : ℝ) = (↑⌊log3_2⌋ : ℝ) from by
        rw [GenContFract.num_eq_conts_a, GenContFract.nth_cont_eq_succ_nth_contAux]
        show log3_2_cf.h = ↑⌊log3_2⌋
        unfold log3_2_cf; rw [GenContFract.of_h_eq_floor]]
      rw [log3_2_floor_eq_zero]
    | succ k =>
      cases k with
      | zero =>
        -- nums 1 = gp.b * h + gp.a where gp = s.get? 0, h = 0, gp.a = 1
        have ⟨gp, hgp⟩ : ∃ gp, log3_2_cf.s.get? 0 = some gp := by
          have hne : log3_2_cf.s.get? 0 ≠ none := fun h =>
            log3_2_not_terminatedAt 0 h
          exact Option.ne_none_iff_exists'.mp hne
        use 1
        rw [GenContFract.first_num_eq hgp,
          show log3_2_cf.h = (0:ℝ) from by
            unfold log3_2_cf; rw [GenContFract.of_h_eq_floor, log3_2_floor_eq_zero]; norm_cast]
        simp [(GenContFract.of_partNum_eq_one_and_exists_int_partDen_eq hgp).1]
      | succ k =>
        have ⟨gp, hgp⟩ : ∃ gp, log3_2_cf.s.get? (k + 1) = some gp := by
          have hne : log3_2_cf.s.get? (k + 1) ≠ none := fun h =>
            log3_2_not_terminatedAt (k + 1) h
          exact Option.ne_none_iff_exists'.mp hne
        obtain ⟨zk, hzk⟩ := ih k (by omega)
        obtain ⟨zk1, hzk1⟩ := ih (k + 1) (by omega)
        obtain ⟨zcoeff, hzcoeff⟩ := (GenContFract.of_partNum_eq_one_and_exists_int_partDen_eq hgp).2
        have ha := (GenContFract.of_partNum_eq_one_and_exists_int_partDen_eq hgp).1
        have hrec := GenContFract.nums_recurrence hgp rfl rfl
        -- hrec : log3_2_cf.nums (k + 2) = gp.b * log3_2_cf.nums (k + 1) + gp.a * log3_2_cf.nums k
        use zcoeff * zk1 + zk
        show (↑(zcoeff * zk1 + zk) : ℝ) = log3_2_cf.nums (k + 2)
        rw [hrec, ha, hzcoeff, ← hzk, ← hzk1]; push_cast; ring

/-- The continued fraction denominators of GenContFract.of are natural-valued.
    Proved by induction: dens 0 = 1, dens 1 = 1 (since h = ⌊log3_2⌋ = 0),
    and the recurrence only adds and multiplies naturals (partial numerators = 1,
    partial denominators ≥ 0). -/
theorem dens_is_natural (k : ℕ) : ∃ m : ℕ, (m : ℝ) = (log3_2_cf.dens k : ℝ) := by
  -- First prove dens is integer-valued
  have h_int : ∃ z : ℤ, (z : ℝ) = (log3_2_cf.dens k : ℝ) := by
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      cases k with
      | zero => exact ⟨1, by rw [GenContFract.zeroth_den_eq_one]; norm_cast⟩
      | succ k =>
        cases k with
        | zero =>
          have ⟨gp, hgp⟩ : ∃ gp, log3_2_cf.s.get? 0 = some gp := by
            have hne : log3_2_cf.s.get? 0 ≠ none := fun h =>
              log3_2_not_terminatedAt 0 h
            exact Option.ne_none_iff_exists'.mp hne
          obtain ⟨z, hz⟩ := (GenContFract.of_partNum_eq_one_and_exists_int_partDen_eq hgp).2
          exact ⟨z, by rw [GenContFract.first_den_eq hgp]; exact_mod_cast hz.symm⟩
        | succ k =>
          have ⟨gp, hgp⟩ : ∃ gp, log3_2_cf.s.get? (k + 1) = some gp := by
            have hne : log3_2_cf.s.get? (k + 1) ≠ none := fun h =>
              log3_2_not_terminatedAt (k + 1) h
            exact Option.ne_none_iff_exists'.mp hne
          obtain ⟨zk, hzk⟩ := ih k (by omega)
          obtain ⟨zk1, hzk1⟩ := ih (k + 1) (by omega)
          obtain ⟨zcoeff, hzcoeff⟩ := (GenContFract.of_partNum_eq_one_and_exists_int_partDen_eq hgp).2
          have ha := (GenContFract.of_partNum_eq_one_and_exists_int_partDen_eq hgp).1
          have hrec := GenContFract.dens_recurrence hgp rfl rfl
          exact ⟨zcoeff * zk1 + zk, by
            show (↑(zcoeff * zk1 + zk) : ℝ) = log3_2_cf.dens (k + 2)
            rw [show (↑(zcoeff * zk1 + zk) : ℝ) = ↑zcoeff * (↑zk1 : ℝ) + (↑zk : ℝ) from by push_cast; ring,
              hrec, ha, hzcoeff, ← hzk, ← hzk1]; push_cast; ring⟩
  -- Convert ℤ to ℕ using non-negativity
  obtain ⟨z, hz⟩ := h_int
  have hz_nonneg : 0 ≤ z := by
    have h := GenContFract.zero_le_of_contsAux_b (v := log3_2) (n := k + 1)
    -- h : 0 ≤ (GenContFract.of log3_2).contsAux (k+1)).b
    -- log3_2_cf = GenContFract.of log3_2, dens k = (contsAux (k+1)).b
    -- hz : ↑z = dens k = (contsAux (k+1)).b
    suffices (0 : ℝ) ≤ ↑z from by exact_mod_cast this
    rw [hz]
    rw [show (log3_2_cf.dens k : ℝ) = ((GenContFract.of log3_2).contsAux (k + 1)).b from by
      unfold log3_2_cf
      rw [GenContFract.den_eq_conts_b, GenContFract.nth_cont_eq_succ_nth_contAux]]
    exact_mod_cast h
  exact ⟨z.toNat, by
    rw [show (↑(z.toNat : ℕ) : ℝ) = (z.toNat : ℤ) from by norm_cast,
      Int.toNat_of_nonneg hz_nonneg]
    exact_mod_cast hz⟩

/-! ## Q Equals CF Dens -/

-- == Stream characterization helpers for log₃(2) CF ==

private lemma log3_2_fract_eq : Int.fract log3_2 = log3_2 := by
  rw [Int.fract_eq_iff]
  refine ⟨le_of_lt log3_2_pos, ErdosTernary.ContinuedFraction.log3_2_lt_one, ?_⟩
  exact ⟨0, by simp⟩

private lemma log3_2_fract_ne_zero : Int.fract log3_2 ≠ 0 := by
  intro h; apply ErdosTernary.ContinuedFraction.log3_2_irrational
  use (⌊log3_2⌋ : ℚ); push_cast; linarith [Int.fract_add_floor log3_2]

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

private lemma log3_2_gt_one_half : log3_2 > (1:ℝ) / 2 := by
  unfold log3_2; suffices h : (1 : ℝ) < 2 * Real.logb 3 2 from by linarith
  rw [show 2 * Real.logb 3 2 = Real.logb 3 4 from by
    rw [show (4:ℝ) = (2:ℝ)^2 from by norm_num, Real.logb_pow (by norm_num)]; push_cast; ring]
  have h33 : Real.logb 3 3 = 1 := Real.logb_self_eq_one (by norm_num : (1:ℝ) < 3)
  rw [show (1:ℝ) = Real.logb 3 3 from h33.symm]
  rw [Real.logb_lt_logb_iff (by norm_num : (1:ℝ) < 3) (by norm_num : (0:ℝ) < 3) (by norm_num : (0:ℝ) < 4)]
  norm_num

private lemma log3_2_lt_two_thirds : log3_2 < (2:ℝ) / 3 :=
  logb3_2_lt 2 3 (by omega) (by omega) (by norm_num : (2:ℝ)^3 < (3:ℝ)^2)

private lemma log3_2_inv_floor_one : ⌊(log3_2 : ℝ)⁻¹⌋ = 1 := by
  rw [Int.floor_eq_iff]; push_cast; constructor
  · rw [show (log3_2 : ℝ)⁻¹ = 1 / log3_2 from by field_simp [log3_2], le_div_iff₀ log3_2_pos]
    linarith [le_of_lt ErdosTernary.ContinuedFraction.log3_2_lt_one]
  · rw [show (log3_2 : ℝ)⁻¹ = 1 / log3_2 from by field_simp [log3_2], div_lt_iff log3_2_pos]
    linarith [log3_2_gt_one_half]

private lemma log3_2_inv_fract_eq : Int.fract (log3_2 : ℝ)⁻¹ = (log3_2 : ℝ)⁻¹ - 1 := by
  rw [Int.fract, log3_2_inv_floor_one]; norm_cast

private lemma log3_2_inv_fract_ne : Int.fract (log3_2 : ℝ)⁻¹ ≠ 0 := by
  rw [log3_2_inv_fract_eq]; intro h
  have : (log3_2 : ℝ)⁻¹ = 1 := by linarith
  rw [inv_eq_one] at this
  linarith [ErdosTernary.ContinuedFraction.log3_2_lt_one]

private lemma inv_inv_chain : (log3_2⁻¹ - 1 : ℝ)⁻¹ = log3_2 / (1 - log3_2) := by
  have hz : (log3_2 : ℝ) ≠ 0 := ne_of_gt log3_2_pos
  show _ = _
  field_simp

private lemma log3_2_inv_fract_floor : ⌊(Int.fract (log3_2 : ℝ)⁻¹)⁻¹⌋ = 1 := by
  rw [log3_2_inv_fract_eq, inv_inv_chain]
  rw [Int.floor_eq_iff]; push_cast; constructor
  · rw [le_div_iff₀ (sub_pos.mpr ErdosTernary.ContinuedFraction.log3_2_lt_one)]
    linarith [log3_2_gt_one_half]
  · rw [div_lt_iff (sub_pos.mpr ErdosTernary.ContinuedFraction.log3_2_lt_one)]
    linarith [log3_2_lt_two_thirds]

/-!
## Xi chain helpers for n ≥ 2

Reference table (x = log₃(2) ≈ 0.63093):

```
stream n | CF coeff aₙ₊₁ | complete quotient ξₙ              | ⌊ξₙ⌋ | (fract ξₙ)⁻¹ = ξₙ₊₁              | target = Al32(n+1)
---------|----------------|------------------------------------|-------|-------------------------------------|-------------------
0        | a₁ = 1         | ξ₀ = x                            | 0     | ξ₁ = 1/x                           | 1
1        | a₂ = 1         | ξ₁ = 1/x                          | 1     | ξ₂ = x/(1-x)                       | 1
2        | a₃ = 1         | ξ₂ = x/(1-x)                      | 1     | ξ₃ = (1-x)/(2x-1)                  | 1
3        | a₄ = 2         | ξ₃ = (1-x)/(2x-1)                 | 1     | ξ₄ = (2x-1)/(2-3x)                 | 2
4        | a₅ = 2         | ξ₄ = (2x-1)/(2-3x)                | 2     | ξ₅ = (2-3x)/(8x-5)                 | 2
5        | a₆ = 3         | ξ₅ = (2-3x)/(8x-5)                | 2     | ξ₆ = (8x-5)/(12-19x)               | 3
6        | a₇ = 1         | ξ₆ = (8x-5)/(12-19x)              | 3     | ξ₇ = (12-19x)/(65x-41)             | 1
7        | a₈ = 5         | ξ₇ = (12-19x)/(65x-41)            | 1     | ξ₈ = (65x-41)/(53-84x)             | 5
8        | a₉ = 2         | ξ₈ = (65x-41)/(53-84x)            | 5     | ξ₉ = (53-84x)/(485x-306)           | 2
9        | a₁₀ = 23       | ξ₉ = (53-84x)/(485x-306)          | 2     | ξ₁₀ = (485x-306)/(665-1054x)       | 23
10       | a₁₁ = 2        | ξ₁₀ = (485x-306)/(665-1054x)      | 23    | ξ₁₁ = (665-1054x)/(24727x-15601)   | 2
11       | a₁₂ = 2        | ξ₁₁ = (665-1054x)/(24727x-15601)  | 2     | ξ₁₂ = (24727x-15601)/(31867-50508x)| 2
12       | a₁₃ = 1        | ξ₁₂ = (24727x-15601)/(31867-50508x)| 2    | ξ₁₃ = (31867-50508x)/(125743x-79335)| 1
13       | a₁₄ = 1        | ξ₁₃ = (31867-50508x)/(125743x-79335)| 1   | ξ₁₄ = (125743x-79335)/(111202-176251x)| 1
14       | a₁₅ = 55       | ξ₁₄ = (125743x-79335)/(111202-176251x)| 1 | ξ₁₅ = (111202-176251x)/(301994x-190537)| 55
```

Key relationships:
- Al32 k = max 1 (log32_cf.getD k 0), so Al32(n+1) = max 1 (CF coeff aₙ₊₁)
- log32_cf = [0,1,1,1,2,2,3,1,5,2,23,2,2,1,1,55] (indices 0–15)
- s.get? n = some ⟨1, Al32(n+1)⟩ is what we prove
- Each xi_N_floor proves ⌊(fract ξ_{N-1})⁻¹⌋ = Al32 N

Proof strategy for each xi_N_floor:
1. Prove ⌊ξ_{N-1}⌋ = K using floor_eq_iff + convergent bounds on log₃(2)
2. Unfold Int.fract (= x - ⌊x⌋ by definition) and rewrite with hK
3. field_simp to simplify (ξ_{N-1} - K)⁻¹ to a fraction
4. Prove floor of that fraction = target using floor_eq_iff + bounds
-/

/-! ## Xi chain helpers for n ≥ 2 -/

-- Additional convergent bounds for earlier xi chain steps
private lemma log3_2_gt_three_fifths : log3_2 > (3:ℝ) / 5 :=
  logb3_2_gt 3 5 (by omega) (by omega) (by norm_num : (3:ℝ)^3 < (2:ℝ)^5)
private lemma log3_2_lt_seven_elevenths : log3_2 < (7:ℝ) / 11 :=
  logb3_2_lt 7 11 (by omega) (by omega) (by norm_num : (2:ℝ)^11 < (3:ℝ)^7)
private lemma log3_2_gt_five_eighths : log3_2 > (5:ℝ) / 8 :=
  logb3_2_gt 5 8 (by omega) (by omega) (by norm_num : (3:ℝ)^5 < (2:ℝ)^8)
private lemma log3_2_lt_twelve_nineteenths : log3_2 < (12:ℝ) / 19 :=
  logb3_2_lt 12 19 (by omega) (by omega) (by norm_num : (2:ℝ)^19 < (3:ℝ)^12)
private lemma log3_2_gt_seventeen_twentysevens : log3_2 > (17:ℝ) / 27 :=
  logb3_2_gt 17 27 (by omega) (by omega) (by norm_num : (3:ℝ)^17 < (2:ℝ)^27)
private lemma log3_2_gt_fortyone_sixtyfive : log3_2 > (41:ℝ) / 65 :=
  logb3_2_gt 41 65 (by omega) (by omega) (by norm_num : (3:ℝ)^41 < (2:ℝ)^65)
private lemma log3_2_lt_fiftythree_eightyfour : log3_2 < (53:ℝ) / 84 :=
  logb3_2_lt 53 84 (by omega) (by omega) (by norm_num : (2:ℝ)^84 < (3:ℝ)^53)
private lemma log3_2_gt_ninetyfour_hundredfortynine : log3_2 > (94:ℝ) / 149 :=
  logb3_2_gt 94 149 (by omega) (by omega) (by norm_num : (3:ℝ)^94 < (2:ℝ)^149)

-- Int.fract x = x - ⌊x⌋ by definition
private lemma fract_def (x : ℝ) : (Int.fract x : ℝ) = x - ⌊x⌋ := rfl

-- Wrappers for Log3Bounds lemmas stated in terms of log3_2 (not Real.logb 3 2)
-- so that linarith can use them directly
private lemma log3_2_gt_306_485' : log3_2 > (306:ℝ) / 485 := by exact log3_2_gt_306_485
private lemma log3_2_lt_665_1054' : log3_2 < (665:ℝ) / 1054 := by exact log3_2_lt_665_1054
private lemma log3_2_lt_359_569' : log3_2 < (359:ℝ) / 569 :=
  lt_trans log3_2_lt_665_1054' (by norm_num : (665:ℝ) / 1054 < 359 / 569)
private lemma log3_2_gt_971_1539' : log3_2 > (971:ℝ) / 1539 := by exact log3_2_gt_971_1539
private lemma log3_2_gt_15601_24727' : log3_2 > (15601:ℝ) / 24727 := by exact log3_2_gt_15601_24727
private lemma log3_2_lt_31867_50508' : log3_2 < (31867:ℝ) / 50508 := by exact log3_2_lt_31867_50508
private lemma log3_2_gt_47468_75235' : log3_2 > (47468:ℝ) / 75235 := by exact log3_2_gt_47468_75235
private lemma log3_2_gt_79335_125743' : log3_2 > (79335:ℝ) / 125743 := by exact log3_2_gt_79335_125743
private lemma log3_2_lt_111202_176251' : log3_2 < (111202:ℝ) / 176251 := by exact log3_2_lt_111202_176251
private lemma log3_2_gt_190537_301994' : log3_2 > (190537:ℝ) / 301994 := by exact log3_2_gt_190537_301994
private lemma log3_2_lt_10590737_16785921' : log3_2 < (10590737:ℝ) / 16785921 := by exact log3_2_lt_10590737_16785921
private lemma log3_2_gt_10781274_17087915' : log3_2 > (10781274:ℝ) / 17087915 := by exact log3_2_gt_10781274_17087915
private lemma log3_2_lt_16266_25781' : log3_2 < (16266:ℝ) / 25781 := by exact log3_2_lt_16266_25781
private lemma log3_2_lt_301739_478245' : log3_2 < (301739:ℝ) / 478245 := by exact log3_2_lt_301739_478245

-- == Position 2 (n=2): ξ₂ = x/(1-x), need ⌊(fract ξ₂)⁻¹⌋ = 1 ==

private lemma xi3_fract_eq : Int.fract (log3_2 / (1 - log3_2)) =
    (2 * log3_2 - 1) / (1 - log3_2) := by
  have h : ⌊(log3_2 / (1 - log3_2) : ℝ)⌋ = 1 := by
    rw [Int.floor_eq_iff]; push_cast; constructor
    · rw [le_div_iff₀ (sub_pos.mpr ErdosTernary.ContinuedFraction.log3_2_lt_one)]
      linarith [log3_2_gt_one_half]
    · rw [div_lt_iff (sub_pos.mpr ErdosTernary.ContinuedFraction.log3_2_lt_one)]
      linarith [log3_2_lt_two_thirds]
  have hne : (1 - log3_2 : ℝ) ≠ 0 := by linarith [ErdosTernary.ContinuedFraction.log3_2_lt_one]
  have hf : (Int.fract (log3_2 / (1 - log3_2)) : ℝ) = (2 * log3_2 - 1) / (1 - log3_2) := by
    rw [fract_def, h]; field_simp [hne]; ring
  exact hf

private lemma xi3_floor : ⌊(Int.fract (log3_2 / (1 - log3_2)))⁻¹⌋ = 1 := by
  rw [xi3_fract_eq]
  have hpos : 0 < (2 * log3_2 - 1 : ℝ) := by linarith [log3_2_gt_one_half]
  rw [Int.floor_eq_iff]; push_cast; simp only [inv_div]; constructor
  · rw [le_div_iff₀ hpos]; linarith [log3_2_lt_two_thirds]
  · rw [div_lt_iff hpos]; linarith [log3_2_gt_three_fifths]

private lemma xi3_fract_ne : Int.fract (log3_2 / (1 - log3_2)) ≠ 0 := by
  rw [xi3_fract_eq]; intro h
  have hp : 0 < (2 * log3_2 - 1 : ℝ) := by linarith [log3_2_gt_one_half]
  have hn : 0 < (1 - log3_2 : ℝ) := by linarith [ErdosTernary.ContinuedFraction.log3_2_lt_one]
  have : (0:ℝ) < (2 * log3_2 - 1) / (1 - log3_2) := div_pos hp hn
  linarith

-- == Position 3 (n=3): ξ₃ = (1-x)/(2x-1), need ⌊(fract ξ₃)⁻¹⌋ = 2 ==

private lemma xi4_floor : ⌊(Int.fract ((1 - log3_2) / (2 * log3_2 - 1)))⁻¹⌋ = 2 := by
  have hp : 0 < (2 * log3_2 - 1 : ℝ) := by linarith [log3_2_gt_one_half]
  have hK : ⌊(1 - log3_2) / (2 * log3_2 - 1 : ℝ)⌋ = 1 := by
    rw [Int.floor_eq_iff]; push_cast; constructor
    · rw [le_div_iff₀ hp]; linarith [log3_2_lt_two_thirds]
    · rw [div_lt_iff hp]; linarith [log3_2_gt_three_fifths]
  have hf : (Int.fract ((1 - log3_2) / (2 * log3_2 - 1)) : ℝ) = (2 - 3 * log3_2) / (2 * log3_2 - 1) := by
    rw [fract_def, hK]; field_simp [ne_of_gt hp]; ring
  rw [hf, inv_div]
  have hp2 : 0 < (2 * log3_2 - 1 : ℝ) := hp
  rw [Int.floor_eq_iff]; push_cast; constructor
  · rw [le_div_iff₀ (by linarith [log3_2_lt_two_thirds] : 0 < (2 - 3 * log3_2 : ℝ))]
    linarith [log3_2_gt_five_eighths]
  · rw [div_lt_iff (by linarith [log3_2_lt_two_thirds] : 0 < (2 - 3 * log3_2 : ℝ))]
    linarith [log3_2_lt_seven_elevenths]

private lemma xi4_fract_ne : Int.fract ((1 - log3_2) / (2 * log3_2 - 1)) ≠ 0 := by
  have hp : 0 < (2 * log3_2 - 1 : ℝ) := by linarith [log3_2_gt_one_half]
  have hK : ⌊(1 - log3_2) / (2 * log3_2 - 1 : ℝ)⌋ = 1 := by
    rw [Int.floor_eq_iff]; push_cast; constructor
    · rw [le_div_iff₀ hp]; linarith [log3_2_lt_two_thirds]
    · rw [div_lt_iff hp]; linarith [log3_2_gt_three_fifths]
  have hf : (Int.fract ((1 - log3_2) / (2 * log3_2 - 1)) : ℝ) = (2 - 3 * log3_2) / (2 * log3_2 - 1) := by
    rw [fract_def, hK]; field_simp [ne_of_gt hp]; ring
  rw [hf]; intro h
  have : (0:ℝ) < (2 - 3 * log3_2) / (2 * log3_2 - 1) := div_pos (by linarith [log3_2_lt_two_thirds]) hp
  linarith

-- == Position 4 (n=4): ξ₄ = (2x-1)/(2-3x), need ⌊(fract ξ₄)⁻¹⌋ = 2 ==

private lemma xi5_floor : ⌊(Int.fract ((2 * log3_2 - 1) / (2 - 3 * log3_2)))⁻¹⌋ = 2 := by
  have hp : 0 < (2 - 3 * log3_2 : ℝ) := by linarith [log3_2_lt_two_thirds]
  have hK : ⌊(2 * log3_2 - 1) / (2 - 3 * log3_2 : ℝ)⌋ = 2 := by
    rw [Int.floor_eq_iff]; push_cast; constructor
    · rw [le_div_iff₀ hp]; linarith [log3_2_gt_five_eighths]
    · rw [div_lt_iff hp]; linarith [log3_2_lt_seven_elevenths]
  have hf : (Int.fract ((2 * log3_2 - 1) / (2 - 3 * log3_2)) : ℝ) = (8 * log3_2 - 5) / (2 - 3 * log3_2) := by
    rw [fract_def, hK]; field_simp [ne_of_gt hp]; ring
  rw [hf, inv_div]
  have hp2 : 0 < (8 * log3_2 - 5 : ℝ) := by linarith [log3_2_gt_five_eighths]
  rw [Int.floor_eq_iff]; push_cast; constructor
  · rw [le_div_iff₀ hp2]; linarith [log3_2_lt_twelve_nineteenths]
  · rw [div_lt_iff hp2]; linarith [log3_2_gt_seventeen_twentysevens]

private lemma xi5_fract_ne : Int.fract ((2 * log3_2 - 1) / (2 - 3 * log3_2)) ≠ 0 := by
  have hp : 0 < (2 - 3 * log3_2 : ℝ) := by linarith [log3_2_lt_two_thirds]
  have hK : ⌊(2 * log3_2 - 1) / (2 - 3 * log3_2 : ℝ)⌋ = 2 := by
    rw [Int.floor_eq_iff]; push_cast; constructor
    · rw [le_div_iff₀ hp]; linarith [log3_2_gt_five_eighths]
    · rw [div_lt_iff hp]; linarith [log3_2_lt_seven_elevenths]
  have hf : (Int.fract ((2 * log3_2 - 1) / (2 - 3 * log3_2)) : ℝ) = (8 * log3_2 - 5) / (2 - 3 * log3_2) := by
    rw [fract_def, hK]; field_simp [ne_of_gt hp]; ring
  rw [hf]; intro h
  have : (0:ℝ) < (8 * log3_2 - 5) / (2 - 3 * log3_2) := div_pos (by linarith [log3_2_gt_five_eighths]) hp
  linarith

-- == Position 5 (n=5): ξ₅ = (2-3x)/(8x-5), need ⌊(fract ξ₅)⁻¹⌋ = 3 ==

private lemma xi6_floor : ⌊(Int.fract ((2 - 3 * log3_2) / (8 * log3_2 - 5)))⁻¹⌋ = 3 := by
  have hp : 0 < (8 * log3_2 - 5 : ℝ) := by linarith [log3_2_gt_five_eighths]
  have hK : ⌊(2 - 3 * log3_2) / (8 * log3_2 - 5 : ℝ)⌋ = 2 := by
    rw [Int.floor_eq_iff]; push_cast; constructor
    · rw [le_div_iff₀ hp]; linarith [log3_2_lt_twelve_nineteenths]
    · rw [div_lt_iff hp]; linarith [log3_2_gt_seventeen_twentysevens]
  have hf : (Int.fract ((2 - 3 * log3_2) / (8 * log3_2 - 5)) : ℝ) = (12 - 19 * log3_2) / (8 * log3_2 - 5) := by
    rw [fract_def, hK]; field_simp [ne_of_gt hp]; ring
  rw [hf, inv_div]
  have hp2 : 0 < (12 - 19 * log3_2 : ℝ) := by linarith [log3_2_lt_twelve_nineteenths]
  rw [Int.floor_eq_iff]; push_cast; constructor
  · rw [le_div_iff₀ hp2]; linarith [log3_2_gt_fortyone_sixtyfive]
  · rw [div_lt_iff hp2]; linarith [log3_2_lt_fiftythree_eightyfour]

private lemma xi6_fract_ne : Int.fract ((2 - 3 * log3_2) / (8 * log3_2 - 5)) ≠ 0 := by
  have hp : 0 < (8 * log3_2 - 5 : ℝ) := by linarith [log3_2_gt_five_eighths]
  have hK : ⌊(2 - 3 * log3_2) / (8 * log3_2 - 5 : ℝ)⌋ = 2 := by
    rw [Int.floor_eq_iff]; push_cast; constructor
    · rw [le_div_iff₀ hp]; linarith [log3_2_lt_twelve_nineteenths]
    · rw [div_lt_iff hp]; linarith [log3_2_gt_seventeen_twentysevens]
  have hf : (Int.fract ((2 - 3 * log3_2) / (8 * log3_2 - 5)) : ℝ) = (12 - 19 * log3_2) / (8 * log3_2 - 5) := by
    rw [fract_def, hK]; field_simp [ne_of_gt hp]; ring
  rw [hf]; intro h
  have : (0:ℝ) < (12 - 19 * log3_2) / (8 * log3_2 - 5) := div_pos (by linarith [log3_2_lt_twelve_nineteenths]) hp
  linarith

-- == Position 6 (n=6): ξ₆ = (8x-5)/(12-19x), need ⌊(fract ξ₆)⁻¹⌋ = 1 ==

private lemma xi7_floor : ⌊(Int.fract ((8 * log3_2 - 5) / (12 - 19 * log3_2)))⁻¹⌋ = 1 := by
  have hp : 0 < (12 - 19 * log3_2 : ℝ) := by linarith [log3_2_lt_twelve_nineteenths]
  have hK : ⌊(8 * log3_2 - 5) / (12 - 19 * log3_2 : ℝ)⌋ = 3 := by
    rw [Int.floor_eq_iff]; push_cast; constructor
    · rw [le_div_iff₀ hp]; linarith [log3_2_gt_fortyone_sixtyfive]
    · rw [div_lt_iff hp]; linarith [log3_2_lt_fiftythree_eightyfour]
  have hf : (Int.fract ((8 * log3_2 - 5) / (12 - 19 * log3_2)) : ℝ) = (65 * log3_2 - 41) / (12 - 19 * log3_2) := by
    rw [fract_def, hK]; field_simp [ne_of_gt hp]; ring
  rw [hf, inv_div]
  have hp2 : 0 < (65 * log3_2 - 41 : ℝ) := by linarith [log3_2_gt_fortyone_sixtyfive]
  rw [Int.floor_eq_iff]; push_cast; constructor
  · rw [le_div_iff₀ hp2]; linarith [log3_2_lt_fiftythree_eightyfour]
  · rw [div_lt_iff hp2]; linarith [log3_2_gt_ninetyfour_hundredfortynine]

private lemma xi7_fract_ne : Int.fract ((8 * log3_2 - 5) / (12 - 19 * log3_2)) ≠ 0 := by
  have hp : 0 < (12 - 19 * log3_2 : ℝ) := by linarith [log3_2_lt_twelve_nineteenths]
  have hK : ⌊(8 * log3_2 - 5) / (12 - 19 * log3_2 : ℝ)⌋ = 3 := by
    rw [Int.floor_eq_iff]; push_cast; constructor
    · rw [le_div_iff₀ hp]; linarith [log3_2_gt_fortyone_sixtyfive]
    · rw [div_lt_iff hp]; linarith [log3_2_lt_fiftythree_eightyfour]
  have hf : (Int.fract ((8 * log3_2 - 5) / (12 - 19 * log3_2)) : ℝ) = (65 * log3_2 - 41) / (12 - 19 * log3_2) := by
    rw [fract_def, hK]; field_simp [ne_of_gt hp]; ring
  rw [hf]; intro h
  have : (0:ℝ) < (65 * log3_2 - 41) / (12 - 19 * log3_2) := div_pos (by linarith [log3_2_gt_fortyone_sixtyfive]) hp
  linarith

-- == Position 7 (n=7): ξ₇ = (12-19x)/(65x-41), need ⌊(fract ξ₇)⁻¹⌋ = 5 ==

private lemma xi8_floor : ⌊(Int.fract ((12 - 19 * log3_2) / (65 * log3_2 - 41)))⁻¹⌋ = 5 := by
  have hp : 0 < (65 * log3_2 - 41 : ℝ) := by linarith [log3_2_gt_fortyone_sixtyfive]
  have hK : ⌊(12 - 19 * log3_2) / (65 * log3_2 - 41 : ℝ)⌋ = 1 := by
    rw [Int.floor_eq_iff]; push_cast; constructor
    · rw [le_div_iff₀ hp]; linarith [log3_2_lt_fiftythree_eightyfour]
    · rw [div_lt_iff hp]; linarith [log3_2_gt_ninetyfour_hundredfortynine]
  have hf : (Int.fract ((12 - 19 * log3_2) / (65 * log3_2 - 41)) : ℝ) = (53 - 84 * log3_2) / (65 * log3_2 - 41) := by
    rw [fract_def, hK]; field_simp [ne_of_gt hp]; ring
  rw [hf, inv_div]
  have hp2 : 0 < (53 - 84 * log3_2 : ℝ) := by linarith [log3_2_lt_fiftythree_eightyfour]
  rw [Int.floor_eq_iff]; push_cast; constructor
  · rw [le_div_iff₀ hp2]; linarith [log3_2_gt_306_485']
  · rw [div_lt_iff hp2]; linarith [log3_2_lt_359_569']

private lemma xi8_fract_ne : Int.fract ((12 - 19 * log3_2) / (65 * log3_2 - 41)) ≠ 0 := by
  have hp : 0 < (65 * log3_2 - 41 : ℝ) := by linarith [log3_2_gt_fortyone_sixtyfive]
  have hK : ⌊(12 - 19 * log3_2) / (65 * log3_2 - 41 : ℝ)⌋ = 1 := by
    rw [Int.floor_eq_iff]; push_cast; constructor
    · rw [le_div_iff₀ hp]; linarith [log3_2_lt_fiftythree_eightyfour]
    · rw [div_lt_iff hp]; linarith [log3_2_gt_ninetyfour_hundredfortynine]
  have hf : (Int.fract ((12 - 19 * log3_2) / (65 * log3_2 - 41)) : ℝ) = (53 - 84 * log3_2) / (65 * log3_2 - 41) := by
    rw [fract_def, hK]; field_simp [ne_of_gt hp]; ring
  rw [hf]; intro h
  have : (0:ℝ) < (53 - 84 * log3_2) / (65 * log3_2 - 41) := div_pos (by linarith [log3_2_lt_fiftythree_eightyfour]) hp
  linarith

-- == Position 8 (n=8): ξ₈ = (65x-41)/(53-84x), need ⌊(fract ξ₈)⁻¹⌋ = 2 ==

private lemma xi9_floor : ⌊(Int.fract ((65 * log3_2 - 41) / (53 - 84 * log3_2)))⁻¹⌋ = 2 := by
  have hp : 0 < (53 - 84 * log3_2 : ℝ) := by linarith [log3_2_lt_fiftythree_eightyfour]
  have hK : ⌊(65 * log3_2 - 41) / (53 - 84 * log3_2 : ℝ)⌋ = 5 := by
    rw [Int.floor_eq_iff]; push_cast; constructor
    · rw [le_div_iff₀ hp]; linarith [log3_2_gt_306_485']
    · rw [div_lt_iff hp]; linarith [log3_2_lt_359_569']
  have hf : (Int.fract ((65 * log3_2 - 41) / (53 - 84 * log3_2)) : ℝ) = (485 * log3_2 - 306) / (53 - 84 * log3_2) := by
    rw [fract_def, hK]; field_simp [ne_of_gt hp]; ring
  rw [hf, inv_div]
  have hp2 : 0 < (485 * log3_2 - 306 : ℝ) := by linarith [log3_2_gt_306_485']
  rw [Int.floor_eq_iff]; push_cast; constructor
  · rw [le_div_iff₀ hp2]; linarith [log3_2_lt_665_1054']
  · rw [div_lt_iff hp2]; linarith [log3_2_gt_971_1539']

private lemma xi9_fract_ne : Int.fract ((65 * log3_2 - 41) / (53 - 84 * log3_2)) ≠ 0 := by
  have hp : 0 < (53 - 84 * log3_2 : ℝ) := by linarith [log3_2_lt_fiftythree_eightyfour]
  have hK : ⌊(65 * log3_2 - 41) / (53 - 84 * log3_2 : ℝ)⌋ = 5 := by
    rw [Int.floor_eq_iff]; push_cast; constructor
    · rw [le_div_iff₀ hp]; linarith [log3_2_gt_306_485']
    · rw [div_lt_iff hp]; linarith [log3_2_lt_359_569']
  have hf : (Int.fract ((65 * log3_2 - 41) / (53 - 84 * log3_2)) : ℝ) = (485 * log3_2 - 306) / (53 - 84 * log3_2) := by
    rw [fract_def, hK]; field_simp [ne_of_gt hp]; ring
  rw [hf]; intro h
  have : (0:ℝ) < (485 * log3_2 - 306) / (53 - 84 * log3_2) := div_pos (by linarith [log3_2_gt_306_485']) hp
  linarith

-- == Position 9 (n=9): ξ₉ = (53-84x)/(485x-306), need ⌊(fract ξ₉)⁻¹⌋ = 23 ==

private lemma xi10_floor : ⌊(Int.fract ((53 - 84 * log3_2) / (485 * log3_2 - 306)))⁻¹⌋ = 23 := by
  have hp : 0 < (485 * log3_2 - 306 : ℝ) := by linarith [log3_2_gt_306_485']
  have hK : ⌊(53 - 84 * log3_2) / (485 * log3_2 - 306 : ℝ)⌋ = 2 := by
    rw [Int.floor_eq_iff]; push_cast; constructor
    · rw [le_div_iff₀ hp]; linarith [log3_2_lt_665_1054']
    · rw [div_lt_iff hp]; linarith [log3_2_gt_971_1539']
  have hf : (Int.fract ((53 - 84 * log3_2) / (485 * log3_2 - 306)) : ℝ) = (665 - 1054 * log3_2) / (485 * log3_2 - 306) := by
    rw [fract_def, hK]; field_simp [ne_of_gt hp]; ring
  rw [hf, inv_div]
  have hp2 : 0 < (665 - 1054 * log3_2 : ℝ) := by linarith [log3_2_lt_665_1054']
  rw [Int.floor_eq_iff]; push_cast; constructor
  · rw [le_div_iff₀ hp2]; linarith [log3_2_gt_15601_24727']
  · rw [div_lt_iff hp2]; linarith [log3_2_lt_16266_25781']

private lemma xi10_fract_ne : Int.fract ((53 - 84 * log3_2) / (485 * log3_2 - 306)) ≠ 0 := by
  have hp : 0 < (485 * log3_2 - 306 : ℝ) := by linarith [log3_2_gt_306_485']
  have hK : ⌊(53 - 84 * log3_2) / (485 * log3_2 - 306 : ℝ)⌋ = 2 := by
    rw [Int.floor_eq_iff]; push_cast; constructor
    · rw [le_div_iff₀ hp]; linarith [log3_2_lt_665_1054']
    · rw [div_lt_iff hp]; linarith [log3_2_gt_971_1539']
  have hf : (Int.fract ((53 - 84 * log3_2) / (485 * log3_2 - 306)) : ℝ) = (665 - 1054 * log3_2) / (485 * log3_2 - 306) := by
    rw [fract_def, hK]; field_simp [ne_of_gt hp]; ring
  rw [hf]; intro h
  have : (0:ℝ) < (665 - 1054 * log3_2) / (485 * log3_2 - 306) := div_pos (by linarith [log3_2_lt_665_1054']) hp
  linarith

-- == Position 10 (n=10): ξ₁₀ = (485x-306)/(665-1054x), need ⌊(fract ξ₁₀)⁻¹⌋ = 2 ==

private lemma xi11_floor : ⌊(Int.fract ((485 * log3_2 - 306) / (665 - 1054 * log3_2)))⁻¹⌋ = 2 := by
  have hp : 0 < (665 - 1054 * log3_2 : ℝ) := by linarith [log3_2_lt_665_1054']
  have hK : ⌊(485 * log3_2 - 306) / (665 - 1054 * log3_2 : ℝ)⌋ = 23 := by
    rw [Int.floor_eq_iff]; push_cast; constructor
    · rw [le_div_iff₀ hp]; linarith [log3_2_gt_15601_24727']
    · rw [div_lt_iff hp]; linarith [log3_2_lt_16266_25781']
  have hf : (Int.fract ((485 * log3_2 - 306) / (665 - 1054 * log3_2)) : ℝ) = (24727 * log3_2 - 15601) / (665 - 1054 * log3_2) := by
    rw [fract_def, hK]; field_simp [ne_of_gt hp]; ring
  rw [hf, inv_div]
  have hp2 : 0 < (24727 * log3_2 - 15601 : ℝ) := by linarith [log3_2_gt_15601_24727']
  rw [Int.floor_eq_iff]; push_cast; constructor
  · rw [le_div_iff₀ hp2]; linarith [log3_2_lt_31867_50508']
  · rw [div_lt_iff hp2]; linarith [log3_2_gt_47468_75235']

private lemma xi11_fract_ne : Int.fract ((485 * log3_2 - 306) / (665 - 1054 * log3_2)) ≠ 0 := by
  have hp : 0 < (665 - 1054 * log3_2 : ℝ) := by linarith [log3_2_lt_665_1054']
  have hK : ⌊(485 * log3_2 - 306) / (665 - 1054 * log3_2 : ℝ)⌋ = 23 := by
    rw [Int.floor_eq_iff]; push_cast; constructor
    · rw [le_div_iff₀ hp]; linarith [log3_2_gt_15601_24727']
    · rw [div_lt_iff hp]; linarith [log3_2_lt_16266_25781']
  have hf : (Int.fract ((485 * log3_2 - 306) / (665 - 1054 * log3_2)) : ℝ) = (24727 * log3_2 - 15601) / (665 - 1054 * log3_2) := by
    rw [fract_def, hK]; field_simp [ne_of_gt hp]; ring
  rw [hf]; intro h
  have : (0:ℝ) < (24727 * log3_2 - 15601) / (665 - 1054 * log3_2) := div_pos (by linarith [log3_2_gt_15601_24727']) hp
  linarith

-- == Position 11 (n=11): ξ₁₁ = (665-1054x)/(24727x-15601), need ⌊(fract ξ₁₁)⁻¹⌋ = 2 ==

private lemma xi12_floor : ⌊(Int.fract ((665 - 1054 * log3_2) / (24727 * log3_2 - 15601)))⁻¹⌋ = 2 := by
  have hp : 0 < (24727 * log3_2 - 15601 : ℝ) := by linarith [log3_2_gt_15601_24727']
  have hK : ⌊(665 - 1054 * log3_2) / (24727 * log3_2 - 15601 : ℝ)⌋ = 2 := by
    rw [Int.floor_eq_iff]; push_cast; constructor
    · rw [le_div_iff₀ hp]; linarith [log3_2_lt_31867_50508']
    · rw [div_lt_iff hp]; linarith [log3_2_gt_47468_75235']
  have hf : (Int.fract ((665 - 1054 * log3_2) / (24727 * log3_2 - 15601)) : ℝ) = (31867 - 50508 * log3_2) / (24727 * log3_2 - 15601) := by
    rw [fract_def, hK]; field_simp [ne_of_gt hp]; ring
  rw [hf, inv_div]
  have hp2 : 0 < (31867 - 50508 * log3_2 : ℝ) := by linarith [log3_2_lt_31867_50508']
  rw [Int.floor_eq_iff]; push_cast; constructor
  · rw [le_div_iff₀ hp2]; linarith [log3_2_gt_79335_125743']
  · rw [div_lt_iff hp2]; linarith [log3_2_lt_111202_176251']

private lemma xi12_fract_ne : Int.fract ((665 - 1054 * log3_2) / (24727 * log3_2 - 15601)) ≠ 0 := by
  have hp : 0 < (24727 * log3_2 - 15601 : ℝ) := by linarith [log3_2_gt_15601_24727']
  have hK : ⌊(665 - 1054 * log3_2) / (24727 * log3_2 - 15601 : ℝ)⌋ = 2 := by
    rw [Int.floor_eq_iff]; push_cast; constructor
    · rw [le_div_iff₀ hp]; linarith [log3_2_lt_31867_50508']
    · rw [div_lt_iff hp]; linarith [log3_2_gt_47468_75235']
  have hf : (Int.fract ((665 - 1054 * log3_2) / (24727 * log3_2 - 15601)) : ℝ) = (31867 - 50508 * log3_2) / (24727 * log3_2 - 15601) := by
    rw [fract_def, hK]; field_simp [ne_of_gt hp]; ring
  rw [hf]; intro h
  have : (0:ℝ) < (31867 - 50508 * log3_2) / (24727 * log3_2 - 15601) := div_pos (by linarith [log3_2_lt_31867_50508']) hp
  linarith

-- == Position 12 (n=12): ξ₁₂ = (24727x-15601)/(31867-50508x), need ⌊(fract ξ₁₂)⁻¹⌋ = 1 ==

private lemma xi13_floor : ⌊(Int.fract ((24727 * log3_2 - 15601) / (31867 - 50508 * log3_2)))⁻¹⌋ = 1 := by
  have hp : 0 < (31867 - 50508 * log3_2 : ℝ) := by linarith [log3_2_lt_31867_50508']
  have hK : ⌊(24727 * log3_2 - 15601) / (31867 - 50508 * log3_2 : ℝ)⌋ = 2 := by
    rw [Int.floor_eq_iff]; push_cast; constructor
    · rw [le_div_iff₀ hp]; linarith [log3_2_gt_79335_125743']
    · rw [div_lt_iff hp]; linarith [log3_2_lt_111202_176251']
  have hf : (Int.fract ((24727 * log3_2 - 15601) / (31867 - 50508 * log3_2)) : ℝ) = (125743 * log3_2 - 79335) / (31867 - 50508 * log3_2) := by
    rw [fract_def, hK]; field_simp [ne_of_gt hp]; ring
  rw [hf, inv_div]
  have hp2 : 0 < (125743 * log3_2 - 79335 : ℝ) := by linarith [log3_2_gt_79335_125743']
  rw [Int.floor_eq_iff]; push_cast; constructor
  · rw [le_div_iff₀ hp2]; linarith [log3_2_lt_111202_176251']
  · rw [div_lt_iff hp2]; linarith [log3_2_gt_190537_301994']

private lemma xi13_fract_ne : Int.fract ((24727 * log3_2 - 15601) / (31867 - 50508 * log3_2)) ≠ 0 := by
  have hp : 0 < (31867 - 50508 * log3_2 : ℝ) := by linarith [log3_2_lt_31867_50508']
  have hK : ⌊(24727 * log3_2 - 15601) / (31867 - 50508 * log3_2 : ℝ)⌋ = 2 := by
    rw [Int.floor_eq_iff]; push_cast; constructor
    · rw [le_div_iff₀ hp]; linarith [log3_2_gt_79335_125743']
    · rw [div_lt_iff hp]; linarith [log3_2_lt_111202_176251']
  have hf : (Int.fract ((24727 * log3_2 - 15601) / (31867 - 50508 * log3_2)) : ℝ) = (125743 * log3_2 - 79335) / (31867 - 50508 * log3_2) := by
    rw [fract_def, hK]; field_simp [ne_of_gt hp]; ring
  rw [hf]; intro h
  have : (0:ℝ) < (125743 * log3_2 - 79335) / (31867 - 50508 * log3_2) := div_pos (by linarith [log3_2_gt_79335_125743']) hp
  linarith

-- == Position 13 (n=13): ξ₁₃ = (31867-50508x)/(125743x-79335), need ⌊(fract ξ₁₃)⁻¹⌋ = 1 ==

private lemma xi14_floor : ⌊(Int.fract ((31867 - 50508 * log3_2) / (125743 * log3_2 - 79335)))⁻¹⌋ = 1 := by
  have hp : 0 < (125743 * log3_2 - 79335 : ℝ) := by linarith [log3_2_gt_79335_125743']
  have hK : ⌊(31867 - 50508 * log3_2) / (125743 * log3_2 - 79335 : ℝ)⌋ = 1 := by
    rw [Int.floor_eq_iff]; push_cast; constructor
    · rw [le_div_iff₀ hp]; linarith [log3_2_lt_111202_176251']
    · rw [div_lt_iff hp]; linarith [log3_2_gt_190537_301994']
  have hf : (Int.fract ((31867 - 50508 * log3_2) / (125743 * log3_2 - 79335)) : ℝ) = (111202 - 176251 * log3_2) / (125743 * log3_2 - 79335) := by
    rw [fract_def, hK]; field_simp [ne_of_gt hp]; ring
  rw [hf, inv_div]
  have hp2 : 0 < (111202 - 176251 * log3_2 : ℝ) := by linarith [log3_2_lt_111202_176251']
  rw [Int.floor_eq_iff]; push_cast; constructor
  · rw [le_div_iff₀ hp2]; linarith [log3_2_gt_190537_301994']
  · rw [div_lt_iff hp2]; linarith [log3_2_lt_301739_478245']

private lemma xi14_fract_ne : Int.fract ((31867 - 50508 * log3_2) / (125743 * log3_2 - 79335)) ≠ 0 := by
  have hp : 0 < (125743 * log3_2 - 79335 : ℝ) := by linarith [log3_2_gt_79335_125743']
  have hK : ⌊(31867 - 50508 * log3_2) / (125743 * log3_2 - 79335 : ℝ)⌋ = 1 := by
    rw [Int.floor_eq_iff]; push_cast; constructor
    · rw [le_div_iff₀ hp]; linarith [log3_2_lt_111202_176251']
    · rw [div_lt_iff hp]; linarith [log3_2_gt_190537_301994']
  have hf : (Int.fract ((31867 - 50508 * log3_2) / (125743 * log3_2 - 79335)) : ℝ) = (111202 - 176251 * log3_2) / (125743 * log3_2 - 79335) := by
    rw [fract_def, hK]; field_simp [ne_of_gt hp]; ring
  rw [hf]; intro h
  have : (0:ℝ) < (111202 - 176251 * log3_2) / (125743 * log3_2 - 79335) := div_pos (by linarith [log3_2_lt_111202_176251']) hp
  linarith

-- == Position 14 (n=14): ξ₁₄ = (125743x-79335)/(111202-176251x), need ⌊(fract ξ₁₄)⁻¹⌋ = 55 ==

private lemma xi15_floor : ⌊(Int.fract ((125743 * log3_2 - 79335) / (111202 - 176251 * log3_2)))⁻¹⌋ = 55 := by
  have hp : 0 < (111202 - 176251 * log3_2 : ℝ) := by linarith [log3_2_lt_111202_176251']
  have hK : ⌊(125743 * log3_2 - 79335) / (111202 - 176251 * log3_2 : ℝ)⌋ = 1 := by
    rw [Int.floor_eq_iff]; push_cast; constructor
    · rw [le_div_iff₀ hp]; linarith [log3_2_gt_190537_301994']
    · rw [div_lt_iff hp]; linarith [log3_2_lt_301739_478245']
  have hf : (Int.fract ((125743 * log3_2 - 79335) / (111202 - 176251 * log3_2)) : ℝ) = (301994 * log3_2 - 190537) / (111202 - 176251 * log3_2) := by
    rw [fract_def, hK]; field_simp [ne_of_gt hp]; ring
  rw [hf, inv_div]
  have hp2 : 0 < (301994 * log3_2 - 190537 : ℝ) := by linarith [log3_2_gt_190537_301994']
  rw [Int.floor_eq_iff]; push_cast; constructor
  · rw [le_div_iff₀ hp2]; linarith [log3_2_lt_10590737_16785921']
  · rw [div_lt_iff hp2]; linarith [log3_2_gt_10781274_17087915']

private lemma xi15_fract_ne : Int.fract ((125743 * log3_2 - 79335) / (111202 - 176251 * log3_2)) ≠ 0 := by
  have hp : 0 < (111202 - 176251 * log3_2 : ℝ) := by linarith [log3_2_lt_111202_176251']
  have hK : ⌊(125743 * log3_2 - 79335) / (111202 - 176251 * log3_2 : ℝ)⌋ = 1 := by
    rw [Int.floor_eq_iff]; push_cast; constructor
    · rw [le_div_iff₀ hp]; linarith [log3_2_gt_190537_301994']
    · rw [div_lt_iff hp]; linarith [log3_2_lt_301739_478245']
  have hf : (Int.fract ((125743 * log3_2 - 79335) / (111202 - 176251 * log3_2)) : ℝ) = (301994 * log3_2 - 190537) / (111202 - 176251 * log3_2) := by
    rw [fract_def, hK]; field_simp [ne_of_gt hp]; ring
  rw [hf]; intro h
  have : (0:ℝ) < (301994 * log3_2 - 190537) / (111202 - 176251 * log3_2) := div_pos (by linarith [log3_2_gt_190537_301994']) hp
  linarith

-- N=0
private theorem log3_2_cf_stream_zero :
    log3_2_cf.s.get? 0 = some ⟨1, (Al32 1 : ℝ)⟩ := by
  unfold log3_2_cf
  rw [GenContFract.of_s_head_aux]
  rw [show (1 : ℕ) = 0 + 1 from by omega]
  rw [GenContFract.IntFractPair.stream_succ_of_some
    (GenContFract.IntFractPair.stream_zero log3_2) log3_2_fract_ne_zero]
  simp only [Option.bind_some, Function.comp_apply, GenContFract.IntFractPair.of]
  rw [log3_2_fract_eq, log3_2_inv_floor_one]
  simp [Al32, ErdosTernary.Ostrowski.log32_cf, List.getD]

-- N=1
private theorem log3_2_cf_stream_one :
    log3_2_cf.s.get? 1 = some ⟨1, (Al32 2 : ℝ)⟩ := by
  unfold log3_2_cf
  rw [GenContFract.of_s_succ log3_2 0]
  rw [show Int.fract log3_2 = log3_2 from log3_2_fract_eq]
  rw [GenContFract.of_s_head_aux]
  rw [show (1 : ℕ) = 0 + 1 from by omega]
  rw [GenContFract.IntFractPair.stream_succ_of_some
    (GenContFract.IntFractPair.stream_zero log3_2⁻¹) log3_2_inv_fract_ne]
  simp only [Option.bind_some, Function.comp_apply, GenContFract.IntFractPair.of]
  rw [log3_2_inv_fract_floor]
  simp [Al32, ErdosTernary.Ostrowski.log32_cf, List.getD]

private lemma xi2_eq : (Int.fract (log3_2 : ℝ)⁻¹)⁻¹ = log3_2 / (1 - log3_2) := by
  rw [fract_def]
  have hf : ⌊(log3_2 : ℝ)⁻¹⌋ = 1 := by exact log3_2_inv_floor_one
  rw [hf]; push_cast; field_simp [ne_of_gt ErdosTernary.ContinuedFraction.log3_2_pos]

private lemma xi3_eq : (Int.fract (log3_2 / (1 - log3_2)) : ℝ)⁻¹ = (1 - log3_2) / (2 * log3_2 - 1) := by
  rw [xi3_fract_eq]; field_simp

private lemma xi4_eq : (Int.fract ((1 - log3_2) / (2 * log3_2 - 1)) : ℝ)⁻¹ = (2 * log3_2 - 1) / (2 - 3 * log3_2) := by
  have hp : 0 < (2 * log3_2 - 1 : ℝ) := by linarith [log3_2_gt_one_half]
  have hK : ⌊(1 - log3_2) / (2 * log3_2 - 1 : ℝ)⌋ = 1 := by
    rw [Int.floor_eq_iff]; push_cast; constructor
    · rw [le_div_iff₀ hp]; linarith [log3_2_lt_two_thirds]
    · rw [div_lt_iff hp]; linarith [log3_2_gt_three_fifths]
  have hf : (Int.fract ((1 - log3_2) / (2 * log3_2 - 1)) : ℝ) = (2 - 3 * log3_2) / (2 * log3_2 - 1) := by
    rw [fract_def, hK]; field_simp [ne_of_gt hp]; ring
  rw [hf]; field_simp

private lemma xi5_eq : (Int.fract ((2 * log3_2 - 1) / (2 - 3 * log3_2)) : ℝ)⁻¹ = (2 - 3 * log3_2) / (8 * log3_2 - 5) := by
  have hp : 0 < (2 - 3 * log3_2 : ℝ) := by linarith [log3_2_lt_two_thirds]
  have hK : ⌊(2 * log3_2 - 1) / (2 - 3 * log3_2 : ℝ)⌋ = 2 := by
    rw [Int.floor_eq_iff]; push_cast; constructor
    · rw [le_div_iff₀ hp]; linarith [log3_2_gt_five_eighths]
    · rw [div_lt_iff hp]; linarith [log3_2_lt_seven_elevenths]
  have hf : (Int.fract ((2 * log3_2 - 1) / (2 - 3 * log3_2)) : ℝ) = (8 * log3_2 - 5) / (2 - 3 * log3_2) := by
    rw [fract_def, hK]; field_simp [ne_of_gt hp]; ring
  rw [hf]; field_simp

private lemma xi6_eq : (Int.fract ((2 - 3 * log3_2) / (8 * log3_2 - 5)) : ℝ)⁻¹ = (8 * log3_2 - 5) / (12 - 19 * log3_2) := by
  have hp : 0 < (8 * log3_2 - 5 : ℝ) := by linarith [log3_2_gt_five_eighths]
  have hK : ⌊(2 - 3 * log3_2) / (8 * log3_2 - 5 : ℝ)⌋ = 2 := by
    rw [Int.floor_eq_iff]; push_cast; constructor
    · rw [le_div_iff₀ hp]; linarith [log3_2_lt_twelve_nineteenths]
    · rw [div_lt_iff hp]; linarith [log3_2_gt_seventeen_twentysevens]
  have hf : (Int.fract ((2 - 3 * log3_2) / (8 * log3_2 - 5)) : ℝ) = (12 - 19 * log3_2) / (8 * log3_2 - 5) := by
    rw [fract_def, hK]; field_simp [ne_of_gt hp]; ring
  rw [hf]; field_simp

private lemma xi7_eq : (Int.fract ((8 * log3_2 - 5) / (12 - 19 * log3_2)) : ℝ)⁻¹ = (12 - 19 * log3_2) / (65 * log3_2 - 41) := by
  have hp : 0 < (12 - 19 * log3_2 : ℝ) := by linarith [log3_2_lt_twelve_nineteenths]
  have hK : ⌊(8 * log3_2 - 5) / (12 - 19 * log3_2 : ℝ)⌋ = 3 := by
    rw [Int.floor_eq_iff]; push_cast; constructor
    · rw [le_div_iff₀ hp]; linarith [log3_2_gt_fortyone_sixtyfive]
    · rw [div_lt_iff hp]; linarith [log3_2_lt_fiftythree_eightyfour]
  have hf : (Int.fract ((8 * log3_2 - 5) / (12 - 19 * log3_2)) : ℝ) = (65 * log3_2 - 41) / (12 - 19 * log3_2) := by
    rw [fract_def, hK]; field_simp [ne_of_gt hp]; ring
  rw [hf]; field_simp

private lemma xi8_eq : (Int.fract ((12 - 19 * log3_2) / (65 * log3_2 - 41)) : ℝ)⁻¹ = (65 * log3_2 - 41) / (53 - 84 * log3_2) := by
  have hp : 0 < (65 * log3_2 - 41 : ℝ) := by linarith [log3_2_gt_fortyone_sixtyfive]
  have hK : ⌊(12 - 19 * log3_2) / (65 * log3_2 - 41 : ℝ)⌋ = 1 := by
    rw [Int.floor_eq_iff]; push_cast; constructor
    · rw [le_div_iff₀ hp]; linarith [log3_2_lt_fiftythree_eightyfour]
    · rw [div_lt_iff hp]; linarith [log3_2_gt_ninetyfour_hundredfortynine]
  have hf : (Int.fract ((12 - 19 * log3_2) / (65 * log3_2 - 41)) : ℝ) = (53 - 84 * log3_2) / (65 * log3_2 - 41) := by
    rw [fract_def, hK]; field_simp [ne_of_gt hp]; ring
  rw [hf]; field_simp

private lemma xi9_eq : (Int.fract ((65 * log3_2 - 41) / (53 - 84 * log3_2)) : ℝ)⁻¹ = (53 - 84 * log3_2) / (485 * log3_2 - 306) := by
  have hp : 0 < (53 - 84 * log3_2 : ℝ) := by linarith [log3_2_lt_fiftythree_eightyfour]
  have hK : ⌊(65 * log3_2 - 41) / (53 - 84 * log3_2 : ℝ)⌋ = 5 := by
    rw [Int.floor_eq_iff]; push_cast; constructor
    · rw [le_div_iff₀ hp]; linarith [log3_2_gt_306_485']
    · rw [div_lt_iff hp]; linarith [log3_2_lt_359_569']
  have hf : (Int.fract ((65 * log3_2 - 41) / (53 - 84 * log3_2)) : ℝ) = (485 * log3_2 - 306) / (53 - 84 * log3_2) := by
    rw [fract_def, hK]; field_simp [ne_of_gt hp]; ring
  rw [hf]; field_simp

private lemma xi10_eq : (Int.fract ((53 - 84 * log3_2) / (485 * log3_2 - 306)) : ℝ)⁻¹ = (485 * log3_2 - 306) / (665 - 1054 * log3_2) := by
  have hp : 0 < (485 * log3_2 - 306 : ℝ) := by linarith [log3_2_gt_306_485']
  have hK : ⌊(53 - 84 * log3_2) / (485 * log3_2 - 306 : ℝ)⌋ = 2 := by
    rw [Int.floor_eq_iff]; push_cast; constructor
    · rw [le_div_iff₀ hp]; linarith [log3_2_lt_665_1054']
    · rw [div_lt_iff hp]; linarith [log3_2_gt_971_1539']
  have hf : (Int.fract ((53 - 84 * log3_2) / (485 * log3_2 - 306)) : ℝ) = (665 - 1054 * log3_2) / (485 * log3_2 - 306) := by
    rw [fract_def, hK]; field_simp [ne_of_gt hp]; ring
  rw [hf]; field_simp

private lemma xi11_eq : (Int.fract ((485 * log3_2 - 306) / (665 - 1054 * log3_2)) : ℝ)⁻¹ = (665 - 1054 * log3_2) / (24727 * log3_2 - 15601) := by
  have hp : 0 < (665 - 1054 * log3_2 : ℝ) := by linarith [log3_2_lt_665_1054']
  have hK : ⌊(485 * log3_2 - 306) / (665 - 1054 * log3_2 : ℝ)⌋ = 23 := by
    rw [Int.floor_eq_iff]; push_cast; constructor
    · rw [le_div_iff₀ hp]; linarith [log3_2_gt_15601_24727']
    · rw [div_lt_iff hp]; linarith [log3_2_lt_16266_25781']
  have hf : (Int.fract ((485 * log3_2 - 306) / (665 - 1054 * log3_2)) : ℝ) = (24727 * log3_2 - 15601) / (665 - 1054 * log3_2) := by
    rw [fract_def, hK]; field_simp [ne_of_gt hp]; ring
  rw [hf]; field_simp

private lemma xi12_eq : (Int.fract ((665 - 1054 * log3_2) / (24727 * log3_2 - 15601)) : ℝ)⁻¹ = (24727 * log3_2 - 15601) / (31867 - 50508 * log3_2) := by
  have hp : 0 < (24727 * log3_2 - 15601 : ℝ) := by linarith [log3_2_gt_15601_24727']
  have hK : ⌊(665 - 1054 * log3_2) / (24727 * log3_2 - 15601 : ℝ)⌋ = 2 := by
    rw [Int.floor_eq_iff]; push_cast; constructor
    · rw [le_div_iff₀ hp]; linarith [log3_2_lt_31867_50508']
    · rw [div_lt_iff hp]; linarith [log3_2_gt_47468_75235']
  have hf : (Int.fract ((665 - 1054 * log3_2) / (24727 * log3_2 - 15601)) : ℝ) = (31867 - 50508 * log3_2) / (24727 * log3_2 - 15601) := by
    rw [fract_def, hK]; field_simp [ne_of_gt hp]; ring
  rw [hf]; field_simp

private lemma xi13_eq : (Int.fract ((24727 * log3_2 - 15601) / (31867 - 50508 * log3_2)) : ℝ)⁻¹ = (31867 - 50508 * log3_2) / (125743 * log3_2 - 79335) := by
  have hp : 0 < (31867 - 50508 * log3_2 : ℝ) := by linarith [log3_2_lt_31867_50508']
  have hK : ⌊(24727 * log3_2 - 15601) / (31867 - 50508 * log3_2 : ℝ)⌋ = 2 := by
    rw [Int.floor_eq_iff]; push_cast; constructor
    · rw [le_div_iff₀ hp]; linarith [log3_2_gt_79335_125743']
    · rw [div_lt_iff hp]; linarith [log3_2_lt_111202_176251']
  have hf : (Int.fract ((24727 * log3_2 - 15601) / (31867 - 50508 * log3_2)) : ℝ) = (125743 * log3_2 - 79335) / (31867 - 50508 * log3_2) := by
    rw [fract_def, hK]; field_simp [ne_of_gt hp]; ring
  rw [hf]; field_simp

private lemma xi14_eq : (Int.fract ((31867 - 50508 * log3_2) / (125743 * log3_2 - 79335)) : ℝ)⁻¹ = (125743 * log3_2 - 79335) / (111202 - 176251 * log3_2) := by
  have hp : 0 < (125743 * log3_2 - 79335 : ℝ) := by linarith [log3_2_gt_79335_125743']
  have hK : ⌊(31867 - 50508 * log3_2) / (125743 * log3_2 - 79335 : ℝ)⌋ = 1 := by
    rw [Int.floor_eq_iff]; push_cast; constructor
    · rw [le_div_iff₀ hp]; linarith [log3_2_lt_111202_176251']
    · rw [div_lt_iff hp]; linarith [log3_2_gt_190537_301994']
  have hf : (Int.fract ((31867 - 50508 * log3_2) / (125743 * log3_2 - 79335)) : ℝ) = (111202 - 176251 * log3_2) / (125743 * log3_2 - 79335) := by
    rw [fract_def, hK]; field_simp [ne_of_gt hp]; ring
  rw [hf]; field_simp

private theorem s_get_zero (v : ℝ) (hv : Int.fract v ≠ 0) (k : ℤ)
    (hk : ⌊(Int.fract v : ℝ)⁻¹⌋ = k) :
    (GenContFract.of v).s.get? 0 = some ⟨1, k⟩ := by
  rw [GenContFract.of_s_head_aux]
  rw [show (1 : ℕ) = 0 + 1 from by omega]
  rw [GenContFract.IntFractPair.stream_succ_of_some
    (GenContFract.IntFractPair.stream_zero v) hv]
  simp only [Option.bind, Function.comp_apply, GenContFract.IntFractPair.of, hk]

-- N=3
private theorem log3_2_cf_stream_three :
    log3_2_cf.s.get? 3 = some ⟨1, (Al32 4 : ℝ)⟩ := by
  unfold log3_2_cf
  rw [GenContFract.of_s_succ log3_2 2]
  rw [show (Int.fract log3_2 : ℝ) = log3_2 from log3_2_fract_eq]
  rw [GenContFract.of_s_succ log3_2⁻¹ 1]
  rw [xi2_eq]
  rw [GenContFract.of_s_succ (log3_2 / (1 - log3_2)) 0]
  rw [xi3_eq]
  exact s_get_zero ((1 - log3_2) / (2 * log3_2 - 1))
    xi4_fract_ne 2 xi4_floor

-- N=4
private theorem log3_2_cf_stream_four :
    log3_2_cf.s.get? 4 = some ⟨1, (Al32 5 : ℝ)⟩ := by
  unfold log3_2_cf
  rw [GenContFract.of_s_succ log3_2 3]
  rw [show (Int.fract log3_2 : ℝ) = log3_2 from log3_2_fract_eq]
  rw [GenContFract.of_s_succ log3_2⁻¹ 2]
  rw [xi2_eq]
  rw [GenContFract.of_s_succ (log3_2 / (1 - log3_2)) 1]
  rw [xi3_eq]
  rw [GenContFract.of_s_succ ((1 - log3_2) / (2 * log3_2 - 1)) 0]
  rw [xi4_eq]
  exact s_get_zero ((2 * log3_2 - 1) / (2 - 3 * log3_2))
    xi5_fract_ne 2 xi5_floor

-- N=5
private theorem log3_2_cf_stream_five :
    log3_2_cf.s.get? 5 = some ⟨1, (Al32 6 : ℝ)⟩ := by
  unfold log3_2_cf
  rw [GenContFract.of_s_succ log3_2 4]
  rw [show (Int.fract log3_2 : ℝ) = log3_2 from log3_2_fract_eq]
  rw [GenContFract.of_s_succ log3_2⁻¹ 3]
  rw [xi2_eq]
  rw [GenContFract.of_s_succ (log3_2 / (1 - log3_2)) 2]
  rw [xi3_eq]
  rw [GenContFract.of_s_succ ((1 - log3_2) / (2 * log3_2 - 1)) 1]
  rw [xi4_eq]
  rw [GenContFract.of_s_succ ((2 * log3_2 - 1) / (2 - 3 * log3_2)) 0]
  rw [xi5_eq]
  exact s_get_zero ((2 - 3 * log3_2) / (8 * log3_2 - 5))
    xi6_fract_ne 3 xi6_floor

-- N=6
private theorem log3_2_cf_stream_six :
    log3_2_cf.s.get? 6 = some ⟨1, (Al32 7 : ℝ)⟩ := by
  unfold log3_2_cf
  rw [GenContFract.of_s_succ log3_2 5]
  rw [show (Int.fract log3_2 : ℝ) = log3_2 from log3_2_fract_eq]
  rw [GenContFract.of_s_succ log3_2⁻¹ 4]
  rw [xi2_eq]
  rw [GenContFract.of_s_succ (log3_2 / (1 - log3_2)) 3]
  rw [xi3_eq]
  rw [GenContFract.of_s_succ ((1 - log3_2) / (2 * log3_2 - 1)) 2]
  rw [xi4_eq]
  rw [GenContFract.of_s_succ ((2 * log3_2 - 1) / (2 - 3 * log3_2)) 1]
  rw [xi5_eq]
  rw [GenContFract.of_s_succ ((2 - 3 * log3_2) / (8 * log3_2 - 5)) 0]
  rw [xi6_eq]
  exact s_get_zero ((8 * log3_2 - 5) / (12 - 19 * log3_2))
    xi7_fract_ne 1 xi7_floor

-- N=7
private theorem log3_2_cf_stream_seven :
    log3_2_cf.s.get? 7 = some ⟨1, (Al32 8 : ℝ)⟩ := by
  unfold log3_2_cf
  rw [GenContFract.of_s_succ log3_2 6]
  rw [show (Int.fract log3_2 : ℝ) = log3_2 from log3_2_fract_eq]
  rw [GenContFract.of_s_succ log3_2⁻¹ 5]
  rw [xi2_eq]
  rw [GenContFract.of_s_succ (log3_2 / (1 - log3_2)) 4]
  rw [xi3_eq]
  rw [GenContFract.of_s_succ ((1 - log3_2) / (2 * log3_2 - 1)) 3]
  rw [xi4_eq]
  rw [GenContFract.of_s_succ ((2 * log3_2 - 1) / (2 - 3 * log3_2)) 2]
  rw [xi5_eq]
  rw [GenContFract.of_s_succ ((2 - 3 * log3_2) / (8 * log3_2 - 5)) 1]
  rw [xi6_eq]
  rw [GenContFract.of_s_succ ((8 * log3_2 - 5) / (12 - 19 * log3_2)) 0]
  rw [xi7_eq]
  exact s_get_zero ((12 - 19 * log3_2) / (65 * log3_2 - 41))
    xi8_fract_ne 5 xi8_floor

-- N=8
private theorem log3_2_cf_stream_eight :
    log3_2_cf.s.get? 8 = some ⟨1, (Al32 9 : ℝ)⟩ := by
  unfold log3_2_cf
  rw [GenContFract.of_s_succ log3_2 7]
  rw [show (Int.fract log3_2 : ℝ) = log3_2 from log3_2_fract_eq]
  rw [GenContFract.of_s_succ log3_2⁻¹ 6]
  rw [xi2_eq]
  rw [GenContFract.of_s_succ (log3_2 / (1 - log3_2)) 5]
  rw [xi3_eq]
  rw [GenContFract.of_s_succ ((1 - log3_2) / (2 * log3_2 - 1)) 4]
  rw [xi4_eq]
  rw [GenContFract.of_s_succ ((2 * log3_2 - 1) / (2 - 3 * log3_2)) 3]
  rw [xi5_eq]
  rw [GenContFract.of_s_succ ((2 - 3 * log3_2) / (8 * log3_2 - 5)) 2]
  rw [xi6_eq]
  rw [GenContFract.of_s_succ ((8 * log3_2 - 5) / (12 - 19 * log3_2)) 1]
  rw [xi7_eq]
  rw [GenContFract.of_s_succ ((12 - 19 * log3_2) / (65 * log3_2 - 41)) 0]
  rw [xi8_eq]
  exact s_get_zero ((65 * log3_2 - 41) / (53 - 84 * log3_2))
    xi9_fract_ne 2 xi9_floor

-- N=9
private theorem log3_2_cf_stream_nine :
    log3_2_cf.s.get? 9 = some ⟨1, (Al32 10 : ℝ)⟩ := by
  unfold log3_2_cf
  rw [GenContFract.of_s_succ log3_2 8]
  rw [show (Int.fract log3_2 : ℝ) = log3_2 from log3_2_fract_eq]
  rw [GenContFract.of_s_succ log3_2⁻¹ 7]
  rw [xi2_eq]
  rw [GenContFract.of_s_succ (log3_2 / (1 - log3_2)) 6]
  rw [xi3_eq]
  rw [GenContFract.of_s_succ ((1 - log3_2) / (2 * log3_2 - 1)) 5]
  rw [xi4_eq]
  rw [GenContFract.of_s_succ ((2 * log3_2 - 1) / (2 - 3 * log3_2)) 4]
  rw [xi5_eq]
  rw [GenContFract.of_s_succ ((2 - 3 * log3_2) / (8 * log3_2 - 5)) 3]
  rw [xi6_eq]
  rw [GenContFract.of_s_succ ((8 * log3_2 - 5) / (12 - 19 * log3_2)) 2]
  rw [xi7_eq]
  rw [GenContFract.of_s_succ ((12 - 19 * log3_2) / (65 * log3_2 - 41)) 1]
  rw [xi8_eq]
  rw [GenContFract.of_s_succ ((65 * log3_2 - 41) / (53 - 84 * log3_2)) 0]
  rw [xi9_eq]
  exact s_get_zero ((53 - 84 * log3_2) / (485 * log3_2 - 306))
    xi10_fract_ne 23 xi10_floor

-- N=10
private theorem log3_2_cf_stream_ten :
    log3_2_cf.s.get? 10 = some ⟨1, (Al32 11 : ℝ)⟩ := by
  unfold log3_2_cf
  rw [GenContFract.of_s_succ log3_2 9]
  rw [show (Int.fract log3_2 : ℝ) = log3_2 from log3_2_fract_eq]
  rw [GenContFract.of_s_succ log3_2⁻¹ 8]
  rw [xi2_eq]
  rw [GenContFract.of_s_succ (log3_2 / (1 - log3_2)) 7]
  rw [xi3_eq]
  rw [GenContFract.of_s_succ ((1 - log3_2) / (2 * log3_2 - 1)) 6]
  rw [xi4_eq]
  rw [GenContFract.of_s_succ ((2 * log3_2 - 1) / (2 - 3 * log3_2)) 5]
  rw [xi5_eq]
  rw [GenContFract.of_s_succ ((2 - 3 * log3_2) / (8 * log3_2 - 5)) 4]
  rw [xi6_eq]
  rw [GenContFract.of_s_succ ((8 * log3_2 - 5) / (12 - 19 * log3_2)) 3]
  rw [xi7_eq]
  rw [GenContFract.of_s_succ ((12 - 19 * log3_2) / (65 * log3_2 - 41)) 2]
  rw [xi8_eq]
  rw [GenContFract.of_s_succ ((65 * log3_2 - 41) / (53 - 84 * log3_2)) 1]
  rw [xi9_eq]
  rw [GenContFract.of_s_succ ((53 - 84 * log3_2) / (485 * log3_2 - 306)) 0]
  rw [xi10_eq]
  exact s_get_zero ((485 * log3_2 - 306) / (665 - 1054 * log3_2))
    xi11_fract_ne 2 xi11_floor

-- N=11
private theorem log3_2_cf_stream_eleven :
    log3_2_cf.s.get? 11 = some ⟨1, (Al32 12 : ℝ)⟩ := by
  unfold log3_2_cf
  rw [GenContFract.of_s_succ log3_2 10]
  rw [show (Int.fract log3_2 : ℝ) = log3_2 from log3_2_fract_eq]
  rw [GenContFract.of_s_succ log3_2⁻¹ 9]
  rw [xi2_eq]
  rw [GenContFract.of_s_succ (log3_2 / (1 - log3_2)) 8]
  rw [xi3_eq]
  rw [GenContFract.of_s_succ ((1 - log3_2) / (2 * log3_2 - 1)) 7]
  rw [xi4_eq]
  rw [GenContFract.of_s_succ ((2 * log3_2 - 1) / (2 - 3 * log3_2)) 6]
  rw [xi5_eq]
  rw [GenContFract.of_s_succ ((2 - 3 * log3_2) / (8 * log3_2 - 5)) 5]
  rw [xi6_eq]
  rw [GenContFract.of_s_succ ((8 * log3_2 - 5) / (12 - 19 * log3_2)) 4]
  rw [xi7_eq]
  rw [GenContFract.of_s_succ ((12 - 19 * log3_2) / (65 * log3_2 - 41)) 3]
  rw [xi8_eq]
  rw [GenContFract.of_s_succ ((65 * log3_2 - 41) / (53 - 84 * log3_2)) 2]
  rw [xi9_eq]
  rw [GenContFract.of_s_succ ((53 - 84 * log3_2) / (485 * log3_2 - 306)) 1]
  rw [xi10_eq]
  rw [GenContFract.of_s_succ ((485 * log3_2 - 306) / (665 - 1054 * log3_2)) 0]
  rw [xi11_eq]
  exact s_get_zero ((665 - 1054 * log3_2) / (24727 * log3_2 - 15601))
    xi12_fract_ne 2 xi12_floor

-- N=12
private theorem log3_2_cf_stream_twelve :
    log3_2_cf.s.get? 12 = some ⟨1, (Al32 13 : ℝ)⟩ := by
  unfold log3_2_cf
  rw [GenContFract.of_s_succ log3_2 11]
  rw [show (Int.fract log3_2 : ℝ) = log3_2 from log3_2_fract_eq]
  rw [GenContFract.of_s_succ log3_2⁻¹ 10]
  rw [xi2_eq]
  rw [GenContFract.of_s_succ (log3_2 / (1 - log3_2)) 9]
  rw [xi3_eq]
  rw [GenContFract.of_s_succ ((1 - log3_2) / (2 * log3_2 - 1)) 8]
  rw [xi4_eq]
  rw [GenContFract.of_s_succ ((2 * log3_2 - 1) / (2 - 3 * log3_2)) 7]
  rw [xi5_eq]
  rw [GenContFract.of_s_succ ((2 - 3 * log3_2) / (8 * log3_2 - 5)) 6]
  rw [xi6_eq]
  rw [GenContFract.of_s_succ ((8 * log3_2 - 5) / (12 - 19 * log3_2)) 5]
  rw [xi7_eq]
  rw [GenContFract.of_s_succ ((12 - 19 * log3_2) / (65 * log3_2 - 41)) 4]
  rw [xi8_eq]
  rw [GenContFract.of_s_succ ((65 * log3_2 - 41) / (53 - 84 * log3_2)) 3]
  rw [xi9_eq]
  rw [GenContFract.of_s_succ ((53 - 84 * log3_2) / (485 * log3_2 - 306)) 2]
  rw [xi10_eq]
  rw [GenContFract.of_s_succ ((485 * log3_2 - 306) / (665 - 1054 * log3_2)) 1]
  rw [xi11_eq]
  rw [GenContFract.of_s_succ ((665 - 1054 * log3_2) / (24727 * log3_2 - 15601)) 0]
  rw [xi12_eq]
  exact s_get_zero ((24727 * log3_2 - 15601) / (31867 - 50508 * log3_2))
    xi13_fract_ne 1 xi13_floor

-- N=13
private theorem log3_2_cf_stream_thirteen :
    log3_2_cf.s.get? 13 = some ⟨1, (Al32 14 : ℝ)⟩ := by
  unfold log3_2_cf
  rw [GenContFract.of_s_succ log3_2 12]
  rw [show (Int.fract log3_2 : ℝ) = log3_2 from log3_2_fract_eq]
  rw [GenContFract.of_s_succ log3_2⁻¹ 11]
  rw [xi2_eq]
  rw [GenContFract.of_s_succ (log3_2 / (1 - log3_2)) 10]
  rw [xi3_eq]
  rw [GenContFract.of_s_succ ((1 - log3_2) / (2 * log3_2 - 1)) 9]
  rw [xi4_eq]
  rw [GenContFract.of_s_succ ((2 * log3_2 - 1) / (2 - 3 * log3_2)) 8]
  rw [xi5_eq]
  rw [GenContFract.of_s_succ ((2 - 3 * log3_2) / (8 * log3_2 - 5)) 7]
  rw [xi6_eq]
  rw [GenContFract.of_s_succ ((8 * log3_2 - 5) / (12 - 19 * log3_2)) 6]
  rw [xi7_eq]
  rw [GenContFract.of_s_succ ((12 - 19 * log3_2) / (65 * log3_2 - 41)) 5]
  rw [xi8_eq]
  rw [GenContFract.of_s_succ ((65 * log3_2 - 41) / (53 - 84 * log3_2)) 4]
  rw [xi9_eq]
  rw [GenContFract.of_s_succ ((53 - 84 * log3_2) / (485 * log3_2 - 306)) 3]
  rw [xi10_eq]
  rw [GenContFract.of_s_succ ((485 * log3_2 - 306) / (665 - 1054 * log3_2)) 2]
  rw [xi11_eq]
  rw [GenContFract.of_s_succ ((665 - 1054 * log3_2) / (24727 * log3_2 - 15601)) 1]
  rw [xi12_eq]
  rw [GenContFract.of_s_succ ((24727 * log3_2 - 15601) / (31867 - 50508 * log3_2)) 0]
  rw [xi13_eq]
  exact s_get_zero ((31867 - 50508 * log3_2) / (125743 * log3_2 - 79335))
    xi14_fract_ne 1 xi14_floor

-- N=14
private theorem log3_2_cf_stream_fourteen :
    log3_2_cf.s.get? 14 = some ⟨1, (Al32 15 : ℝ)⟩ := by
  unfold log3_2_cf
  rw [GenContFract.of_s_succ log3_2 13]
  rw [show (Int.fract log3_2 : ℝ) = log3_2 from log3_2_fract_eq]
  rw [GenContFract.of_s_succ log3_2⁻¹ 12]
  rw [xi2_eq]
  rw [GenContFract.of_s_succ (log3_2 / (1 - log3_2)) 11]
  rw [xi3_eq]
  rw [GenContFract.of_s_succ ((1 - log3_2) / (2 * log3_2 - 1)) 10]
  rw [xi4_eq]
  rw [GenContFract.of_s_succ ((2 * log3_2 - 1) / (2 - 3 * log3_2)) 9]
  rw [xi5_eq]
  rw [GenContFract.of_s_succ ((2 - 3 * log3_2) / (8 * log3_2 - 5)) 8]
  rw [xi6_eq]
  rw [GenContFract.of_s_succ ((8 * log3_2 - 5) / (12 - 19 * log3_2)) 7]
  rw [xi7_eq]
  rw [GenContFract.of_s_succ ((12 - 19 * log3_2) / (65 * log3_2 - 41)) 6]
  rw [xi8_eq]
  rw [GenContFract.of_s_succ ((65 * log3_2 - 41) / (53 - 84 * log3_2)) 5]
  rw [xi9_eq]
  rw [GenContFract.of_s_succ ((53 - 84 * log3_2) / (485 * log3_2 - 306)) 4]
  rw [xi10_eq]
  rw [GenContFract.of_s_succ ((485 * log3_2 - 306) / (665 - 1054 * log3_2)) 3]
  rw [xi11_eq]
  rw [GenContFract.of_s_succ ((665 - 1054 * log3_2) / (24727 * log3_2 - 15601)) 2]
  rw [xi12_eq]
  rw [GenContFract.of_s_succ ((24727 * log3_2 - 15601) / (31867 - 50508 * log3_2)) 1]
  rw [xi13_eq]
  rw [GenContFract.of_s_succ ((31867 - 50508 * log3_2) / (125743 * log3_2 - 79335)) 0]
  rw [xi14_eq]
  exact s_get_zero ((125743 * log3_2 - 79335) / (111202 - 176251 * log3_2))
    xi15_fract_ne 55 xi15_floor

-- N=2
private theorem log3_2_cf_stream_two :
    log3_2_cf.s.get? 2 = some ⟨1, (Al32 3 : ℝ)⟩ := by
  unfold log3_2_cf
  have hfract : (Int.fract (log3_2 : ℝ)⁻¹)⁻¹ = log3_2 / (1 - log3_2) := by
    rw [fract_def]
    have hf : ⌊(log3_2 : ℝ)⁻¹⌋ = 1 := by exact log3_2_inv_floor_one
    rw [hf]
    push_cast
    field_simp [ne_of_gt ErdosTernary.ContinuedFraction.log3_2_pos]
  rw [GenContFract.of_s_succ log3_2 1]
  rw [show (Int.fract log3_2 : ℝ) = log3_2 from log3_2_fract_eq]
  rw [GenContFract.of_s_succ log3_2⁻¹ 0]
  rw [show (Int.fract (log3_2 : ℝ)⁻¹)⁻¹ = log3_2 / (1 - log3_2) from hfract]
  rw [GenContFract.of_s_head_aux]
  rw [show (1 : ℕ) = 0 + 1 from by omega]
  have hfract_ne : Int.fract (log3_2 / (1 - log3_2)) ≠ 0 := by
    rw [xi3_fract_eq]; exact div_ne_zero (by linarith [log3_2_gt_one_half]) (by linarith [ErdosTernary.ContinuedFraction.log3_2_lt_one])
  rw [GenContFract.IntFractPair.stream_succ_of_some
    (GenContFract.IntFractPair.stream_zero (log3_2 / (1 - log3_2))) hfract_ne]
  simp only [Option.bind_some, Function.comp_apply, GenContFract.IntFractPair.of]
  rw [xi3_floor]
  simp [Al32, ErdosTernary.Ostrowski.log32_cf, List.getD]

/-- The GenContFract stream of log₃(2) at position n equals ⟨1, Al32(n+1)⟩,
    for n ≤ 14 (the range covered by the stored log32_cf partial quotients
    that appear as actual CF coefficients of log₃(2)). -/
private theorem log3_2_cf_stream (n : ℕ) (hn : n ≤ 14) :
    log3_2_cf.s.get? n = some ⟨1, (Al32 (n + 1) : ℝ)⟩ := by
  exact match n, hn with
  | 0, _ => log3_2_cf_stream_zero
  | 1, _ => log3_2_cf_stream_one
  | 2, _ => log3_2_cf_stream_two
  | 3, _ => log3_2_cf_stream_three
  | 4, _ => log3_2_cf_stream_four
  | 5, _ => log3_2_cf_stream_five
  | 6, _ => log3_2_cf_stream_six
  | 7, _ => log3_2_cf_stream_seven
  | 8, _ => log3_2_cf_stream_eight
  | 9, _ => log3_2_cf_stream_nine
  | 10, _ => log3_2_cf_stream_ten
  | 11, _ => log3_2_cf_stream_eleven
  | 12, _ => log3_2_cf_stream_twelve
  | 13, _ => log3_2_cf_stream_thirteen
  | 14, _ => log3_2_cf_stream_fourteen
  | n + 15, hn => absurd hn (by omega)

/-- If two functions satisfy the same second-order linear recurrence with the same
    initial values, they are equal. Proved by strong induction. -/
private theorem eq_of_recurrence {f g : ℕ → ℝ} {c : ℕ → ℝ}
    (h0 : f 0 = g 0) (h1 : f 1 = g 1)
    (hrec : ∀ k, f (k + 2) = c (k + 2) * f (k + 1) + f k)
    (hrec' : ∀ k, g (k + 2) = c (k + 2) * g (k + 1) + g k) :
    ∀ k, f k = g k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    cases k with
    | zero => exact h0
    | succ k =>
      cases k with
      | zero => exact h1
      | succ k =>
        rw [hrec k, hrec' k, ih k (by omega), ih (k + 1) (by omega)]

/-- Q Al32 k equals log3_2_cf.dens k for all k.
    Both satisfy f(0)=1, f(1)=1, f(k+2) = Al32(k+2)*f(k+1) + f(k).
    For the CF: dens(k+2) = b_{k+1}*dens(k+1) + dens(k) where b_{k+1} = Al32(k+2)
    by the stream characterization, and a=1 for GenContFract.of. -/
theorem Q_eq_cf_dens (k : ℕ) (hk : k ≤ 15) :
    (Q Al32 k : ℝ) = log3_2_cf.dens k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    cases k with
    | zero => simp [Q, GenContFract.zeroth_den_eq_one]
    | succ k =>
      cases k with
      | zero =>
        simp only [Q, Q_zero, Q_one]
        have h₀ := log3_2_cf_stream 0 (by omega)
        have hrec := GenContFract.second_contAux_eq h₀
        rw [show (log3_2_cf.dens 1 : ℝ) = (log3_2_cf.contsAux 2).b from by
          rw [GenContFract.den_eq_conts_b, GenContFract.nth_cont_eq_succ_nth_contAux]]
        rw [hrec]
        simp [Al32]
        norm_num [ErdosTernary.Ostrowski.log32_cf, List.getD]
      | succ k =>
        simp only [Q]
        have hstream := log3_2_cf_stream (k + 1) (by omega)
        have hrec := GenContFract.dens_recurrence hstream rfl rfl
        push_cast
        rw [ih (k + 1) (by omega) (by omega), ih k (by omega) (by omega)]
        rw [hrec]
        push_cast
        ring

/-- dens k ≥ Q Al32 k for k ≤ 15. -/
theorem dens_ge_Q (k : ℕ) (hk : k ≤ 15) :
    (Q Al32 k : ℝ) ≤ (log3_2_cf.dens k : ℝ) :=
  le_of_eq (Q_eq_cf_dens k hk)

/-! ## Convergent Error Bound -/

/-- The convergent error bound: |εₖ| < 1/Bₖ₊₁.

    Proof chain:
    1. epsilon k = dens k * (α - convs k)     [epsilon_eq_mul_sub]
    2. |α - convs k| < 1/(dens k * dens(k+1))  [log3_2_convs_error + irrationality]
    3. Multiply by dens k > 0: |εₖ| < 1/dens(k+1)
    4. dens(k+1) = Q Al32(k+1)                  [Q_eq_cf_dens] -/
theorem epsilon_lt (k : ℕ) (hk : k + 1 ≤ 15) :
    |epsilon k| < 1 / (Q Al32 (k + 1) : ℝ) := by
  have hpos := cf_dens_pos k
  have hd : (log3_2_cf.dens k : ℝ) ≠ 0 := ne_of_gt hpos
  have h_strict : |α - log3_2_cf.convs k| < 1 / (log3_2_cf.dens k * log3_2_cf.dens (k + 1)) := by
    have h_le := log3_2_convs_error k
    by_contra h_not_strict
    push_neg at h_not_strict
    have h_eq : |α - log3_2_cf.convs k| = 1 / (log3_2_cf.dens k * log3_2_cf.dens (k + 1)) :=
      le_antisymm h_le h_not_strict
    rcases eq_or_eq_neg_of_abs_eq h_eq with hc_pos | hc_neg
    · -- Case: α - convs = +1/(B*B') → α = convs + 1/(B*B') is rational
      have hα : α = log3_2_cf.convs k + 1 / (log3_2_cf.dens k * log3_2_cf.dens (k + 1)) := by linarith
      have h_rational : ∃ r : ℚ, (r : ℝ) = α := by
        obtain ⟨z, hz⟩ := nums_is_integer k
        obtain ⟨m₁, hm₁⟩ := dens_is_natural k
        obtain ⟨m₂, hm₂⟩ := dens_is_natural (k + 1)
        refine ⟨(z : ℚ) / (m₁ : ℚ) + 1 / ((m₁ : ℚ) * (m₂ : ℚ)), ?_⟩
        rw [hα, GenContFract.convs, hz.symm, hm₁.symm, hm₂.symm]; push_cast; ring
      exact log3_2_irrational h_rational
    · -- Case: α - convs = -1/(B*B') → α = convs - 1/(B*B') is rational
      have hα : α = log3_2_cf.convs k - 1 / (log3_2_cf.dens k * log3_2_cf.dens (k + 1)) := by linarith
      have h_rational : ∃ r : ℚ, (r : ℝ) = α := by
        obtain ⟨z, hz⟩ := nums_is_integer k
        obtain ⟨m₁, hm₁⟩ := dens_is_natural k
        obtain ⟨m₂, hm₂⟩ := dens_is_natural (k + 1)
        refine ⟨(z : ℚ) / (m₁ : ℚ) - 1 / ((m₁ : ℚ) * (m₂ : ℚ)), ?_⟩
        rw [hα, GenContFract.convs, hz.symm, hm₁.symm, hm₂.symm]; push_cast; ring
      exact log3_2_irrational h_rational
  have h_raw : |epsilon k| < 1 / (log3_2_cf.dens (k + 1) : ℝ) := by
    rw [epsilon_eq_mul_sub]
    calc |(log3_2_cf.dens k : ℝ) * (α - log3_2_cf.convs k)|
        = (log3_2_cf.dens k : ℝ) * |α - log3_2_cf.convs k| := by
          rw [abs_mul, abs_of_pos hpos]
      _ < (log3_2_cf.dens k : ℝ) * (1 / ((log3_2_cf.dens k : ℝ) * (log3_2_cf.dens (k + 1) : ℝ))) := by
        exact mul_lt_mul_of_pos_left h_strict hpos
      _ = 1 / (log3_2_cf.dens (k + 1) : ℝ) := by
        have hd2 : (log3_2_cf.dens (k + 1) : ℝ) ≠ 0 := ne_of_gt (cf_dens_pos (k + 1))
        field_simp
  -- dens(k+1) ≥ Q(k+1), so 1/dens(k+1) ≤ 1/Q(k+1)
  have h_ge := dens_ge_Q (k + 1) hk
  have hQ_pos : 0 < (Q Al32 (k + 1) : ℝ) := by exact_mod_cast Q_pos (k + 1)
  have hQ_ne : (Q Al32 (k + 1) : ℝ) ≠ 0 := ne_of_gt hQ_pos
  -- h_ge: Q(k+1) ≤ dens(k+1), hQ_pos: 0 < Q(k+1) → 1/dens(k+1) ≤ 1/Q(k+1)
  have h_inv : (1 : ℝ) / (log3_2_cf.dens (k + 1)) ≤ (1 : ℝ) / (Q Al32 (k + 1)) :=
    one_div_le_one_div_of_le hQ_pos h_ge
  exact lt_of_lt_of_le h_raw h_inv

/-! ## Alternating Sign -/

/-- Helper: ¬TerminatedAt n implies stream v n is some. -/
private theorem stream_ne_none_of_not_terminated {n : ℕ} :
    ¬log3_2_cf.TerminatedAt n →
    ∃ ifp, GenContFract.IntFractPair.stream log3_2 n = some ifp := by
  intro h_not_term
  -- ¬TerminatedAt n means stream (n+1) ≠ none
  have h_not_none : GenContFract.IntFractPair.stream log3_2 (n + 1) ≠ none := by
    intro h
    exact h_not_term (GenContFract.of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none.mpr h)
  -- stream (n+1) ≠ none implies stream n ≠ none
  have h_stream_n_ne : GenContFract.IntFractPair.stream log3_2 n ≠ none := by
    by_contra h_eq_none
    exact h_not_none (by simp [GenContFract.IntFractPair.stream, h_eq_none])
  exact Option.ne_none_iff_exists'.mp h_stream_n_ne

/-- The convergent error εₖ = dens k * (α - convs k) has sign (-1)^k.
    From sub_convs_eq: α - convs k = (-1)^k / (B * (fr⁻¹ * B + B₋₁)),
    where B = dens k, B₋₁ = dens (k-1), and fr ∈ (0,1) for irrational v.
    Since B > 0 and fr⁻¹ * B + B₋₁ > 0, the sign is determined by (-1)^k. -/
theorem epsilon_pos_of_even (k : ℕ) (hk : Even k) : 0 < epsilon k := by
  rw [epsilon_eq_mul_sub]
  apply mul_pos (cf_dens_pos k)
  obtain ⟨ifp, hstream⟩ := stream_ne_none_of_not_terminated (log3_2_not_terminatedAt k)
  have hfr_ne : ifp.fr ≠ 0 := by
    intro hfr_eq
    have := GenContFract.IntFractPair.stream_eq_none_of_fr_eq_zero hstream hfr_eq
    exact log3_2_not_terminatedAt k
      (GenContFract.of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none.mpr this)
  have h := GenContFract.sub_convs_eq hstream
  rw [show α - log3_2_cf.convs k =
      if ifp.fr = 0 then (0:ℝ) else (-1:ℝ) ^ k /
        ((log3_2_cf.contsAux (k + 1)).b *
          (ifp.fr⁻¹ * (log3_2_cf.contsAux (k + 1)).b + (log3_2_cf.contsAux k).b)) from h]
  rw [if_neg hfr_ne, hk.neg_one_pow]
  rw [one_div_pos]
  have hB_pos : 0 < (log3_2_cf.contsAux (k + 1)).b := by
    have := cf_dens_pos k
    rwa [GenContFract.den_eq_conts_b, GenContFract.nth_cont_eq_succ_nth_contAux] at this
  have hpB_nonneg : 0 ≤ (log3_2_cf.contsAux k).b := GenContFract.zero_le_of_contsAux_b
  have hfr_pos : 0 < ifp.fr := by
    have := GenContFract.IntFractPair.nth_stream_fr_nonneg hstream
    exact lt_of_le_of_ne this hfr_ne.symm
  have hinv_pos : 0 < ifp.fr⁻¹ := by positivity
  have hmul_pos : 0 < ifp.fr⁻¹ * (log3_2_cf.contsAux (k + 1)).b := mul_pos hinv_pos (by
    have := cf_dens_pos k
    rwa [GenContFract.den_eq_conts_b, GenContFract.nth_cont_eq_succ_nth_contAux] at this)
  exact mul_pos hB_pos (add_pos_of_pos_of_nonneg hmul_pos hpB_nonneg)

theorem epsilon_neg_of_odd (k : ℕ) (hk : Odd k) : epsilon k < 0 := by
  rw [epsilon_eq_mul_sub]
  obtain ⟨ifp, hstream⟩ := stream_ne_none_of_not_terminated (log3_2_not_terminatedAt k)
  have hfr_ne : ifp.fr ≠ 0 := by
    intro hfr_eq
    have := GenContFract.IntFractPair.stream_eq_none_of_fr_eq_zero hstream hfr_eq
    exact log3_2_not_terminatedAt k
      (GenContFract.of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none.mpr this)
  have h := GenContFract.sub_convs_eq hstream
  rw [show α - log3_2_cf.convs k =
      if ifp.fr = 0 then (0:ℝ) else (-1:ℝ) ^ k /
        ((log3_2_cf.contsAux (k + 1)).b *
          (ifp.fr⁻¹ * (log3_2_cf.contsAux (k + 1)).b + (log3_2_cf.contsAux k).b)) from h]
  rw [if_neg hfr_ne, hk.neg_one_pow]
  have hB_pos : 0 < (log3_2_cf.contsAux (k + 1)).b := by
    have := cf_dens_pos k
    rwa [GenContFract.den_eq_conts_b, GenContFract.nth_cont_eq_succ_nth_contAux] at this
  have hpB_nonneg : 0 ≤ (log3_2_cf.contsAux k).b := GenContFract.zero_le_of_contsAux_b
  have hfr_pos : 0 < ifp.fr := by
    have := GenContFract.IntFractPair.nth_stream_fr_nonneg hstream
    exact lt_of_le_of_ne this hfr_ne.symm
  have hinv_pos : 0 < ifp.fr⁻¹ := by positivity
  have hsum_pos : 0 < ifp.fr⁻¹ * (log3_2_cf.contsAux (k + 1)).b + (log3_2_cf.contsAux k).b := by
    have hmul := mul_pos hinv_pos hB_pos
    exact add_pos_of_pos_of_nonneg hmul hpB_nonneg
  have hden_pos : 0 < (log3_2_cf.contsAux (k + 1)).b * (ifp.fr⁻¹ * (log3_2_cf.contsAux (k + 1)).b + (log3_2_cf.contsAux k).b) :=
    mul_pos hB_pos hsum_pos
  apply mul_neg_of_pos_of_neg (cf_dens_pos k)
  rw [neg_div, neg_lt_zero]
  exact one_div_pos.mpr hden_pos

/-! ## Ostrowski Representation -/

/-- Helper: topIdx(n % Qt) < topIdx n when 0 < n. -/
private theorem ostrowski_topIdx_lt {n : ℕ} (hpos : 0 < n) :
    topIdx Al32 Al32_hyp (n % Q Al32 (topIdx Al32 Al32_hyp n)) < topIdx Al32 Al32_hyp n := by
  have hQt_pos : 0 < Q Al32 (topIdx Al32 Al32_hyp n) := Q_pos _
  have hmod_qt : n % Q Al32 (topIdx Al32 Al32_hyp n) < Q Al32 (topIdx Al32 Al32_hyp n) :=
    Nat.mod_lt n hQt_pos
  have h1 : 1 ≤ topIdx Al32 Al32_hyp n := by
    cases hc : topIdx Al32 Al32_hyp n with
    | zero =>
      have hhi := topIdx_hi Al32_hyp n
      rw [hc, Q_one] at hhi
      linarith
    | succ m => exact Nat.succ_le_succ (Nat.zero_le _)
  have hle : topIdx Al32 Al32_hyp (n % Q Al32 (topIdx Al32 Al32_hyp n)) ≤
      topIdx Al32 Al32_hyp n - 1 :=
    topIdx_le_of_lt Al32_hyp (by rw [Nat.sub_add_cancel h1]; exact hmod_qt)
  exact Nat.lt_of_le_pred h1 hle

/-- The Ostrowski representation: n = Σ bₖ * Q(k).
    Proved by strong induction on n using gd_eq_top_of / gd_eq_shift_of. -/
theorem ostrowski_representation (n : ℕ) (hpos : 0 < n) :
    (n : ℝ) = ∑ k in Finset.range (topIdx Al32 Al32_hyp n + 1),
      (gd Al32 Al32_hyp k n : ℝ) * (Q Al32 k : ℝ) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [Finset.sum_range_succ]
    rw [gd_eq_top_of Al32_hyp hpos rfl]
    have hQt_pos : 0 < Q Al32 (topIdx Al32 Al32_hyp n) := Q_pos _
    have hmod : n % Q Al32 (topIdx Al32 Al32_hyp n) < n :=
      lt_of_lt_of_le (Nat.mod_lt n hQt_pos) (topIdx_lo Al32_hyp hpos)
    have hmod_qt : n % Q Al32 (topIdx Al32 Al32_hyp n) < Q Al32 (topIdx Al32 Al32_hyp n) :=
      Nat.mod_lt n hQt_pos
    have htop_lt := ostrowski_topIdx_lt hpos
    -- Rewrite the inner sum: gd(k,n) = gd(k, n%Qt) for k ≠ topIdx
    have h_congr :
        ∑ k in Finset.range (topIdx Al32 Al32_hyp n),
            (gd Al32 Al32_hyp k n : ℝ) * (Q Al32 k : ℝ) =
        ∑ k in Finset.range (topIdx Al32 Al32_hyp n),
            (gd Al32 Al32_hyp k (n % Q Al32 (topIdx Al32 Al32_hyp n)) : ℝ) * (Q Al32 k : ℝ) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk_ne : k ≠ topIdx Al32 Al32_hyp n := ne_of_lt (Finset.mem_range.mp hk)
      rw [gd_eq_shift_of Al32_hyp hpos hk_ne]
    rw [h_congr]
    -- Extend the sum from range(topIdx(n%Qt)+1) to range(topIdx n)
    have hsum_ext :
        ∑ k in Finset.range (topIdx Al32 Al32_hyp (n % Q Al32 (topIdx Al32 Al32_hyp n)) + 1),
            (gd Al32 Al32_hyp k (n % Q Al32 (topIdx Al32 Al32_hyp n)) : ℝ) * (Q Al32 k : ℝ) =
        ∑ k in Finset.range (topIdx Al32 Al32_hyp n),
            (gd Al32 Al32_hyp k (n % Q Al32 (topIdx Al32 Al32_hyp n)) : ℝ) * (Q Al32 k : ℝ) := by
      apply Finset.sum_subset (Finset.range_subset.mpr (Nat.succ_le_of_lt htop_lt))
      intro k _ hk_not
      have hk_ge : topIdx Al32 Al32_hyp (n % Q Al32 (topIdx Al32 Al32_hyp n)) + 1 ≤ k := by
        exact not_lt.mp (mt Finset.mem_range.mpr hk_not)
      rw [gd_zero_of_lt Al32_hyp (lt_of_lt_of_le (topIdx_hi Al32_hyp
        (n % Q Al32 (topIdx Al32 Al32_hyp n)))
        (Q_mono Al32_hyp (by omega : 1 ≤ topIdx Al32 Al32_hyp (n % Q Al32 (topIdx Al32 Al32_hyp n)) + 1) hk_ge))]
      simp
    -- Apply IH to n%Qt and rewrite
    rw [← hsum_ext]
    -- If n%Qt = 0, the inner sum vanishes and we get n = (n/Qt)*Qt directly
    by_cases hmod0 : n % Q Al32 (topIdx Al32 Al32_hyp n) = 0
    · -- n%Qt = 0: gd(k, 0) = 0 for all k, so inner sum = 0
      rw [hmod0]
      have hsum_zero : ∑ k in Finset.range (topIdx Al32 Al32_hyp 0 + 1),
          (gd Al32 Al32_hyp k 0 : ℝ) * (Q Al32 k : ℝ) = 0 := by
        apply Finset.sum_eq_zero; intro k _
        simp [gd, zero_mul]
      rw [hsum_zero, zero_add]
      -- Goal: (n : ℝ) = (n/Qt : ℝ) * (Qt : ℝ)
      have hdiv : n / Q Al32 (topIdx Al32 Al32_hyp n) * Q Al32 (topIdx Al32 Al32_hyp n) = n := by
        have h := Nat.div_add_mod n (Q Al32 (topIdx Al32 Al32_hyp n))
        rw [hmod0, add_zero] at h
        rwa [mul_comm] at h
      exact_mod_cast hdiv.symm
    · -- 0 < n%Qt: apply IH
      have hmodpos : 0 < n % Q Al32 (topIdx Al32 Al32_hyp n) := Nat.pos_of_ne_zero hmod0
      have ih_n := ih (n % Q Al32 (topIdx Al32 Al32_hyp n)) hmod hmodpos
      rw [← ih_n]
      -- Goal: ↑n = ↑(n%Qt) + ↑(n/Qt) * ↑Qt
      -- Prove n = n%Qt + n/Qt * Qt at ℕ, then cast
      have hnat : n = n % Q Al32 (topIdx Al32 Al32_hyp n) +
          n / Q Al32 (topIdx Al32 Al32_hyp n) * Q Al32 (topIdx Al32 Al32_hyp n) := by
        have h := Nat.div_add_mod n (Q Al32 (topIdx Al32 Al32_hyp n))
        have hc := mul_comm (Q Al32 (topIdx Al32 Al32_hyp n))
            (n / Q Al32 (topIdx Al32 Al32_hyp n))
        linarith
      have hcast := congr_arg (Nat.cast : ℕ → ℝ) hnat
      rw [Nat.cast_add, Nat.cast_mul] at hcast
      exact hcast

/-! ## The Rotation Decomposition Identity -/

/-- The key identity: n * α = (Σ bₖ * Aₖ) + (Σ bₖ * εₖ).
    Follows from ostrowski_representation and the definition of epsilon. -/
theorem rotation_decomposition (n : ℕ) (hpos : 0 < n)
    (hbound : topIdx Al32 Al32_hyp n ≤ 15) :
    (n : ℝ) * α =
      (∑ k in Finset.range (topIdx Al32 Al32_hyp n + 1),
        (gd Al32 Al32_hyp k n : ℝ) * (log3_2_cf.nums k : ℝ)) +
      (∑ k in Finset.range (topIdx Al32 Al32_hyp n + 1),
        (gd Al32 Al32_hyp k n : ℝ) * epsilon k) := by
  -- Key: Q(k) * α = nums(k) + epsilon(k) for k ≤ 15
  have key : ∀ k ≤ 15, (Q Al32 k : ℝ) * α = (log3_2_cf.nums k : ℝ) + epsilon k := by
    intro k hk
    simp only [epsilon, Q_eq_cf_dens k hk]
    ring
  -- From ostrowski: n = Σ gd(k,n) * Q(k), multiply by α, use key, distribute
  have hrep := ostrowski_representation n hpos
  calc (n : ℝ) * α
      = (∑ k in Finset.range (topIdx Al32 Al32_hyp n + 1),
          (gd Al32 Al32_hyp k n : ℝ) * (Q Al32 k : ℝ)) * α := by rw [hrep]
    _ = ∑ k in Finset.range (topIdx Al32 Al32_hyp n + 1),
          (gd Al32 Al32_hyp k n : ℝ) * (Q Al32 k : ℝ) * α := by rw [Finset.sum_mul]
    _ = ∑ k in Finset.range (topIdx Al32 Al32_hyp n + 1),
          (gd Al32 Al32_hyp k n : ℝ) * ((log3_2_cf.nums k : ℝ) + epsilon k) := by
      apply Finset.sum_congr rfl; intro k hk
      have hk_le : k ≤ 15 := by
        have := Finset.mem_range.mp hk
        omega
      rw [← key k hk_le]; ring
    _ = _ := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro k _
      ring

/-- The numerator sum Σ gd(k,n) * nums(k) is an integer-valued. -/
private theorem nums_sum_is_integer (n : ℕ) :
    ∃ z : ℤ, (z : ℝ) = ∑ k in Finset.range (topIdx Al32 Al32_hyp n + 1),
      (gd Al32 Al32_hyp k n : ℝ) * (log3_2_cf.nums k : ℝ) := by
  have key : ∀ s : Finset ℕ, ∃ z : ℤ, (z : ℝ) = ∑ k in s,
      (gd Al32 Al32_hyp k n : ℝ) * (log3_2_cf.nums k : ℝ) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨0, by simp⟩
    | @insert a s ha ih =>
      obtain ⟨z, hz⟩ := ih
      obtain ⟨zk, hzk⟩ := nums_is_integer a
      use z + gd Al32 Al32_hyp a n * zk
      rw [Finset.sum_insert ha]
      conv_lhs => rw [show (↑(z + gd Al32 Al32_hyp a n * zk) : ℝ) =
        (z : ℝ) + (↑(gd Al32 Al32_hyp a n) : ℝ) * (zk : ℝ) from by push_cast; ring]
      rw [hz, hzk]; ring
  exact key _

/-- The fractional part of n * α comes from Σ bₖ * εₖ.
    Since Σ bₖ * Aₖ is an integer (Nat-valued sum), fract removes it. -/
theorem integer_part_eq (n : ℕ) (hpos : 0 < n)
    (hbound : topIdx Al32 Al32_hyp n ≤ 15) :
    Int.fract ((n : ℝ) * α) =
      Int.fract
        (∑ k in Finset.range (topIdx Al32 Al32_hyp n + 1),
          (gd Al32 Al32_hyp k n : ℝ) * epsilon k) := by
  obtain ⟨z, hz⟩ := nums_sum_is_integer n
  have hrot := rotation_decomposition n hpos hbound
  -- n*α = nums_sum + eps_sum, with nums_sum = ↑z
  -- so fract(n*α) = fract(↑z + eps_sum) = fract(eps_sum + ↑z) = fract(eps_sum)
  conv_lhs => rw [hrot]
  rw [hz.symm, add_comm, Int.fract_add_int]

/-! ## Bound on the Signed Error Sum -/

/-- The signed error sum is bounded: |Σ bₖ * εₖ| < Σ bₖ / Bₖ₊₁. -/
theorem signed_error_bound (n : ℕ) (hpos : 0 < n)
    (hbound : topIdx Al32 Al32_hyp n + 1 ≤ 15) :
    |∑ k in Finset.range (topIdx Al32 Al32_hyp n + 1),
        (gd Al32 Al32_hyp k n : ℝ) * epsilon k| <
      ∑ k in Finset.range (topIdx Al32 Al32_hyp n + 1),
        (gd Al32 Al32_hyp k n : ℝ) / (Q Al32 (k + 1) : ℝ) := by
  have key := fun k (hk : k + 1 ≤ 15) => epsilon_lt k hk
  have hgd_nonneg : ∀ k, 0 ≤ (gd Al32 Al32_hyp k n : ℝ) := fun k => by exact_mod_cast Nat.zero_le _
  have k_bound : ∀ k ∈ Finset.range (topIdx Al32 Al32_hyp n + 1), k + 1 ≤ 15 := by
    intro k hk
    have := Finset.mem_range.mp hk
    omega
  -- Non-strict pointwise bound: |gd * eps| ≤ gd / Q(k+1)
  have pointwise_le : ∀ k ∈ Finset.range (topIdx Al32 Al32_hyp n + 1),
      |(gd Al32 Al32_hyp k n : ℝ) * epsilon k| ≤
        (gd Al32 Al32_hyp k n : ℝ) / (Q Al32 (k + 1) : ℝ) := by
    intro k hk
    rw [abs_mul, abs_of_nonneg (hgd_nonneg k)]
    have hkey := key k (k_bound k hk)
    have hQ_pos : 0 < (Q Al32 (k + 1) : ℝ) := by exact_mod_cast Q_pos (k + 1)
    calc (gd Al32 Al32_hyp k n : ℝ) * |epsilon k|
        ≤ (gd Al32 Al32_hyp k n : ℝ) * (1 / (Q Al32 (k + 1) : ℝ)) :=
          mul_le_mul_of_nonneg_left (le_of_lt hkey) (hgd_nonneg k)
      _ = (gd Al32 Al32_hyp k n : ℝ) / (Q Al32 (k + 1) : ℝ) := by ring_nf
  -- Strict inequality for k = topIdx n (gd(topIdx) = n / Q(topIdx) ≥ 1)
  have t_mem : topIdx Al32 Al32_hyp n ∈ Finset.range (topIdx Al32 Al32_hyp n + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_self _)
  have gt_zero : 0 < gd Al32 Al32_hyp (topIdx Al32 Al32_hyp n) n := by
    rw [gd_eq_top_of Al32_hyp hpos rfl]
    exact Nat.div_pos (topIdx_lo Al32_hyp hpos) (Q_pos _)
  have pointwise_strict :
      |(gd Al32 Al32_hyp (topIdx Al32 Al32_hyp n) n : ℝ) * epsilon (topIdx Al32 Al32_hyp n)| <
        (gd Al32 Al32_hyp (topIdx Al32 Al32_hyp n) n : ℝ) / (Q Al32 (topIdx Al32 Al32_hyp n + 1) : ℝ) := by
    have hg_pos : 0 < (gd Al32 Al32_hyp (topIdx Al32 Al32_hyp n) n : ℝ) :=
      by exact_mod_cast gt_zero
    have hε := key (topIdx Al32 Al32_hyp n) hbound
    rw [abs_mul, abs_of_pos hg_pos]
    calc (gd Al32 Al32_hyp (topIdx Al32 Al32_hyp n) n : ℝ) * |epsilon (topIdx Al32 Al32_hyp n)|
        < (gd Al32 Al32_hyp (topIdx Al32 Al32_hyp n) n : ℝ) * (1 / (Q Al32 (topIdx Al32 Al32_hyp n + 1) : ℝ)) :=
          mul_lt_mul_of_pos_left hε hg_pos
      _ = (gd Al32 Al32_hyp (topIdx Al32 Al32_hyp n) n : ℝ) / (Q Al32 (topIdx Al32 Al32_hyp n + 1) : ℝ) := by ring_nf
  -- Sum the pointwise bounds
  have hsum :
      ∑ k in Finset.range (topIdx Al32 Al32_hyp n + 1),
          |(gd Al32 Al32_hyp k n : ℝ) * epsilon k| <
        ∑ k in Finset.range (topIdx Al32 Al32_hyp n + 1),
          (gd Al32 Al32_hyp k n : ℝ) / (Q Al32 (k + 1) : ℝ) :=
    Finset.sum_lt_sum (fun k hk => pointwise_le k hk) ⟨_, t_mem, pointwise_strict⟩
  -- Triangle inequality: |∑ ...| ≤ ∑ |...|
  have htrian :
      |∑ k in Finset.range (topIdx Al32 Al32_hyp n + 1),
          (gd Al32 Al32_hyp k n : ℝ) * epsilon k| ≤
        ∑ k in Finset.range (topIdx Al32 Al32_hyp n + 1),
          |(gd Al32 Al32_hyp k n : ℝ) * epsilon k| :=
    Finset.abs_sum_le_sum_abs _ _
  exact lt_of_le_of_lt htrian hsum

/-! ## Tail Bound -/

/-- For large k, the convergent errors are negligible. -/
theorem high_index_bounded (n : ℕ) (hpos : 0 < n) (m : ℕ) (hm : 5 ≤ m)
    (hbound : topIdx Al32 Al32_hyp n + 1 ≤ 15) :
    |∑ k in Finset.Ico m (topIdx Al32 Al32_hyp n + 1),
        (gd Al32 Al32_hyp k n : ℝ) * epsilon k| <
      (n : ℝ) / (Q Al32 m : ℝ) := by
  have hgd_nonneg : ∀ k, 0 ≤ (gd Al32 Al32_hyp k n : ℝ) := fun k => by exact_mod_cast Nat.zero_le _
  have hm1 : 1 ≤ m := by omega
  have hQ_m_pos : 0 < (Q Al32 m : ℝ) := by exact_mod_cast Q_pos m
  have eps_bound : ∀ k ∈ Finset.Ico m (topIdx Al32 Al32_hyp n + 1), k + 1 ≤ 15 := by
    intro k hk
    have := Finset.mem_Ico.mp hk
    omega
  -- Case split: empty vs nonempty range
  by_cases h_range : Finset.Ico m (topIdx Al32 Al32_hyp n + 1) = ∅
  · -- Empty range: sum = 0 < n/Q(m)
    rw [h_range, Finset.sum_empty, abs_zero]
    apply div_pos
    · exact_mod_cast hpos
    · exact_mod_cast Q_pos m
  · -- Nonempty range: use triangle inequality + pointwise bound + one strict term
    push_neg at h_range
    obtain ⟨k₀, hk₀_mem⟩ := Finset.nonempty_iff_ne_empty.mpr h_range
    -- For k ≥ m: |eps(k)| < 1/Q(k+1) ≤ 1/Q(m)
    have pointwise : ∀ k ∈ Finset.Ico m (topIdx Al32 Al32_hyp n + 1),
        |(gd Al32 Al32_hyp k n : ℝ) * epsilon k| ≤
          (gd Al32 Al32_hyp k n : ℝ) / (Q Al32 m : ℝ) := by
      intro k hk
      have hk_mem := Finset.mem_Ico.mp hk
      have hkge : m ≤ k + 1 := by omega
      have hQ_le : (Q Al32 m : ℝ) ≤ (Q Al32 (k + 1) : ℝ) :=
        mod_cast Q_mono Al32_hyp hm1 hkge
      rw [abs_mul, abs_of_nonneg (hgd_nonneg k)]
      calc (gd Al32 Al32_hyp k n : ℝ) * |epsilon k|
          ≤ (gd Al32 Al32_hyp k n : ℝ) * (1 / (Q Al32 (k + 1) : ℝ)) :=
            mul_le_mul_of_nonneg_left (le_of_lt (epsilon_lt k (eps_bound k hk))) (hgd_nonneg k)
        _ ≤ (gd Al32 Al32_hyp k n : ℝ) * (1 / (Q Al32 m : ℝ)) := by
          exact mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hQ_m_pos hQ_le) (hgd_nonneg k)
        _ = _ := by ring_nf
    -- Triangle inequality: |sum| ≤ ∑ |...|
    have h1 : |∑ k in Finset.Ico m (topIdx Al32 Al32_hyp n + 1),
        (gd Al32 Al32_hyp k n : ℝ) * epsilon k| ≤
      ∑ k in Finset.Ico m (topIdx Al32 Al32_hyp n + 1),
          |(gd Al32 Al32_hyp k n : ℝ) * epsilon k| :=
      Finset.abs_sum_le_sum_abs _ _
    -- ∑ |...| ≤ ∑ gd / Q(m)
    have h2 :
        ∑ k in Finset.Ico m (topIdx Al32 Al32_hyp n + 1),
            |(gd Al32 Al32_hyp k n : ℝ) * epsilon k| ≤
          ∑ k in Finset.Ico m (topIdx Al32 Al32_hyp n + 1),
            (gd Al32 Al32_hyp k n : ℝ) / (Q Al32 m : ℝ) :=
      Finset.sum_le_sum pointwise
    -- ∑ gd(k,n) / Q(m) ≤ n / Q(m)
    have h3 :
        ∑ k in Finset.Ico m (topIdx Al32 Al32_hyp n + 1),
            (gd Al32 Al32_hyp k n : ℝ) / (Q Al32 m : ℝ) ≤
          (n : ℝ) / (Q Al32 m : ℝ) := by
      rw [← Finset.sum_div]
      have h_le_n : (∑ k in Finset.Ico m (topIdx Al32 Al32_hyp n + 1),
          (gd Al32 Al32_hyp k n : ℝ)) ≤ (n : ℝ) := by
        have h_sub : Finset.Ico m (topIdx Al32 Al32_hyp n + 1) ⊆
            Finset.range (topIdx Al32 Al32_hyp n + 1) :=
          fun _ hk => Finset.mem_range.mpr (Finset.mem_Ico.mp hk).2
        have hsdiff := Finset.sum_sdiff h_sub (f := fun k => (gd Al32 Al32_hyp k n : ℝ) * (Q Al32 k : ℝ))
        have h_le_ico : (∑ k in Finset.Ico m (topIdx Al32 Al32_hyp n + 1),
            (gd Al32 Al32_hyp k n : ℝ)) ≤
          ∑ k in Finset.Ico m (topIdx Al32 Al32_hyp n + 1),
            (gd Al32 Al32_hyp k n : ℝ) * (Q Al32 k : ℝ) := by
          apply Finset.sum_le_sum
          intro k _
          have hQ1 : 1 ≤ (Q Al32 k : ℝ) := by exact_mod_cast Nat.succ_le_of_lt (Q_pos k)
          linarith [mul_le_mul_of_nonneg_left hQ1 (hgd_nonneg k)]
        have h_rest_nonneg : 0 ≤
            ∑ k in (Finset.range (topIdx Al32 Al32_hyp n + 1) \ Finset.Ico m (topIdx Al32 Al32_hyp n + 1)),
            (gd Al32 Al32_hyp k n : ℝ) * (Q Al32 k : ℝ) := by
          apply Finset.sum_nonneg
          intro k _
          apply mul_nonneg (hgd_nonneg k) (by exact_mod_cast Nat.zero_le _)
        -- hsdiff : rest + ico_sum = total_sum
        -- ico_gd ≤ ico_sum
        -- 0 ≤ rest
        -- ico_gd ≤ ico_sum ≤ rest + ico_sum = total = n
        have h_ico_le_total :
            ∑ k in Finset.Ico m (topIdx Al32 Al32_hyp n + 1),
              (gd Al32 Al32_hyp k n : ℝ) * (Q Al32 k : ℝ) ≤
            ∑ k in Finset.range (topIdx Al32 Al32_hyp n + 1),
              (gd Al32 Al32_hyp k n : ℝ) * (Q Al32 k : ℝ) := by
          have := hsdiff
          linarith
        have h_total_eq_n :
            ∑ k in Finset.range (topIdx Al32 Al32_hyp n + 1),
              (gd Al32 Al32_hyp k n : ℝ) * (Q Al32 k : ℝ) = (n : ℝ) :=
          (ostrowski_representation n hpos).symm
        linarith [h_le_ico, h_ico_le_total, h_total_eq_n]
      exact div_le_div_of_nonneg_right h_le_n hQ_m_pos.le
    -- Strict bound: one term (topIdx) has strict inequality from epsilon_lt
    have h_top_mem : topIdx Al32 Al32_hyp n ∈ Finset.Ico m (topIdx Al32 Al32_hyp n + 1) := by
      refine Finset.mem_Ico.mpr ⟨?_, lt_add_one _⟩
      obtain ⟨k₀, hk₀⟩ := Finset.nonempty_iff_ne_empty.mpr h_range
      have := Finset.mem_Ico.mp hk₀
      exact this.1.trans (Nat.le_of_lt_succ this.2)
    have h_gd_top_pos : 0 < gd Al32 Al32_hyp (topIdx Al32 Al32_hyp n) n :=
      (gd_eq_top_of Al32_hyp hpos rfl) ▸ Nat.div_pos (topIdx_lo Al32_hyp hpos) (Q_pos (A := Al32) _)
    have h_gd_top_pos_real : 0 < (gd Al32 Al32_hyp (topIdx Al32 Al32_hyp n) n : ℝ) :=
      mod_cast h_gd_top_pos
    have h_top_strict :
        |(gd Al32 Al32_hyp (topIdx Al32 Al32_hyp n) n : ℝ) * epsilon (topIdx Al32 Al32_hyp n)| <
        (gd Al32 Al32_hyp (topIdx Al32 Al32_hyp n) n : ℝ) / (Q Al32 m : ℝ) := by
      have htop := Finset.mem_Ico.mp h_top_mem
      rw [abs_mul, abs_of_nonneg (hgd_nonneg _)]
      have hQ_le : (Q Al32 m : ℝ) ≤ (Q Al32 (topIdx Al32 Al32_hyp n + 1) : ℝ) :=
        mod_cast Q_mono Al32_hyp hm1 (le_trans htop.1 (Nat.le_succ _))
      calc _ < (gd Al32 Al32_hyp _ n : ℝ) * (1 / (Q Al32 (topIdx Al32 Al32_hyp n + 1) : ℝ)) :=
            mul_lt_mul_of_pos_left (epsilon_lt _ hbound) h_gd_top_pos_real
      _ ≤ (gd Al32 Al32_hyp _ n : ℝ) * (1 / (Q Al32 m : ℝ)) :=
            mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hQ_m_pos hQ_le) (hgd_nonneg _)
      _ = _ := by ring_nf
    have h_strict_sum :
        ∑ k in Finset.Ico m (topIdx Al32 Al32_hyp n + 1),
            |(gd Al32 Al32_hyp k n : ℝ) * epsilon k| <
        ∑ k in Finset.Ico m (topIdx Al32 Al32_hyp n + 1),
            (gd Al32 Al32_hyp k n : ℝ) / (Q Al32 m : ℝ) :=
      Finset.sum_lt_sum pointwise ⟨topIdx Al32 Al32_hyp n, h_top_mem, h_top_strict⟩
    exact lt_of_le_of_lt h1 (lt_of_lt_of_le h_strict_sum h3)

end ErdosTernary.RotationDecomp
