import Mathlib.Algebra.ContinuedFractions.Basic
import Mathlib.Algebra.ContinuedFractions.Computation.Basic
import Mathlib.Algebra.ContinuedFractions.Computation.Approximations
import Mathlib.Algebra.ContinuedFractions.Computation.TerminatesIffRat
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Real.Irrational

namespace ErdosTernary.ContinuedFraction

/-- α = log₃(2) -/
noncomputable def log3_2 : ℝ := Real.logb 3 2

private theorem pow3_not_dvd2 (p : ℕ) : ¬ 2 ∣ 3 ^ p := by
  suffices h : ∀ n, 3 ^ n % 2 = 1 from fun h2 => by
    have := h p; have := Nat.mod_eq_zero_of_dvd h2; omega
  intro n; induction n with
  | zero => simp
  | succ n ih => simp [Nat.pow_succ]; omega

private theorem dvd_two_pow (n : ℕ) (h : 0 < n) : 2 ∣ 2 ^ n := by
  cases n with
  | zero => contradiction
  | succ n => exact ⟨2 ^ n, by simp [Nat.pow_succ]; ring⟩

/-- log₃(2) is irrational -/
theorem log3_2_irrational : Irrational log3_2 := by
  intro ⟨r, hr⟩
  have h3r2 : (3 : ℝ) ^ (r : ℝ) = 2 := by
    have h := @Real.rpow_logb 3 2 (by norm_num) (by norm_num) (by norm_num)
    rw [hr]; exact h
  have hmul : (r : ℝ) * (r.den : ℝ) = (r.num : ℝ) := by
    simp only [Rat.cast_def]; field_simp
  have hpow : (3 : ℝ) ^ (r.num : ℝ) = (2 : ℝ) ^ (r.den : ℝ) := by
    have h1 : ((3 : ℝ) ^ (r : ℝ)) ^ (r.den : ℝ) = (2 : ℝ) ^ (r.den : ℝ) := by rw [h3r2]
    rw [← Real.rpow_mul (by norm_num : 0 ≤ (3:ℝ)), hmul] at h1
    exact h1
  have hcases : 0 ≤ r.num ∨ r.num < 0 := Int.le_or_lt 0 r.num
  cases hcases with
  | inl hpos =>
    have heq_nn : 3 ^ r.num.toNat = 2 ^ r.den := by
      have key : (3 : ℝ) ^ ((r.num.toNat : ℕ) : ℝ) = (2 : ℝ) ^ ((r.den : ℕ) : ℝ) := by
        rw [show ((r.den : ℕ) : ℝ) = (r.den : ℝ) from by norm_cast]
        rw [show ((r.num.toNat : ℕ) : ℝ) = (r.num : ℝ) from by
          show ((r.num.toNat : ℕ) : ℝ) = (r.num : ℝ)
          exact_mod_cast (show (r.num.toNat : ℤ) = r.num from Int.toNat_of_nonneg hpos)]
        exact hpow
      rw [Real.rpow_natCast, Real.rpow_natCast] at key
      exact_mod_cast key
    have hdvd : 2 ∣ 2 ^ r.den := dvd_two_pow r.den r.pos
    exact pow3_not_dvd2 r.num.toNat (heq_nn ▸ hdvd)
  | inr hneg =>
    have hrn : (r.num : ℝ) < 0 := by norm_cast
    have h3lt1 : (3 : ℝ) ^ (r.num : ℝ) < 1 := by
      rw [show (1:ℝ) = (3:ℝ) ^ (0:ℝ) from (Real.rpow_zero 3).symm]
      exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ) < 3) hrn
    have h2ge2 : (2 : ℝ) ^ (r.den : ℝ) ≥ 2 := by
      have hd1 : 1 ≤ r.den := Nat.succ_le_of_lt r.pos
      have h21 : (2 : ℝ) ^ (1 : ℝ) ≤ (2 : ℝ) ^ (r.den : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) (by exact_mod_cast hd1 : (1:ℝ) ≤ (r.den:ℝ))
      linarith [show (2:ℝ) ^ (1:ℝ) = 2 from Real.rpow_one 2]
    linarith [show (2:ℝ) ^ (r.den : ℝ) = (3:ℝ) ^ (r.num : ℝ) from hpow ▸ rfl]

/-- The continued fraction of log₃(2) -/
noncomputable def log3_2_cf : GenContFract ℝ :=
  GenContFract.of log3_2

/-- log₃(2) CF is well-formed (numerators = 1, denominators > 0) -/
theorem log3_2_cf_isWellFormed : log3_2_cf.IsSimpContFract :=
  GenContFract.of_isSimpContFract log3_2

/-- log₃(2) CF never terminates (since it is irrational) -/
theorem log3_2_not_terminatedAt (n : ℕ) : ¬log3_2_cf.TerminatedAt n := by
  intro h_term
  have h_not_irrational : ¬Irrational log3_2 := by
    intro h_irr
    have h_not_terminates : ¬log3_2_cf.Terminates :=
      mt (GenContFract.terminates_iff_rat log3_2).mp
        (fun ⟨q, hq⟩ => h_irr ⟨q, hq.symm⟩)
    exact h_not_terminates ⟨n, h_term⟩
  exact h_not_irrational log3_2_irrational

/-- log₃(2) > 0, since 2 > 1 = 3^0 and 3 > 1 -/
theorem log3_2_pos : 0 < log3_2 :=
  Real.logb_pos (by norm_num : (1:ℝ) < 3) (by norm_num : (1:ℝ) < 2)

/-- log₃(2) < 1, since 2 < 3 = 3^1 and 3 > 1 -/
theorem log3_2_lt_one : log3_2 < 1 :=
  (Real.logb_lt_iff_lt_rpow (by norm_num : (1:ℝ) < 3) (by norm_num : (0:ℝ) < 2)).mpr
    (by norm_num : (2:ℝ) < 3 ^ (1:ℝ))

/-- ⌊log₃(2)⌋ = 0, since 0 ≤ log₃(2) < 1 -/
theorem log3_2_floor_eq_zero : ⌊log3_2⌋ = 0 := by
  rw [Int.floor_eq_iff]
  constructor
  · show (Int.cast 0 : ℝ) ≤ log3_2
    simp
    exact le_of_lt log3_2_pos
  · show log3_2 < (Int.cast 0 : ℝ) + 1
    simp
    exact log3_2_lt_one

/-- Error bound: |log₃(2) - convs n| ≤ 1/(dens n * dens (n+1)) -/
theorem log3_2_convs_error (n : ℕ) :
    |log3_2 - log3_2_cf.convs n| ≤ 1 / (log3_2_cf.dens n * log3_2_cf.dens (n + 1)) :=
  GenContFract.abs_sub_convs_le (log3_2_not_terminatedAt n)

end ErdosTernary.ContinuedFraction
