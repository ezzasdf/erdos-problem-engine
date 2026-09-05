/-
  Leading Digits: Connection between fractional parts and leading ternary digit blocks.

  For α = log₃(2), the leading 30-digit block of 2^r in base 3 is determined
  by {r · α} via:

    2^r = 3^{rα} = 3^{⌊rα⌋} · 3^{{rα}}

  The leading block equals ⌊3^{{rα}+29}⌋ (for r large enough).

  C30Lead captures: {x ∈ [0,1) : ⌊3^{x+29}⌋ has no digit 2 in base 3}.

  The corollary: {rα} ∉ C30Lead ⟹ ¬memCantorNat(2^r), because if 2^r is in the
  Cantor set (all digits 0 or 1), then the leading block has no digit 2.
-/

import Mathlib.Tactic
import Mathlib.Data.Real.Irrational
import Mathlib.Data.Nat.Digits
import ErdosTernary.Narkiewicz

open Narkiewicz

namespace ErdosTernary.LeadingDigits

/-- α = log₃(2) -/
noncomputable def α : ℝ := Real.logb 3 2

/-- 2^r = 3^{r·α}

    Proof chain:
      3^α = 3^{logb 3 2} = 2          [by Real.rpow_logb]
      (3^α)^r = 2^r                    [by rewriting]
      (3^α)^r = 3^{α · r}             [by Real.rpow_mul_natCast]
      3^{α · r} = 3^{r · α}           [by ring]
-/
theorem pow2_eq_rpow3 (r : ℕ) : (2 : ℝ) ^ r = (3 : ℝ) ^ ((r : ℝ) * α) := by
  -- Step 1: 3^α = 2
  have h3a : (3 : ℝ) ^ α = 2 :=
    Real.rpow_logb (by norm_num : (0 : ℝ) < 3) (by norm_num : (3 : ℝ) ≠ 1) (by norm_num : (0 : ℝ) < 2)
  -- Rewrite 2^r as (3^α)^r
  rw [← h3a]
  -- Now goal: (3^α)^r = 3^{r · α}
  -- Use rpow_mul_natCast: x^(y*n) = (x^y)^n
  conv_lhs => rw [← (Real.rpow_mul_natCast (by positivity) α r)]
  -- Now goal: 3^{α · r} = 3^{r · α}
  ring_nf

/-- The leading 30-digit block of 2^r in base 3.
    For r large enough (rα ≥ 29), this is a 30-digit number in [3^29, 3^30). -/
noncomputable def leadingBlock (r : ℕ) : ℕ :=
  Int.toNat ⌊(3 : ℝ) ^ (Int.fract ((r : ℝ) * α) + 29)⌋

/-- C30Lead: the set of x ∈ [0,1) whose leading 30-digit block ⌊3^{x+29}⌋
    has no digit 2 in base 3. This is the "correct" forbidden set for the
    leading-digit condition. -/
def C30Lead (x : ℝ) : Prop :=
  0 ≤ x ∧ x < 1 ∧
  ∀ k < 30, digit₃ (Int.toNat ⌊(3 : ℝ) ^ (x + 29)⌋) k ≠ 2

/-- Key identity: 3^{fract(x) + 29} = 3^x · 3^{(29:ℝ) - ⌊x⌋} -/
theorem rpow_fract_add (x : ℝ) :
    (3 : ℝ) ^ (Int.fract x + 29) = (3 : ℝ) ^ x * (3 : ℝ) ^ ((29 : ℝ) - ↑(Int.floor x)) := by
  have h1 : (Int.fract x + 29 : ℝ) = (x + ((29 : ℝ) - ↑(Int.floor x)) : ℝ) := by
    unfold Int.fract; ring
  rw [h1, Real.rpow_add (by norm_num : (0 : ℝ) < 3)]

/-- digit₃_mul_pow_three: Multiplying by 3^m shifts digits left.
    digit₃ (n * 3^m) k = 0 if k < m, digit₃ n (k-m) if k ≥ m. -/
theorem digit₃_mul_pow_three (n m k : ℕ) :
    (n * 3 ^ m / 3 ^ k) % 3 = if k < m then 0 else (n / 3 ^ (k - m)) % 3 := by
  by_cases h : k < m
  · rw [if_pos h]
    have key : n * 3 ^ m / 3 ^ k = n * 3 ^ (m - k) := by
      have h1 : n * 3 ^ m = n * 3 ^ (m - k) * 3 ^ k := by
        conv_lhs => rw [show m = (m - k) + k from by omega, Nat.pow_add]
        ring
      rw [h1, mul_comm _ (3 ^ k), Nat.mul_div_cancel_left _ (pow_pos (by norm_num) k)]
    rw [key]
    obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le (by omega : 1 ≤ m - k)
    rw [hj, show (1 : ℕ) + j = j + 1 from by omega, Nat.pow_add_one]
    simp [Nat.mul_mod, show (3 : ℕ) % 3 = 0 from by rfl, Nat.zero_mul, Nat.zero_mod]
  · rw [if_neg h]
    have key : n * 3 ^ m / 3 ^ k = n / 3 ^ (k - m) := by
      calc n * 3 ^ m / 3 ^ k
          = n * 3 ^ m / 3 ^ (m + (k - m)) := by conv_lhs => rw [show k = m + (k - m) from by omega]
        _ = n * 3 ^ m / (3 ^ m * 3 ^ (k - m)) := by rw [Nat.pow_add]
        _ = n * 3 ^ m / 3 ^ m / 3 ^ (k - m) := by rw [← Nat.div_div_eq_div_mul]
        _ = (3 ^ m * n) / 3 ^ m / 3 ^ (k - m) := by rw [mul_comm n (3 ^ m)]
        _ = n / 3 ^ (k - m) := by rw [Nat.mul_div_cancel_left n (pow_pos (by norm_num) m)]
    rw [key]

/-- α > 0 since log₃(2) > log₃(1) = 0 -/
theorem alpha_pos : 0 < α := by
  unfold α; exact Real.logb_pos (by norm_num) (by norm_num)

theorem r_mul_alpha_nonneg (r : ℕ) : 0 ≤ (r : ℝ) * α :=
  mul_nonneg (Nat.cast_nonneg r) alpha_pos.le

/-- For x ≥ 0, the ℤ→ℝ cast of ⌊x⌋ equals the ℕ→ℝ cast of Int.toNat ⌊x⌋.
    This bridges Int.floor (ℤ) and Int.toNat (ℕ) through ℝ. -/
theorem floor_cast (x : ℝ) (hx : 0 ≤ x) :
    ((Int.floor x : ℤ) : ℝ) = ((Int.toNat (Int.floor x) : ℕ) : ℝ) := by
  have := (Int.toNat_of_nonneg (Int.floor_nonneg.mpr hx)).symm
  rw [this]; norm_cast

/-- floor of exact natural number cast is the natural number itself -/
theorem toNat_floor_nat (n : ℕ) : (Int.floor (↑n : ℝ)).toNat = n := by
  rw [Int.floor_toNat, Nat.floor_natCast]

/-- Int.toNat of floor of nat division is nat division -/
theorem floor_natdiv (a b : ℕ) :
    (Int.floor ((a : ℝ) / (b : ℝ))).toNat = a / b := by
  rw [Int.floor_toNat, Nat.floor_div_eq_div]

/-- Case 1 (n ≤ 29): 3^{fract(rα)+29} = ↑(2^r · 3^{29-n}) as exact ℝ of ℕ -/
private theorem h_val_le (r n : ℕ) (_h : n ≤ 29)
    (hn : n = Int.toNat (Int.floor ((r : ℝ) * α))) :
    (3 : ℝ) ^ (Int.fract ((r : ℝ) * α) + 29) = ((2 ^ r * 3 ^ (29 - n) : ℕ) : ℝ) := by
  rw [rpow_fract_add, ← pow2_eq_rpow3,
      floor_cast ((r : ℝ) * α) (r_mul_alpha_nonneg r), ← hn]
  norm_cast

/-- Case 2 (n > 29): 3^{fract(rα)+29} = ↑(2^r) / ↑(3^{n-29}) as ℝ quotient -/
private theorem h_val_gt (r n : ℕ) (h : n > 29)
    (hn : n = Int.toNat (Int.floor ((r : ℝ) * α))) :
    (3 : ℝ) ^ (Int.fract ((r : ℝ) * α) + 29) =
    ((2 ^ r : ℕ) : ℝ) / ((3 ^ (n - 29) : ℕ) : ℝ) := by
  rw [rpow_fract_add, ← pow2_eq_rpow3,
      floor_cast ((r : ℝ) * α) (r_mul_alpha_nonneg r), ← hn]
  have hexp : (3 : ℝ) ^ ((29 : ℝ) - (n : ℝ)) =
      ((3 : ℝ) ^ ((n - 29 : ℕ) : ℝ))⁻¹ := by
    have : (29 : ℝ) - (n : ℝ) = -((n - 29 : ℕ) : ℝ) := by
      have : (n : ℝ) = ↑(n - 29) + (29 : ℝ) := by
        rw [← Nat.sub_add_cancel (by omega : 29 ≤ n)]; norm_cast
      linarith
    rw [this, Real.rpow_neg (by norm_num : (0:ℝ) ≤ 3) ((n - 29 : ℕ) : ℝ)]
  rw [hexp]; field_simp

/-- memCantorNat(2^r) ⟹ {rα} ∈ C30Lead -/
theorem memCantor_imp_mem_C30Lead (r : ℕ)
    (hCant : memCantorNat (2 ^ r)) :
    C30Lead (Int.fract ((r : ℝ) * α)) := by
  refine ⟨Int.fract_nonneg _, Int.fract_lt_one _, fun k hk => ?_⟩
  set n := Int.toNat (Int.floor ((r : ℝ) * α)) with hn_def
  by_cases h : n ≤ 29
  · -- Case 1: n ≤ 29. Then 3^{fract(rα)+29} = ↑(2^r * 3^{29-n}).
    -- Floor of exact ℕ cast is itself, so leadingBlock = 2^r * 3^{29-n}.
    -- digit₃_mul_pow_three splits: digits < (29-n) are 0, rest come from 2^r.
    have hblock : Int.toNat ⌊(3 : ℝ) ^ (Int.fract ((r : ℝ) * α) + 29)⌋ =
        2 ^ r * 3 ^ (29 - n) := by
      rw [show (3 : ℝ) ^ (Int.fract ((r : ℝ) * α) + 29) =
            ((2 ^ r * 3 ^ (29 - n) : ℕ) : ℝ) from h_val_le r n h hn_def]
      exact toNat_floor_nat (2 ^ r * 3 ^ (29 - n))
    rw [hblock]
    unfold Narkiewicz.digit₃
    rw [digit₃_mul_pow_three]
    by_cases hk2 : k < 29 - n
    · simp [hk2]
    · simp [hk2]; exact hCant (k - (29 - n))
  · -- Case 2: n > 29. Then 3^{fract(rα)+29} = ↑(2^r) / ↑(3^{n-29}).
    -- Floor of nat division by nat division via floor_natdiv.
    -- digit₃_div_pow shifts: digit₃(2^r / 3^{n-29}) k = digit₃(2^r)(n-29+k).
    have hblock : Int.toNat ⌊(3 : ℝ) ^ (Int.fract ((r : ℝ) * α) + 29)⌋ =
        2 ^ r / 3 ^ (n - 29) := by
      rw [show (3 : ℝ) ^ (Int.fract ((r : ℝ) * α) + 29) =
            ((2 ^ r : ℕ) : ℝ) / ((3 ^ (n - 29) : ℕ) : ℝ) from h_val_gt r n (by omega) hn_def]
      exact floor_natdiv (2 ^ r) (3 ^ (n - 29))
    rw [hblock, digit₃_div_pow]
    exact hCant (n - 29 + k)

/-- Main corollary: if {rα} ∉ C30Lead, then 2^r is not in the Cantor set. -/
theorem not_mem_C30Lead_not_cantor (r : ℕ)
    (h : ¬C30Lead (Int.fract ((r : ℝ) * α))) :
    ¬memCantorNat (2 ^ r) :=
  fun hCant => h (memCantor_imp_mem_C30Lead r hCant)

end ErdosTernary.LeadingDigits
