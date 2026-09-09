import Mathlib.Tactic
import ErdosTernary.BridgeCompute

open ErdosTernary.BridgeCompute

namespace ErdosTernary.Lifting

def ternaryDigit (n k : Nat) : Nat :=
  (n / 3 ^ k) % 3

-- ============================================================
-- Phase 1: Core Algebraic Identity (no sorry)
-- ============================================================

private theorem cubic_one_plus (K : Nat) (hK : K ≥ 1) :
    (1 + 3 ^ K) ^ 3 % 3 ^ (K + 2) = 1 + 3 ^ (K + 1) := by
  have hlt : 1 + 3 ^ (K + 1) < 3 ^ (K + 2) := by
    calc 1 + 3 ^ (K + 1) < 3 ^ (K + 1) + 3 ^ (K + 1) := by norm_num
      _ = 2 * 3 ^ (K + 1) := by ring
      _ ≤ 3 * 3 ^ (K + 1) := Nat.mul_le_mul_right _ (by norm_num : (2 : Nat) ≤ 3)
      _ = 3 ^ (K + 2) := by ring_nf
  have hfac : (1 + 3 ^ K) ^ 3 = (1 + 3 ^ (K + 1)) + 3 ^ (K + 2) * (3 ^ (K - 1) + 3 ^ (2 * K - 2)) := by
    rw [show (1 + 3 ^ K) ^ 3 = 1 + 3 ^ (K + 1) + 3 ^ (2 * K + 1) + 3 ^ (3 * K) from by ring_nf]
    rw [show 3 ^ (2 * K + 1) = 3 ^ (K + 2) * 3 ^ (K - 1) from by rw [show 2 * K + 1 = (K + 2) + (K - 1) from by omega]; ring_nf]
    rw [show 3 ^ (3 * K) = 3 ^ (K + 2) * 3 ^ (2 * K - 2) from by rw [show 3 * K = (K + 2) + (2 * K - 2) from by omega]; ring_nf]
    ring
  rw [hfac, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

private theorem cube_mod_helper (r t m : Nat) (hm : m ≥ 1) :
    (r + t * 3 ^ m) ^ 3 % 3 ^ (m + 1) = r ^ 3 % 3 ^ (m + 1) := by
  have hfac : (r + t * 3 ^ m) ^ 3 = r ^ 3 + 3 ^ (m + 1) * (r ^ 2 * t + 3 ^ m * (r * t ^ 2) + 3 ^ (2 * m - 1) * t ^ 3) := by
    rw [show (r + t * 3 ^ m) ^ 3 = r ^ 3 + 3 * r ^ 2 * (t * 3 ^ m) + 3 * r * (t * 3 ^ m) ^ 2 + (t * 3 ^ m) ^ 3 from by ring]
    have h1 : 3 * r ^ 2 * (t * 3 ^ m) = 3 ^ (m + 1) * (r ^ 2 * t) := by ring_nf
    have h2 : 3 * r * (t * 3 ^ m) ^ 2 = 3 ^ (m + 1) * (3 ^ m * (r * t ^ 2)) := by ring_nf
    have h3 : (t * 3 ^ m) ^ 3 = 3 ^ (m + 1) * (3 ^ (2 * m - 1) * t ^ 3) := by
      rw [show (t * 3 ^ m) ^ 3 = t ^ 3 * 3 ^ (3 * m) from by ring]
      rw [show 3 * m = (m + 1) + (2 * m - 1) from by omega]; ring_nf
    rw [h1, h2, h3]; ring
  rw [hfac, Nat.add_mul_mod_self_left]

private theorem cubic_lift (a b m : Nat) (hm : m ≥ 1) (h : a % 3 ^ m = b % 3 ^ m) :
    a ^ 3 % 3 ^ (m + 1) = b ^ 3 % 3 ^ (m + 1) := by
  have ha : a = a % 3 ^ m + a / 3 ^ m * 3 ^ m := by rw [show a % 3 ^ m + a / 3 ^ m * 3 ^ m = 3 ^ m * (a / 3 ^ m) + a % 3 ^ m from by ring]; exact (Nat.div_add_mod a (3^m)).symm
  have hb : b = b % 3 ^ m + b / 3 ^ m * 3 ^ m := by rw [show b % 3 ^ m + b / 3 ^ m * 3 ^ m = 3 ^ m * (b / 3 ^ m) + b % 3 ^ m from by ring]; exact (Nat.div_add_mod b (3^m)).symm
  rw [ha, hb, h, cube_mod_helper (b % 3 ^ m) (a / 3 ^ m) m hm, cube_mod_helper (b % 3 ^ m) (b / 3 ^ m) m hm]

theorem pow2_uK_mod (K : Nat) (hK : K ≥ 1) :
    2 ^ uK K % 3 ^ (K + 1) = 1 + 3 ^ K := by
  revert hK
  induction K using Nat.strongRecOn with
  | _ K ih =>
    intro hK
    match K with
    | 0 => contradiction
    | 1 => norm_num [uK]
    | K + 2 =>
      have ih_val := ih (K + 1) (by omega) (by omega)
      have h_uK : uK (K + 2) = 3 * uK (K + 1) := by simp [uK]; omega
      rw [h_uK, show 3 * uK (K + 1) = uK (K + 1) * 3 from by ring, Nat.pow_mul]
      have h_bmod : (1 + 3 ^ (K + 1)) % 3 ^ (K + 2) = 1 + 3 ^ (K + 1) := by
        apply Nat.mod_eq_of_lt
        calc 1 + 3 ^ (K + 1) < 3 ^ (K + 1) + 3 ^ (K + 1) := by norm_num
          _ = 2 * 3 ^ (K + 1) := by ring
          _ ≤ 3 * 3 ^ (K + 1) := Nat.mul_le_mul_right _ (by norm_num : (2 : Nat) ≤ 3)
          _ = 3 ^ (K + 2) := by ring_nf
      have ih_mod := show 2 ^ uK (K + 1) % 3 ^ (K + 2) = (1 + 3 ^ (K + 1)) % 3 ^ (K + 2) from by rw [ih_val, h_bmod]
      have h_cubic := cubic_lift (2 ^ uK (K + 1)) (1 + 3 ^ (K + 1)) (K + 2) (by omega) ih_mod
      rw [show K + 2 + 1 = K + 3 from by omega] at h_cubic
      rw [h_cubic]; exact cubic_one_plus (K + 1) (by omega)

-- ============================================================
-- Phase 2: Digit extraction (no sorry)
-- ============================================================

def kthDigit (K r j : Nat) : Nat :=
  ternaryDigit (2 ^ (r + j * uK K)) K

/-- A*3^K mod 3^{K+1} = (A mod 3)*3^K -/
private theorem mul_pow_mod (A K : Nat) (_hK : K ≥ 1) :
    A * 3 ^ K % 3 ^ (K + 1) = (A % 3) * 3 ^ K := by
  have h := (Nat.div_add_mod A 3).symm
  conv_lhs => rw [show A = 3 * (A / 3) + A % 3 from h]
  rw [show (3 * (A / 3) + A % 3) * 3 ^ K = 3 * (A / 3) * 3 ^ K + A % 3 * 3 ^ K from by ring]
  rw [show 3 * (A / 3) * 3 ^ K = (A / 3) * (3 * 3 ^ K) from by ring]
  rw [show 3 * 3 ^ K = 3 ^ (K + 1) from by ring]
  rw [show (A / 3) * 3 ^ (K + 1) = 3 ^ (K + 1) * (A / 3) from by ring]
  rw [show 3 ^ (K + 1) * (A / 3) + A % 3 * 3 ^ K = A % 3 * 3 ^ K + 3 ^ (K + 1) * (A / 3) from by ring]
  rw [Nat.add_mul_mod_self_left]
  apply Nat.mod_eq_of_lt
  have hmod := Nat.mod_lt A (by norm_num : 3 > 0)
  rw [Nat.pow_succ, mul_comm (3 ^ K) 3]
  exact mul_lt_mul_of_pos_right hmod (Nat.pow_pos (by norm_num : 0 < 3))

/-- Key digit extraction: (A + s*3^K) mod 3^{K+1} / 3^K % 3 = (A/3^K + s) % 3 -/
private theorem digit_add_mul_pow (A s K : Nat) (_hK : K ≥ 1) (_hs : s < 3) (hA : A < 3 ^ (K + 1)) :
    (A + s * 3 ^ K) % 3 ^ (K + 1) / 3 ^ K % 3 = (A / 3 ^ K + s) % 3 := by
  have hKpos : 3 ^ K > 0 := Nat.pow_pos (by norm_num : 0 < 3)
  have hR : A % 3 ^ K < 3 ^ K := Nat.mod_lt A hKpos
  rw [show (A + s * 3 ^ K) % 3 ^ (K + 1) =
    (A % 3 ^ (K + 1) + (s * 3 ^ K) % 3 ^ (K + 1)) % 3 ^ (K + 1) from by simp [Nat.add_mod]]
  rw [Nat.mod_eq_of_lt hA]
  rw [mul_pow_mod s K (by omega : K ≥ 1)]
  have hA' : A = 3 ^ K * (A / 3 ^ K) + A % 3 ^ K := (Nat.div_add_mod A (3 ^ K)).symm
  conv_lhs => rw [hA']
  rw [show 3 ^ K * (A / 3 ^ K) + A % 3 ^ K + s % 3 * 3 ^ K =
    A % 3 ^ K + (A / 3 ^ K + s % 3) * 3 ^ K from by ring]
  rw [show (A % 3 ^ K + (A / 3 ^ K + s % 3) * 3 ^ K) % 3 ^ (K + 1) =
    (A % 3 ^ K % 3 ^ (K + 1) + ((A / 3 ^ K + s % 3) * 3 ^ K) % 3 ^ (K + 1)) % 3 ^ (K + 1)
    from by simp [Nat.add_mod]]
  rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hR (Nat.pow_le_pow_right (by norm_num : 0 < 3) (Nat.le_succ K)))]
  rw [mul_pow_mod (A / 3 ^ K + s % 3) K (by omega : K ≥ 1)]
  have hbound : A % 3 ^ K + (A / 3 ^ K + s % 3) % 3 * 3 ^ K < 3 ^ (K + 1) := by
    have hs' := Nat.mod_lt (A / 3 ^ K + s % 3) (by norm_num : 3 > 0)
    rw [show 3 ^ (K + 1) = 3 * 3 ^ K from by ring]
    nlinarith
  rw [Nat.mod_eq_of_lt hbound]
  rw [Nat.add_mul_div_right (A % 3 ^ K) ((A / 3 ^ K + s % 3) % 3) hKpos]
  rw [(Nat.div_eq_zero_iff hKpos).mpr hR, Nat.zero_add]
  omega

/-- K-th digit of A*(1+3^K) mod 3^{K+1} = (A/3^K + A%3) % 3 -/
theorem digit_mul_one_plus (A K : Nat) (hK : K ≥ 1) (hA : A < 3 ^ (K + 1)) :
    (A * (1 + 3 ^ K)) % 3 ^ (K + 1) / 3 ^ K % 3 = (A / 3 ^ K + A % 3) % 3 := by
  rw [show A * (1 + 3 ^ K) = A + A * 3 ^ K from by ring]
  have h1 : (A + A * 3 ^ K) % 3 ^ (K + 1) = (A + (A % 3) * 3 ^ K) % 3 ^ (K + 1) := by
    rw [show (A + A * 3 ^ K) % 3 ^ (K + 1) =
      (A % 3 ^ (K + 1) + (A * 3 ^ K) % 3 ^ (K + 1)) % 3 ^ (K + 1) from by simp [Nat.add_mod]]
    rw [Nat.mod_eq_of_lt hA, mul_pow_mod A K hK]
  rw [h1]
  exact digit_add_mul_pow A (A % 3) K hK (Nat.mod_lt A (by norm_num : 3 > 0)) hA

/-- The K-th digit of 2^{r+uK K} depends on 2^r mod 3^{K+1} and 2^r mod 3^K -/
theorem kthDigit_step (K r : Nat) (hK : K ≥ 1) :
    kthDigit K r 1 = ((2 ^ r % 3 ^ (K + 1) / 3 ^ K) + (2 ^ r % 3 ^ K)) % 3 := by
  unfold kthDigit ternaryDigit
  rw [show 2 ^ (r + 1 * uK K) = 2 ^ r * 2 ^ (uK K) from by ring]
  rw [digit_eq_of_modPow (2 ^ r * 2 ^ uK K) K (K + 1) (by omega)]
  rw [Nat.mul_mod, show 2 ^ uK K % 3 ^ (K + 1) = 1 + 3 ^ K from pow2_uK_mod K hK]
  rw [digit_mul_one_plus (2 ^ r % 3 ^ (K + 1)) K hK (Nat.mod_lt _ (by exact Nat.pow_pos (by omega : 0 < 3)))]
  have h3dvd_K : (3 : Nat) ∣ 3 ^ K := Nat.pow_dvd_pow 3 (by omega : 1 ≤ K)
  have h3dvd_K1 : (3 : Nat) ∣ 3 ^ (K + 1) := Nat.pow_dvd_pow 3 (by omega : 1 ≤ K + 1)
  have hA3 : (2 ^ r % 3 ^ (K + 1)) % 3 = 2 ^ r % 3 := Nat.mod_mod_of_dvd (2 ^ r) h3dvd_K1
  have hB3 : 2 ^ r % 3 ^ K % 3 = 2 ^ r % 3 := Nat.mod_mod_of_dvd (2 ^ r) h3dvd_K
  rw [Nat.add_mod ((2 ^ r % 3 ^ (K + 1)) / 3^K) ((2 ^ r % 3 ^ (K + 1)) % 3) 3]
  rw [show 2 ^ r % 3 ^ (K + 1) % 3 % 3 = 2 ^ r % 3 ^ (K + 1) % 3 from by omega, hA3]
  rw [Nat.add_mod ((2 ^ r % 3 ^ (K + 1)) / 3^K) (2 ^ r % 3 ^ K) 3]
  rw [hB3]

-- ============================================================
-- Phase 3: K-th digit for j=2 (no sorry)
-- ============================================================

/-- (1+3^K)^2 mod 3^{K+1} = 1+2*3^K for K >= 1 -/
private lemma sq_one_plus_pow (K : Nat) (hK : K ≥ 1) :
    (1 + 3 ^ K) ^ 2 % 3 ^ (K + 1) = 1 + 2 * 3 ^ K := by
  have hfac : (1 + 3 ^ K) ^ 2 = 1 + 2 * 3 ^ K + 3 ^ (2 * K) := by ring
  rw [hfac, show 2 * K = (K + 1) + (K - 1) from by omega, Nat.pow_add]
  rw [Nat.add_mul_mod_self_left]
  apply Nat.mod_eq_of_lt
  set x := 3 ^ K
  have hx : x ≥ 3 := by
    rw [show (3 : Nat) = 3 ^ 1 from by norm_num]
    exact Nat.pow_le_pow_right (by omega : 0 < 3) hK
  omega

/-- 2^{2*uK K} mod 3^{K+1} = 1+2*3^K for K >= 1 -/
private lemma pow2_uK_sq (K : Nat) (hK : K ≥ 1) :
    2 ^ (2 * uK K) % 3 ^ (K + 1) = 1 + 2 * 3 ^ K := by
  rw [show 2 * uK K = uK K + uK K from by ring, Nat.pow_add, Nat.mul_mod]
  rw [pow2_uK_mod K hK]
  have : (1 + 3 ^ K) ^ 2 = (1 + 3 ^ K) * (1 + 3 ^ K) := by ring
  rw [← this, sq_one_plus_pow K hK]

/-- K-th digit of A*(1+2*3^K) mod 3^{K+1} = (A/3^K + (A*2)%3) % 3 -/
private lemma digit_mul_one_plus_sq (A K : Nat) (hK : K ≥ 1) (hA : A < 3 ^ (K + 1)) :
    (A * (1 + 2 * 3 ^ K)) % 3 ^ (K + 1) / 3 ^ K % 3 = (A / 3 ^ K + (A * 2) % 3) % 3 := by
  have hAs : (A * 2) % 3 < 3 := Nat.mod_lt _ (by norm_num : 3 > 0)
  rw [show A * (1 + 2 * 3 ^ K) = A + (A * 2) * 3 ^ K from by ring]
  rw [show (A + (A * 2) * 3 ^ K) % 3 ^ (K + 1) =
    (A % 3 ^ (K + 1) + ((A * 2) * 3 ^ K) % 3 ^ (K + 1)) % 3 ^ (K + 1) from by simp [Nat.add_mod]]
  rw [Nat.mod_eq_of_lt hA, mul_pow_mod (A * 2) K hK]
  exact digit_add_mul_pow A ((A * 2) % 3) K hK hAs hA

/-- The K-th digit of 2^{r+2*uK K} depends on 2^r mod 3^{K+1} and 2^r mod 3^K -/
theorem kthDigit_step_2 (K r : Nat) (hK : K ≥ 1) :
    kthDigit K r 2 = ((2 ^ r % 3 ^ (K + 1) / 3 ^ K) + 2 * (2 ^ r % 3 ^ K)) % 3 := by
  unfold kthDigit ternaryDigit
  rw [digit_eq_of_modPow (2 ^ (r + 2 * uK K)) K (K + 1) (by omega)]
  rw [show 2 ^ (r + 2 * uK K) = 2 ^ r * 2 ^ (2 * uK K) from by ring]
  rw [Nat.mul_mod, pow2_uK_sq K hK]
  rw [digit_mul_one_plus_sq (2 ^ r % 3 ^ (K + 1)) K hK (Nat.mod_lt _ (Nat.pow_pos (by omega : 0 < 3)))]
  have h3dvd_K : (3 : Nat) ∣ 3 ^ K := Nat.pow_dvd_pow 3 (by omega : 1 ≤ K)
  have h3dvd_K1 : (3 : Nat) ∣ 3 ^ (K + 1) := Nat.pow_dvd_pow 3 (by omega : 1 ≤ K + 1)
  have hA3 : (2 ^ r % 3 ^ (K + 1)) * 2 % 3 = 2 ^ r % 3 ^ K * 2 % 3 := by
    have h1 : 2 ^ r % 3 ^ (K + 1) % 3 = 2 ^ r % 3 := Nat.mod_mod_of_dvd (2 ^ r) h3dvd_K1
    have h2 : 2 ^ r % 3 ^ K % 3 = 2 ^ r % 3 := Nat.mod_mod_of_dvd (2 ^ r) h3dvd_K
    omega
  omega

/-- For r < uK K and K >= 1, the three K-th digits form an AP with delta = 2^r % 3 -/
theorem digits_arithmetic_progression (K r : Nat) (hK : K ≥ 1) (hr : r < uK K) :
    kthDigit K r 1 = (kthDigit K r 0 + 2 ^ r % 3) % 3 ∧
    kthDigit K r 2 = (kthDigit K r 0 + 2 * (2 ^ r % 3)) % 3 := by
  have h3dvd : (3 : Nat) ∣ 3 ^ K := Nat.pow_dvd_pow 3 (by omega : 1 ≤ K)
  have h3dvd1 : (3 : Nat) ∣ 3 ^ (K + 1) := Nat.pow_dvd_pow 3 (by omega : 1 ≤ K + 1)
  have hmod3 : 2 ^ r % 3 ^ K % 3 = 2 ^ r % 3 := Nat.mod_mod_of_dvd (2 ^ r) h3dvd
  have hmod3_1 : 2 ^ r % 3 ^ (K + 1) % 3 = 2 ^ r % 3 := Nat.mod_mod_of_dvd (2 ^ r) h3dvd1
  constructor
  · rw [kthDigit_step K r hK, show kthDigit K r 0 = (2 ^ r % 3 ^ (K + 1) / 3 ^ K) % 3 from by
      unfold kthDigit ternaryDigit
      rw [show r + 0 * uK K = r from by ring]
      exact digit_eq_of_modPow (2 ^ r) K (K + 1) (by omega)]
    rw [Nat.add_mod ((2 ^ r % 3 ^ (K + 1)) / 3 ^ K) (2 ^ r % 3 ^ K) 3]
    rw [hmod3]
  · rw [kthDigit_step_2 K r hK, show kthDigit K r 0 = (2 ^ r % 3 ^ (K + 1) / 3 ^ K) % 3 from by
      unfold kthDigit ternaryDigit
      rw [show r + 0 * uK K = r from by ring]
      exact digit_eq_of_modPow (2 ^ r) K (K + 1) (by omega)]
    rw [Nat.add_mod ((2 ^ r % 3 ^ (K + 1)) / 3 ^ K) (2 * (2 ^ r % 3 ^ K)) 3]
    rw [Nat.mul_mod 2 (2 ^ r % 3 ^ K) 3, hmod3]
    omega

-- ============================================================
-- Phase 4: Exactly one digit 2 (no sorry)
-- ============================================================

/-- 2^r mod 3 is always 1 or 2 -/
private lemma two_pow_mod3_pos (r : Nat) : 2 ^ r % 3 = 1 ∨ 2 ^ r % 3 = 2 := by
  induction r with
  | zero => norm_num
  | succ r ih =>
    rcases ih with h1 | h2
    · rw [Nat.pow_succ, Nat.mul_mod, h1]; norm_num
    · rw [Nat.pow_succ, Nat.mul_mod, h2]; norm_num

/-- hasTrailingDigit2 false at K >= 1 -> least significant ternary digit != 2 -/
private lemma no_trail_digit0 (val K : Nat) (hK : K ≥ 1)
    (h : hasTrailingDigit2 val K = false) : val % 3 ≠ 2 := by
  unfold hasTrailingDigit2 at h
  intro h2
  have hmem : (0 : Nat) ∈ List.range K := List.mem_range.mpr hK
  have hany_true : (List.range K).any (fun i => (val / 3 ^ i) % 3 == 2) = true := by
    rw [List.any_eq_true]
    refine ⟨0, hmem, ?_⟩
    simp only [Nat.pow_zero, Nat.div_one]
    simp [h2]
  simp_all

/-- For K >= 1, no trailing digit 2 in 2^r mod 3^K implies 2^r % 3 = 1 -/
private lemma mod3_eq_one_of_no_trail2 (K r : Nat) (hK : K ≥ 1)
    (h : hasTrailingDigit2 (2 ^ r % 3 ^ K) K = false) : 2 ^ r % 3 = 1 := by
  have hne2 : 2 ^ r % 3 ^ K % 3 ≠ 2 := no_trail_digit0 _ K hK h
  have h3dvd : (3 : Nat) ∣ 3 ^ K := Nat.pow_dvd_pow 3 (by omega : 1 ≤ K)
  have hmod : 2 ^ r % 3 ^ K % 3 = 2 ^ r % 3 := Nat.mod_mod_of_dvd (2 ^ r) h3dvd
  have hor := two_pow_mod3_pos r
  omega

/-- Among the three K-th digits for lifts j=0,1,2, exactly one equals 2.
    Key for the Erdos conjecture: the AP has delta=1 for N_K members. -/
theorem exactly_one_digit2 (K r : Nat) (hK : K ≥ 1) (hr : r < uK K)
    (htrail : hasTrailingDigit2 (2 ^ r % 3 ^ K) K = false) :
    let d0 := kthDigit K r 0
    List.count 2 [d0, (d0 + 1) % 3, (d0 + 2) % 3] = 1 := by
  have hAP := digits_arithmetic_progression K r hK hr
  have hd0 : kthDigit K r 0 < 3 := by
    unfold kthDigit ternaryDigit
    exact Nat.mod_lt _ (by norm_num : 3 > 0)
  interval_cases d0 : kthDigit K r 0 <;> simp [List.count]

-- ============================================================
-- Phase 5: Exactly two lifts survive (no sorry)
-- ============================================================

/-- 2^{uK K} mod 3^K = 1 (from pow2_uK_mod which gives mod 3^{K+1}) -/
private lemma pow2_uK_mod_of (K : Nat) (hK : K ≥ 1) : 2 ^ uK K % 3 ^ K = 1 := by
  have h := pow2_uK_mod K hK
  have hmod : 2 ^ uK K % 3 ^ (K + 1) % 3 ^ K = 2 ^ uK K % 3 ^ K :=
    Nat.mod_mod_of_dvd (2 ^ uK K) (Nat.pow_dvd_pow 3 (by omega : K ≤ K + 1))
  have heq : (1 + 3 ^ K) % 3 ^ K = 1 := by
    rw [show 1 + 3 ^ K = 1 + 3 ^ K * 1 from by ring, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by
      have := Nat.pow_le_pow_right (by omega : 0 < 3) hK
      omega)
  rw [← hmod, h, heq]

private lemma one_mod_pow3 (K : Nat) (hK : K ≥ 1) : 1 % 3 ^ K = 1 :=
  Nat.mod_eq_of_lt (by
    have := Nat.pow_le_pow_right (by omega : 0 < 3) hK
    omega)

/-- 2^{r + j*uK K} mod 3^K = 2^r mod 3^K -/
lemma pow2_add_uK_mod (K r j : Nat) (hK : K ≥ 1) :
    2 ^ (r + j * uK K) % 3 ^ K = 2 ^ r % 3 ^ K := by
  rw [show 2 ^ (r + j * uK K) = 2 ^ r * 2 ^ (j * uK K) from by ring, Nat.mul_mod]
  have huK1 : 2 ^ uK K % 3 ^ K = 1 := pow2_uK_mod_of K hK
  suffices h : 2 ^ (j * uK K) % 3 ^ K = 1 by
    rw [h, Nat.mul_one]
    exact Nat.mod_eq_of_lt (Nat.mod_lt _ (Nat.pow_pos (by omega : 0 < 3)))
  induction j with
  | zero => simp [Nat.zero_mul, Nat.pow_zero]; exact one_mod_pow3 K hK
  | succ j ih =>
    rw [show (j + 1) * uK K = j * uK K + uK K from by ring, Nat.pow_add, Nat.mul_mod]
    rw [ih, one_mul, huK1, one_mod_pow3 K hK]

/-- hasTrailingDigit2 at K+1 decomposes: trailing at K OR digit K = 2 -/
private lemma hasTrailingDigit2_succ (val K : Nat) (hK : K ≥ 1) :
    hasTrailingDigit2 val (K + 1) =
    (hasTrailingDigit2 val K || (val / 3 ^ K) % 3 == 2) := by
  unfold hasTrailingDigit2
  rw [show K + 1 = (K : Nat) + 1 from rfl, List.range_succ]
  simp [List.any_append, List.any]

private theorem list_any_eq_of_forall {α : Type} {l : List α} {p q : α → Bool}
    (h : ∀ x ∈ l, p x = q x) : l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.any_cons]
    rw [h a (List.mem_cons_self a l), ih (fun x hx => h x (List.mem_cons_of_mem a hx))]

/-- For K >= 1, r in N_K => exactly two of three lifts survive to N_{K+1}. -/
theorem exactly_two_lifts (K r : Nat) (hK : K ≥ 1) (hr : r < uK K)
    (htrail : hasTrailingDigit2 (2 ^ r % 3 ^ K) K = false) :
    let f := fun (j : Nat) => hasTrailingDigit2 (2 ^ (r + j * uK K) % 3 ^ (K + 1)) (K + 1)
    List.count false [f 0, f 1, f 2] = 2 := by
  intro f
  have h1 := mod3_eq_one_of_no_trail2 K r hK htrail
  have hAP := digits_arithmetic_progression K r hK hr
  have trail_same : ∀ j, hasTrailingDigit2 (2 ^ (r + j * uK K) % 3 ^ K) K = false := by
    intro j; rw [pow2_add_uK_mod K r j hK]; exact htrail
  have hsucc : ∀ val, hasTrailingDigit2 val (K + 1) =
      (hasTrailingDigit2 val K || (val / 3 ^ K) % 3 == 2) :=
    fun val => hasTrailingDigit2_succ val K hK
  have trail_ext : ∀ j, hasTrailingDigit2 (2 ^ (r + j * uK K) % 3 ^ (K + 1)) K = false := by
    intro j
    have h := trail_same j
    unfold hasTrailingDigit2 at h ⊢
    have congr_key : ∀ i ∈ List.range K,
        (((2 ^ (r + j * uK K) % 3 ^ (K + 1)) / 3 ^ i) % 3 == 2) =
        (((2 ^ (r + j * uK K) % 3 ^ K) / 3 ^ i) % 3 == 2) := by
      intro i hi
      rw [List.mem_range] at hi
      rw [← digit_eq_of_modPow (2 ^ (r + j * uK K)) i (K + 1) (by omega),
          ← digit_eq_of_modPow (2 ^ (r + j * uK K)) i K hi]
    rw [list_any_eq_of_forall congr_key]; exact h
  simp only [f, hsucc, trail_ext 0, trail_ext 1, trail_ext 2, Bool.false_or]
  have hd0 : (2 ^ (r + 0 * uK K) % 3 ^ (K + 1) / 3 ^ K) % 3 = kthDigit K r 0 := by
    unfold kthDigit ternaryDigit
    rw [show r + 0 * uK K = r from by ring]
    exact (digit_eq_of_modPow (2 ^ r) K (K + 1) (by omega)).symm
  have hd1 : (2 ^ (r + 1 * uK K) % 3 ^ (K + 1) / 3 ^ K) % 3 = kthDigit K r 1 := by
    unfold kthDigit ternaryDigit
    rw [show r + 1 * uK K = r + uK K from by ring]
    exact (digit_eq_of_modPow (2 ^ (r + uK K)) K (K + 1) (by omega)).symm
  have hd2 : (2 ^ (r + 2 * uK K) % 3 ^ (K + 1) / 3 ^ K) % 3 = kthDigit K r 2 := by
    unfold kthDigit ternaryDigit
    exact (digit_eq_of_modPow (2 ^ (r + 2 * uK K)) K (K + 1) (by omega)).symm
  rw [hd0, hd1, hd2, hAP.1, hAP.2, h1]
  have hd₀ : kthDigit K r 0 < 3 := by
    unfold kthDigit ternaryDigit; exact Nat.mod_lt _ (by norm_num : 3 > 0)
  interval_cases kthDigit K r 0 <;> simp [List.count] <;> omega

-- ============================================================
-- Phase 6: |N_K| = 2^{K-1} (no sorry)
-- ============================================================

/-- Bridge: Finset.range 3 filter card equals List.count false -/
private lemma finset_range3_filter_count (f : Nat → Bool) :
    ((Finset.range 3).filter fun q => !f q).card = List.count false [f 0, f 1, f 2] := by
  rw [Finset.card_filter, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero]
  cases f 0 <;> cases f 1 <;> cases f 2 <;> rfl

/-- N_K as a Finset -/
private def NKF (K : Nat) : Finset Nat :=
  (Finset.range (uK K)).filter fun r => !hasTrailingDigit2 (2 ^ r % 3 ^ K) K

/-- Base case: |N_1| = 1 = 2^0 -/
private lemma nkf_base : (NKF 1).card = 1 := by native_decide

/-- Trailing K digits are preserved when going from mod 3^K to mod 3^{K+1} -/
private lemma trail_ext_general (K s q : Nat) (hK : K ≥ 1) :
    hasTrailingDigit2 (2 ^ (q * uK K + s) % 3 ^ (K + 1)) K =
    hasTrailingDigit2 (2 ^ s % 3 ^ K) K := by
  unfold hasTrailingDigit2
  have congr_key : ∀ i ∈ List.range K,
      (((2 ^ (q * uK K + s) % 3 ^ (K + 1)) / 3 ^ i) % 3 == 2) =
      (((2 ^ (q * uK K + s) % 3 ^ K) / 3 ^ i) % 3 == 2) := by
    intro i hi
    rw [List.mem_range] at hi
    rw [← digit_eq_of_modPow (2 ^ (q * uK K + s)) i (K + 1) (by omega),
        ← digit_eq_of_modPow (2 ^ (q * uK K + s)) i K hi]
  rw [list_any_eq_of_forall congr_key, show q * uK K + s = s + q * uK K from by ring,
      pow2_add_uK_mod K s q hK]

/-- Filter predicate: hasTrailingDigit2 of the K+1 lift equals digit-2 test of kthDigit -/
private lemma filter_pred_eq_digit (K s q : Nat) (hK : K ≥ 1)
    (htrail : hasTrailingDigit2 (2 ^ s % 3 ^ K) K = false) :
    hasTrailingDigit2 (2 ^ (q * uK K + s) % 3 ^ (K + 1)) (K + 1) = (kthDigit K s q == 2) := by
  have hstep := hasTrailingDigit2_succ (2 ^ (q * uK K + s) % 3 ^ (K + 1)) K hK
  have hext := trail_ext_general K s q hK
  rw [hstep, hext, htrail, Bool.false_or]
  rw [show q * uK K + s = s + q * uK K from by ring]
  unfold kthDigit ternaryDigit
  exact congrArg (· == 2) (digit_eq_of_modPow (2 ^ (s + q * uK K)) K (K + 1) (by omega)).symm

/-- For K >= 1 and s < uK K, exactly 2 of {s, s+uK K, s+2*uK K} survive
    into N_{K+1} iff s is in N_K. -/
private lemma nkf_fiber (K s : Nat) (hK : K ≥ 1) (hs : s < uK K) :
    ((Finset.range 3).filter fun q =>
      !hasTrailingDigit2 (2 ^ (q * uK K + s) % 3 ^ (K + 1)) (K + 1)).card =
    if s ∈ NKF K then 2 else 0 := by
  have h_mem_iff : s ∈ NKF K ↔ hasTrailingDigit2 (2^s % 3^K) K = false := by
    constructor
    · intro h
      simp only [NKF, Finset.mem_filter, Finset.mem_range] at h
      revert h; cases hasTrailingDigit2 (2^s % 3^K) K <;> simp
    · intro h
      simp only [NKF, Finset.mem_filter, Finset.mem_range, hs, true_and]
      revert h; cases hasTrailingDigit2 (2^s % 3^K) K <;> simp
  split_ifs with h
  · -- s ∈ NKF K: exactly 2 survive
    have htrail := h_mem_iff.mp h
    have h_two := exactly_two_lifts K s hK hs htrail
    dsimp at h_two
    have hbridge := finset_range3_filter_count
      (fun q => hasTrailingDigit2 (2 ^ (q * uK K + s) % 3 ^ (K + 1)) (K + 1))
    rw [hbridge, show 0 * uK K + s = s + 0 * uK K from by omega,
        show 1 * uK K + s = s + 1 * uK K from by omega,
        show 2 * uK K + s = s + 2 * uK K from by omega]
    exact h_two
  · -- s ∉ NKF K: none survive
    have htrue : hasTrailingDigit2 (2^s % 3^K) K = true := by
      have := h_mem_iff.not.mp h
      revert this; cases hasTrailingDigit2 (2^s % 3^K) K <;> simp
    have h_all : ∀ q, hasTrailingDigit2 (2^(q * uK K + s) % 3^(K + 1)) (K + 1) = true := by
      intro q
      rw [hasTrailingDigit2_succ _ K hK, trail_ext_general K s q hK, htrue, Bool.true_or]
    have h_empty : (Finset.range 3).filter (fun q =>
      !hasTrailingDigit2 (2 ^ (q * uK K + s) % 3 ^ (K + 1)) (K + 1)) = ∅ := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_range, Finset.not_mem_empty, iff_false]
      intro ⟨_, hq⟩
      have := h_all q
      revert hq this; cases hasTrailingDigit2 (2 ^ (q * uK K + s) % 3 ^ (K + 1)) (K + 1) <;> simp
    rw [h_empty, Finset.card_empty]

/-- |N_{K+1}| = 2 * |N_K| for K >= 1 -/
private lemma nkf_inductive (K : Nat) (hK : K ≥ 1) :
    (NKF (K + 1)).card = 2 * (NKF K).card := by
  have huK : uK (K + 1) = 3 * uK K := by
    unfold uK
    have h1 : K + 1 - 1 = K := by omega
    have h2 : K - 1 + 1 = K := by omega
    rw [h1, show 3 ^ K = 3 ^ (K - 1) * 3 from by conv_lhs => rw [← h2, Nat.pow_succ]]
    omega
  have huK_pos : 0 < uK K := by
    unfold uK; exact Nat.mul_pos (by omega) (Nat.pow_pos (by omega))
  unfold NKF; rw [huK]
  rw [Finset.card_filter, Finset.card_filter, Finset.mul_sum]
  rw [show 3 * uK K = uK K + uK K + uK K from by omega,
      Finset.sum_range_add, Finset.sum_range_add]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s hs
  have hs' : s < uK K := Finset.mem_range.1 hs
  have hfiber := nkf_fiber K s hK hs'
  rw [Finset.card_filter] at hfiber
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, add_zero] at hfiber
  simp only [zero_add, one_mul, show 0 * uK K = 0 from by omega,
    show 1 * uK K = uK K from by omega, show 2 * uK K = uK K + uK K from by omega] at hfiber
  rw [hfiber]
  -- Goal: ite (s ∈ NKF K) 2 0 = 2 * (if !hasTrailingDigit2 (2^s % 3^K) K then 1 else 0)
  -- Rewrite s ∈ NKF K to its definition
  simp only [NKF, Finset.mem_filter, Finset.mem_range, hs', true_and]
  -- Now both sides depend on hasTrailingDigit2 (2^s % 3^K) K
  split <;> simp_all <;> omega

/-- |N_K| = 2^{K-1} for K >= 1. Main counting theorem for the tree. -/
theorem nk_size (K : Nat) (hK : K ≥ 1) :
    (NKF K).card = 2 ^ (K - 1) := by
  match K with
  | 0 => contradiction
  | 1 => exact nkf_base
  | K + 2 =>
    have hK1 : K + 1 ≥ 1 := by omega
    have ih := nk_size (K + 1) hK1
    have step := nkf_inductive (K + 1) hK1
    rw [step, ih, show K + 1 - 1 = K from by omega]
    show 2 * 2 ^ K = 2 ^ (K + 1)
    rw [show K + 1 = Nat.succ K from by omega]
    rw [Nat.pow_succ]
    exact (Nat.mul_comm (2 ^ K) 2).symm

-- ============================================================
-- {0,2,8} Characterization (no sorry)
-- ============================================================

private theorem ternaryDigit_zero_of_large (n K p : Nat) (hn : n < 3 ^ K) (hp : p ≥ K) :
    ternaryDigit n p ≠ 2 := by
  unfold ternaryDigit
  have hpow_le : 3 ^ K ≤ 3 ^ p := Nat.pow_le_pow_right (by omega : 0 < 3) hp
  have hlt : n < 3 ^ p := lt_of_lt_of_le hn hpow_le
  rw [Nat.div_eq_of_lt hlt]; norm_num

theorem two_pow_zero_no_digit2 : ∀ p, ternaryDigit (2 ^ 0) p ≠ 2 := by
  intro p; simp only [Nat.pow_zero]; unfold ternaryDigit
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · norm_num
  · exact ternaryDigit_zero_of_large 1 1 p (by norm_num) hp

theorem two_pow_two_no_digit2 : ∀ p, ternaryDigit (2 ^ 2) p ≠ 2 := by
  intro p; simp only [Nat.pow_two]; unfold ternaryDigit
  rcases Nat.lt_trichotomy p 2 with h | rfl | h
  · interval_cases p <;> norm_num
  · norm_num
  · exact ternaryDigit_zero_of_large 4 2 p (by norm_num) (Nat.le_of_lt h)

theorem two_pow_eight_no_digit2 : ∀ p, ternaryDigit (2 ^ 8) p ≠ 2 := by
  intro p; unfold ternaryDigit
  rcases Nat.lt_or_ge p 6 with hp | hp
  · interval_cases p <;> norm_num
  · exact ternaryDigit_zero_of_large 256 6 p (by norm_num) hp

end ErdosTernary.Lifting
