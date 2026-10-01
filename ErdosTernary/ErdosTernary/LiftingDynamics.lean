/-
  LiftingDynamics.lean — Generalized digit-position lemma for the Erdős conjecture.

  Core new results:
  1. digit_pos_of_lift: kthDigit K s q = q % 3 for s ∈ {0,2,8}, K ≥ 6
  2. cantor_quotient_restricted: q mod 3 ∈ {0,1} for Cantor exponents
  3. Helper lemmas for the lifting-dynamics proof strategy
-/
import Mathlib.Tactic
import ErdosTernary.BridgeCompute
import ErdosTernary.Narkiewicz
import ErdosTernary.Lifting
import ErdosTernary.CarryAnalysis
import ErdosTernary.ThreeLevelCompat

open ErdosTernary.BridgeCompute
open Narkiewicz
open ErdosTernary.Lifting
open ErdosTernary.CarryAnalysis
open ErdosTernary.ThreeLevelCompat

namespace ErdosTernary.LiftingDynamics

private lemma uK_pos' (K : Nat) : 0 < uK K := by
  unfold uK; exact Nat.mul_pos (by omega) (Nat.pow_pos (by omega))

private theorem cube_mod_helper' (r t m : Nat) (hm : m ≥ 1) :
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

private theorem cubic_lift' (a b m : Nat) (hm : m ≥ 1) (h : a % 3 ^ m = b % 3 ^ m) :
    a ^ 3 % 3 ^ (m + 1) = b ^ 3 % 3 ^ (m + 1) := by
  have ha : a = a % 3 ^ m + a / 3 ^ m * 3 ^ m := by rw [show a % 3 ^ m + a / 3 ^ m * 3 ^ m = 3 ^ m * (a / 3 ^ m) + a % 3 ^ m from by ring]; exact (Nat.div_add_mod a (3^m)).symm
  have hb : b = b % 3 ^ m + b / 3 ^ m * 3 ^ m := by rw [show b % 3 ^ m + b / 3 ^ m * 3 ^ m = 3 ^ m * (b / 3 ^ m) + b % 3 ^ m from by ring]; exact (Nat.div_add_mod b (3^m)).symm
  rw [ha, hb, h, cube_mod_helper' (b % 3 ^ m) (a / 3 ^ m) m hm, cube_mod_helper' (b % 3 ^ m) (b / 3 ^ m) m hm]

/-! ## Part 1: Generalized digit-position lemma -/

private lemma two_pow_s_lt_pow3 (s K : Nat)
    (hs : s = 0 ∨ s = 2 ∨ s = 8) (hK : K ≥ 6) :
    2 ^ s < 3 ^ K := by
  rcases hs with rfl | rfl | rfl
  · have : (1 : Nat) < 3 ^ K :=
      Nat.lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by omega) hK)
    omega
  · have : (4 : Nat) < 3 ^ K :=
      Nat.lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by omega) hK)
    omega
  · have : (256 : Nat) < 3 ^ K :=
      Nat.lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by omega) hK)
    omega

private lemma digit_sum_mod3' (s q : Nat) (hs : s = 0 ∨ s = 2 ∨ s = 8) :
    (q % 3 + 2 ^ s) % 3 = (q + 1) % 3 := by
  rcases hs with rfl | rfl | rfl <;> omega

/-- 2^uK K % 3^K = 1 for K ≥ 1. Derived from pow2_uK_mod. -/
private lemma pow2_uK_mod3K (K : Nat) (hK : K ≥ 1) :
    2 ^ uK K % 3 ^ K = 1 := by
  have h := pow2_uK_mod K hK
  have hdvd : 3 ^ K ∣ 3 ^ (K + 1) := Nat.pow_dvd_pow 3 (by omega)
  have h3K : 1 < 3 ^ K := by
    calc 1 < 3 ^ 1 := by norm_num
      _ ≤ 3 ^ K := Nat.pow_le_pow_right (by omega) hK
  have hrewrite : 2 ^ uK K % 3 ^ K =
      (2 ^ uK K % 3 ^ (K + 1)) % 3 ^ K :=
    (Nat.mod_mod_of_dvd (2 ^ uK K) hdvd) |>.symm
  rw [hrewrite, h, show 1 + 3 ^ K = 3 ^ K + 1 from by omega]
  rw [show (3 ^ K + 1 : Nat) = 3 ^ K + 1 * 1 from by ring]
  rw [show (3 ^ K + 1 * 1 : Nat) = 1 + 1 * 3 ^ K from by ring, Nat.add_mul_mod_self_right]
  exact Nat.mod_eq_of_lt h3K

/-- (2^uK K)^q % 3^K = 1 for K ≥ 1. -/
private lemma pow2_uK_q_mod3K (q K : Nat) (hK : K ≥ 1) :
    (2 ^ uK K) ^ q % 3 ^ K = 1 := by
  rw [Nat.pow_mod (2 ^ uK K) q (3 ^ K), pow2_uK_mod3K K hK, Nat.one_pow]
  have h3K : 1 < 3 ^ K := by
    calc 1 < 3 ^ 1 := by norm_num
      _ ≤ 3 ^ K := Nat.pow_le_pow_right (by omega) hK
  exact Nat.mod_eq_of_lt h3K

/-- 2^{s+q*uK K} % 3^K = 2^s when 2^s < 3^K. -/
private lemma pow_mod_pow3_base (s q K : Nat) (hK : K ≥ 1)
    (h2s : 2 ^ s < 3 ^ K) :
    2 ^ (s + q * uK K) % 3 ^ K = 2 ^ s := by
  rw [Nat.pow_add, Nat.mul_comm q, Nat.pow_mul]
  have hrep : (2 ^ uK K) ^ q =
      ((2 ^ uK K) ^ q / 3 ^ K) * 3 ^ K + 1 := by
    have h1 := Nat.div_add_mod ((2 ^ uK K) ^ q) (3 ^ K)
    rw [pow2_uK_q_mod3K q K hK, Nat.mul_comm (3 ^ K)] at h1
    exact h1.symm
  rw [hrep, Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc, Nat.add_comm,
    Nat.mul_comm _ (3 ^ K), Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt h2s

/-- n / 3^K % 3 = n % 3^(K+1) / 3^K -/
private lemma div_mod_eq_aux (n K : Nat) :
    n / 3 ^ K % 3 = n % 3 ^ (K + 1) / 3 ^ K := by
  have h1 := digit_eq_of_modPow n K (K + 1) (by omega)
  unfold ternaryDigit at h1
  have h3K1 : 3 ^ (K + 1) = 3 ^ K * 3 := Nat.pow_succ 3 K
  have h2 : n % 3 ^ (K + 1) / 3 ^ K < 3 := by
    have h3 : n % 3 ^ (K + 1) < 3 ^ (K + 1) :=
      @Nat.mod_lt n _ (Nat.pow_pos (by omega : 0 < 3))
    rw [h3K1, Nat.mul_comm (3 ^ K) 3] at h3 ⊢
    exact (Nat.div_lt_iff_lt_mul (Nat.pow_pos (by omega : 0 < 3))).mpr h3
  rw [Nat.mod_eq_of_lt h2] at h1
  exact h1

/-- The core identity: kthDigit K s q = q % 3
    for s ∈ {0,2,8} and K ≥ 6.
    This generalizes digit_pos18_of_lift (K=18) to all K ≥ 6. -/
theorem digit_pos_of_lift (s q K : Nat)
    (hs : s = 0 ∨ s = 2 ∨ s = 8) (hK : K ≥ 6) :
    kthDigit K s q = q % 3 := by
  have hKpos : K ≥ 1 := by omega
  have h2s := two_pow_s_lt_pow3 s K hs hK
  induction q generalizing s with
  | zero =>
    unfold kthDigit ternaryDigit
    simp only [show s + 0 * uK K = s from by omega]
    rw [(Nat.div_eq_zero_iff (Nat.pow_pos (by omega : 0 < 3))).mpr h2s]
  | succ q ih =>
    have h_ih := ih s hs h2s
    have h_eq : kthDigit K s (q + 1) = kthDigit K (s + q * uK K) 1 := by
      unfold kthDigit
      show ternaryDigit (2 ^ (s + (q + 1) * uK K)) K =
        ternaryDigit (2 ^ (s + q * uK K + 1 * uK K)) K
      congr 2; ring
    have hstep := kthDigit_step K (s + q * uK K) hKpos
    rw [h_eq, hstep]
    have h_quot : 2 ^ (s + q * uK K) % 3 ^ (K + 1) / 3 ^ K = q % 3 := by
      unfold kthDigit ternaryDigit at h_ih
      rw [div_mod_eq_aux (2 ^ (s + q * uK K)) K] at h_ih
      exact h_ih
    have h_rem := pow_mod_pow3_base s q K hKpos h2s
    rw [h_quot, h_rem]
    exact digit_sum_mod3' s q hs

/-! ## Part 2: Quotient restriction -/

/-- For Cantor 2^r with r = s + q*uK K, s ∈ {0,2,8}, K ≥ 6, s < uK K:
    q mod 3 ∈ {0,1}. -/
theorem cantor_quotient_restricted (r s q K : Nat)
    (hc : memCantorNat (2 ^ r))
    (hs : s = 0 ∨ s = 2 ∨ s = 8)
    (hK : K ≥ 6)
    (hs_lt : s < uK K)
    (hr : r = s + q * uK K) :
    q % 3 ≤ 1 := by
  have huK_pos : 0 < uK K := uK_pos' K
  have h_rmod : r % uK K = s := by
    rw [hr, show q * uK K = uK K * q from by ring, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt hs_lt
  have h_rdiv : r / uK K = q := by
    have hdiv : (s + q * uK K) / uK K = s / uK K + q :=
      Nat.add_mul_div_right s q huK_pos
    rw [hr, hdiv, (Nat.div_eq_zero_iff huK_pos).mpr hs_lt, zero_add]
  have h_cantor := digit2_free_digit_le_one r hc K
  have h_state := digit_from_state r K
  rw [h_rmod, h_rdiv] at h_state
  have h_digit := digit_pos_of_lift s q K hs hK
  omega

/-- The quotient digit is not 2. -/
theorem cantor_q_mod3_ne_two (r s q K : Nat)
    (hc : memCantorNat (2 ^ r))
    (hs : s = 0 ∨ s = 2 ∨ s = 8)
    (hK : K ≥ 6)
    (hs_lt : s < uK K)
    (hr : r = s + q * uK K) :
    q % 3 ≠ 2 := by
  have := cantor_quotient_restricted r s q K hc hs hK hs_lt hr
  omega

/-! ## Part 3: Recursive quotient descent -/

/-- The quotient satisfies q_{K+1} = q_K / 3. -/
theorem quotient_step (r K : Nat) (hK : K ≥ 1) :
    r / uK (K + 1) = r / uK K / 3 :=
  q_step r K hK

/-- The state decomposition. -/
theorem state_decomp (r K : Nat) :
    r = r % uK K + r / uK K * uK K := by
  rw [Nat.mul_comm (r / uK K) (uK K)]
  exact (Nat.mod_add_div r (uK K)).symm

/-- The quotient eventually reaches 0. -/
theorem quotient_eventually_zero (r : Nat) :
    ∃ K₀, ∀ K ≥ K₀, r / uK K = 0 :=
  qK_eventually_zero r

/-! ## Part 4: State transition and convergence

Key insight: if s_K ∈ {0,2,8} at level K, the quotient restriction
(q_K % 3 ∈ {0,1}) forces q_K % 3 = 0 (since q_K % 3 = 1 would push
the state s_{K+1} = s_K + uK K out of {0,2,8}).

Combined with q_K → 0, this means the state must converge to r ∈ {0,2,8}.
-/

/-- State step: s_{K+1} = s_K + (q_K % 3) * uK K.
    This is s_step from ThreeLevelCompat. -/
theorem state_step (r K : Nat) (hK : K ≥ 1) :
    r % uK (K + 1) = r % uK K + (r / uK K % 3) * uK K :=
  s_step r K hK

/-- If s_K ∈ {0,2,8} and q_K % 3 = 1, then s_{K+1} > 8
    (hence s_{K+1} ∉ {0,2,8}). -/
theorem state_pushes_beyond_exceptionals (s q K : Nat)
    (hs : s = 0 ∨ s = 2 ∨ s = 8) (hK : K ≥ 6) (_hq1 : q % 3 = 1) :
    s + uK K > 8 := by
  have huK : uK K ≥ 486 := by
    unfold uK
    have : K - 1 ≥ 5 := by omega
    calc 2 * 3 ^ (K - 1) ≥ 2 * 3 ^ 5 := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by omega) this)
      _ = 486 := by norm_num
  rcases hs with rfl | rfl | rfl <;> omega

/-- If s_K ∈ {0,2,8} and the state stays at s at the next level,
    then q_K % 3 = 0. -/
theorem quotient_must_be_zero_mod3 (r s q K : Nat)
    (_hc : memCantorNat (2 ^ r))
    (_hs : s = 0 ∨ s = 2 ∨ s = 8)
    (hK : K ≥ 6)
    (hs_lt : s < uK K)
    (hr : r = s + q * uK K)
    (h_s_next : r % uK (K + 1) = s) :
    q % 3 = 0 := by
  have hK1 : K ≥ 1 := by omega
  have huK_pos : 0 < uK K := uK_pos' K
  have h_rmod : r % uK K = s := by
    rw [hr, show q * uK K = uK K * q from by ring, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt hs_lt
  have h_rdiv : r / uK K = q := by
    have hdiv := Nat.add_mul_div_right s q huK_pos
    rw [hr, hdiv, (Nat.div_eq_zero_iff huK_pos).mpr hs_lt, zero_add]
  have h_step := s_step r K hK1
  rw [h_rmod, h_rdiv, h_s_next] at h_step
  have h_zero : (q % 3) * uK K = 0 := by omega
  have := Nat.mul_eq_zero.mp h_zero
  omega

/-- If q_K = 0 and s_K = r, then r = s_K. -/
theorem zero_quotient_gives_r (r K : Nat) (hq : r / uK K = 0) :
    r % uK K = r := by
  have huK_pos : 0 < uK K := uK_pos' K
  have hlt : r < uK K := by
    have := (Nat.div_eq_zero_iff huK_pos).mp hq
    omega
  rw [Nat.mod_eq_of_lt hlt]

/-! ## Part 5: Escape theorem — exceptional state forces digit 2

Key insight: when s ∈ {0,2,8} and K ≥ 6, the number 2^(s + uK K) has a digit 2
at a specific position. This is the escape mechanism: if the Cantor quotient
restriction ever forces q%3 = 1, the resulting state s + uK K is NOT Cantor.

The proof uses the identity 2^(uK K) mod 3^(K+2) = 1 + 7·3^K, proved by
induction using the same cubing trick as pow2_uK_mod.
-/

/-- (1 + 7·3^K)^3 mod 3^(K+3) = 1 + 7·3^(K+1) for K ≥ 2. -/
private lemma cubic_one_plus_seven (K : Nat) (hK : K ≥ 2) :
    (1 + 7 * 3 ^ K) ^ 3 % 3 ^ (K + 3) = 1 + 7 * 3 ^ (K + 1) := by
  have hlt : 1 + 7 * 3 ^ (K + 1) < 3 ^ (K + 3) := by
    have h1 : (1 : Nat) < 3 ^ (K + 1) := by
      have := Nat.pow_le_pow_right (by omega : 0 < 3) (by omega : 1 ≤ K + 1)
      nlinarith
    calc 1 + 7 * 3 ^ (K + 1) < 3 ^ (K + 1) + 7 * 3 ^ (K + 1) := by omega
      _ = 8 * 3 ^ (K + 1) := by ring
      _ ≤ 9 * 3 ^ (K + 1) := Nat.mul_le_mul_right _ (by omega : (8 : Nat) ≤ 9)
      _ = 3 ^ (K + 3) := by ring_nf
  have hfac :
      (1 + 7 * 3 ^ K) ^ 3 =
        1 + 7 * 3 ^ (K + 1) +
          3 ^ (K + 3) * (49 * 3 ^ (K - 2) + 343 * 3 ^ (2 * K - 3)) := by
    have h147 : 147 * 3 ^ (2 * K) = 3 ^ (K + 3) * (49 * 3 ^ (K - 2)) := by
      have : 147 * 3 ^ (2 * K) = 49 * 3 ^ (2 * K + 1) := by ring_nf
      rw [this, show 2 * K + 1 = (K + 3) + (K - 2) from by omega, Nat.pow_add]
      ring
    have h343 : 343 * 3 ^ (3 * K) = 3 ^ (K + 3) * (343 * 3 ^ (2 * K - 3)) := by
      have : 343 * 3 ^ (3 * K) = 343 * 3 ^ ((2 * K - 3) + (K + 3)) := by
        rw [show 3 * K = (2 * K - 3) + (K + 3) from by omega]
      rw [this, Nat.pow_add]; ring
    rw [show (1 + 7 * 3 ^ K) ^ 3 =
        1 + 21 * 3 ^ K + 147 * 3 ^ (2 * K) + 343 * 3 ^ (3 * K) from by ring,
      show 21 * 3 ^ K = 7 * 3 ^ (K + 1) from by ring_nf, h147, h343]
    ring
  show _ % _ = _
  rw [hfac, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

/-- (1 + 16·3^K)^3 mod 3^(K+4) = 1 + 16·3^(K+1) for K ≥ 4. -/
private lemma cubic_one_plus_16_mod3K4 (K : Nat) (_hK : K ≥ 4) :
    (1 + 16 * 3 ^ K) ^ 3 % 3 ^ (K + 4) = 1 + 16 * 3 ^ (K + 1) := by
  have hlt : 1 + 16 * 3 ^ (K + 1) < 3 ^ (K + 4) := by
    have h3k1 : 0 < 3 ^ (K + 1) := Nat.pow_pos (by decide : (0 : ℕ) < 3)
    have : (3 : Nat) ^ (K + 4) = 27 * 3 ^ (K + 1) := by ring_nf
    rw [this]; nlinarith
  have hfac :
      (1 + 16 * 3 ^ K) ^ 3 =
        1 + 16 * 3 ^ (K + 1) +
          3 ^ (K + 4) * (768 * 3 ^ (K - 4) + 4096 * 3 ^ (2 * K - 4)) := by
    have h768 : 768 * 3 ^ (2 * K) = 3 ^ (K + 4) * (768 * 3 ^ (K - 4)) := by
      have : 768 * 3 ^ (2 * K) = 768 * 3 ^ ((K - 4) + (K + 4)) := by
        rw [show 2 * K = (K - 4) + (K + 4) from by omega]
      rw [this, Nat.pow_add]; ring
    have h4096 : 4096 * 3 ^ (3 * K) = 3 ^ (K + 4) * (4096 * 3 ^ (2 * K - 4)) := by
      have : 4096 * 3 ^ (3 * K) = 4096 * 3 ^ ((2 * K - 4) + (K + 4)) := by
        rw [show 3 * K = (2 * K - 4) + (K + 4) from by omega]
      rw [this, Nat.pow_add]; ring
    rw [show (1 + 16 * 3 ^ K) ^ 3 =
        1 + 48 * 3 ^ K + 768 * 3 ^ (2 * K) + 4096 * 3 ^ (3 * K) from by ring,
      show 48 * 3 ^ K = 16 * 3 ^ (K + 1) from by ring_nf, h768, h4096]
    ring
  show _ % _ = _
  rw [hfac, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

/-- (1 + 16·3^K)^3 mod 3^(K+5) = 1 + 16·3^(K+1) for K ≥ 5. -/
private lemma cubic_one_plus_16_mod3K5 (K : Nat) (_hK : K ≥ 5) :
    (1 + 16 * 3 ^ K) ^ 3 % 3 ^ (K + 5) = 1 + 16 * 3 ^ (K + 1) := by
  have hlt : 1 + 16 * 3 ^ (K + 1) < 3 ^ (K + 5) := by
    have h3k1 : 0 < 3 ^ (K + 1) := Nat.pow_pos (by decide : (0 : ℕ) < 3)
    have : (3 : Nat) ^ (K + 5) = 81 * 3 ^ (K + 1) := by ring_nf
    rw [this]; nlinarith
  have hfac :
      (1 + 16 * 3 ^ K) ^ 3 =
        1 + 16 * 3 ^ (K + 1) +
          3 ^ (K + 5) * (768 * 3 ^ (K - 5) + 4096 * 3 ^ (2 * K - 5)) := by
    have h768 : 768 * 3 ^ (2 * K) = 3 ^ (K + 5) * (768 * 3 ^ (K - 5)) := by
      have : 768 * 3 ^ (2 * K) = 768 * 3 ^ ((K - 5) + (K + 5)) := by
        rw [show 2 * K = (K - 5) + (K + 5) from by omega]
      rw [this, Nat.pow_add]; ring
    have h4096 : 4096 * 3 ^ (3 * K) = 3 ^ (K + 5) * (4096 * 3 ^ (2 * K - 5)) := by
      have : 4096 * 3 ^ (3 * K) = 4096 * 3 ^ ((2 * K - 5) + (K + 5)) := by
        rw [show 3 * K = (2 * K - 5) + (K + 5) from by omega]
      rw [this, Nat.pow_add]; ring
    rw [show (1 + 16 * 3 ^ K) ^ 3 =
        1 + 48 * 3 ^ K + 768 * 3 ^ (2 * K) + 4096 * 3 ^ (3 * K) from by ring,
      show 48 * 3 ^ K = 16 * 3 ^ (K + 1) from by ring_nf, h768, h4096]
    ring
  show _ % _ = _
  rw [hfac, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

/-- (1 + 178·3^K)^3 mod 3^(K+6) = 1 + 178·3^(K+1) for K ≥ 6. -/
private lemma cubic_one_plus_178_mod3K6 (K : Nat) (_hK : K ≥ 6) :
    (1 + 178 * 3 ^ K) ^ 3 % 3 ^ (K + 6) = 1 + 178 * 3 ^ (K + 1) := by
  have hlt : 1 + 178 * 3 ^ (K + 1) < 3 ^ (K + 6) := by
    have h3k1 : 0 < 3 ^ (K + 1) := Nat.pow_pos (by decide : (0 : ℕ) < 3)
    have : (3 : Nat) ^ (K + 6) = 243 * 3 ^ (K + 1) := by ring_nf
    rw [this]; nlinarith
  have hfac :
      (1 + 178 * 3 ^ K) ^ 3 =
        1 + 178 * 3 ^ (K + 1) +
          3 ^ (K + 6) * (31684 * 3 ^ (K - 5) + 5639752 * 3 ^ (2 * K - 6)) := by
    have h95052 : 3 * 178 ^ 2 * 3 ^ (2 * K) = 3 ^ (K + 6) * (31684 * 3 ^ (K - 5)) := by
      have : 3 * 178 ^ 2 * 3 ^ (2 * K) = 31684 * 3 ^ (2 * K + 1) := by norm_num; ring
      rw [this, show 2 * K + 1 = (K - 5) + (K + 6) from by omega, Nat.pow_add]; ring
    have h5639752 : 178 ^ 3 * 3 ^ (3 * K) = 3 ^ (K + 6) * (5639752 * 3 ^ (2 * K - 6)) := by
      have : 178 ^ 3 * 3 ^ (3 * K) = 5639752 * 3 ^ (3 * K) := by norm_num; ring
      rw [this, show 3 * K = (2 * K - 6) + (K + 6) from by omega, Nat.pow_add]; ring
    rw [show (1 + 178 * 3 ^ K) ^ 3 =
        1 + 534 * 3 ^ K + 3 * 178 ^ 2 * 3 ^ (2 * K) + 178 ^ 3 * 3 ^ (3 * K) from by ring,
      show 534 * 3 ^ K = 178 * 3 ^ (K + 1) from by ring_nf, h95052, h5639752]
    ring
  show _ % _ = _
  rw [hfac, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

/-- 2^(uK K) mod 3^(K+2) = 1 + 7·3^K for K ≥ 6.
    Refinement of pow2_uK_mod: determines the digit at position K+1 = 2. -/
theorem pow2_uK_mod3K_plus2 (K : Nat) (hK : K ≥ 6) :
    2 ^ uK K % 3 ^ (K + 2) = 1 + 7 * 3 ^ K := by
  revert hK
  induction K using Nat.strongRecOn with
  | _ K ih =>
    intro hK
    match K with
    | 0 => omega
    | 1 => omega
    | 2 => omega
    | 3 => omega
    | 4 => omega
    | 5 => omega
    | 6 => norm_num [uK]
    | n + 7 =>
      have ih_val := ih (n + 6) (by omega) (by omega)
      have h_uK : uK (n + 7) = 3 * uK (n + 6) := by simp [uK]; ring_nf
      rw [h_uK, show 3 * uK (n + 6) = uK (n + 6) * 3 from by ring, Nat.pow_mul]
      have h_bmod : (1 + 7 * 3 ^ (n + 6)) % 3 ^ (n + 8) = 1 + 7 * 3 ^ (n + 6) := by
        apply Nat.mod_eq_of_lt
        have h3n : 0 < 3 ^ (n + 6) := Nat.pow_pos (by decide : (0 : ℕ) < 3)
        have h3eq : 3 ^ (n + 8) = 3 ^ (n + 6) * 9 := by ring_nf
        rw [h3eq]; nlinarith
      have ih_mod : 2 ^ uK (n + 6) % 3 ^ (n + 8) =
          (1 + 7 * 3 ^ (n + 6)) % 3 ^ (n + 8) := by
        rw [ih_val, h_bmod]
      have h_cubic := cubic_lift' (2 ^ uK (n + 6)) (1 + 7 * 3 ^ (n + 6))
        (n + 8) (by omega) ih_mod
      rw [h_cubic]
      exact cubic_one_plus_seven (n + 6) (by omega)

/-- The digit at position K+1 of 2^(uK K) is 2 (for s=0 case).
    From pow2_uK_mod3K_plus2: 2^(uK K) mod 3^(K+2) = 1 + 7·3^K.
    The digit at K+1 = (1 + 7·3^K) / 3^(K+1) % 3 = 2. -/
private lemma digit_K1_of_two_pow_uK (K : Nat) (hK : K ≥ 6) :
    (2 ^ uK K % 3 ^ (K + 2) / 3 ^ (K + 1)) % 3 = 2 := by
  rw [pow2_uK_mod3K_plus2 K hK]
  have h3pos : 0 < 3 ^ (K + 1) := Nat.pow_pos (by decide : (0 : ℕ) < 3)
  have hsmall : 3 ^ K + 1 < 3 ^ (K + 1) := by
    have h3eq : 3 ^ (K + 1) = 3 ^ K * 3 := by ring_nf
    rw [h3eq]
    have h3k : 0 < 3 ^ K := Nat.pow_pos (by decide : (0 : ℕ) < 3)
    nlinarith
  have hdecomp : (1 + 7 * 3 ^ K : ℕ) = 3 ^ (K + 1) * 2 + (3 ^ K + 1) := by ring
  rw [hdecomp, show 3 ^ (K + 1) * 2 + (3 ^ K + 1) = (3 ^ K + 1) + 3 ^ (K + 1) * 2 from by ring,
    show (3 : ℕ) ^ (K + 1) * 2 = 3 ^ (K + 1) + 3 ^ (K + 1) from by ring,
    ← Nat.add_assoc,
    Nat.add_div_right _ h3pos,
    Nat.add_div_right _ h3pos,
    Nat.div_eq_of_lt hsmall]

/-- 2^(uK K) mod 3^(K+3) = 1 + 16·3^K for K ≥ 6. -/
theorem pow2_uK_mod3K_plus3 (K : Nat) (hK : K ≥ 6) :
    2 ^ uK K % 3 ^ (K + 3) = 1 + 16 * 3 ^ K := by
  revert hK
  induction K using Nat.strongRecOn with
  | _ K ih =>
    intro hK
    match K with
    | 0 => omega
    | 1 => omega
    | 2 => omega
    | 3 => omega
    | 4 => omega
    | 5 => omega
    | 6 => norm_num [uK]
    | n + 7 =>
      have ih_val := ih (n + 6) (by omega) (by omega)
      have h_uK : uK (n + 7) = 3 * uK (n + 6) := by simp [uK]; ring_nf
      rw [h_uK, show 3 * uK (n + 6) = uK (n + 6) * 3 from by ring, Nat.pow_mul]
      have h_bmod : (1 + 16 * 3 ^ (n + 6)) % 3 ^ (n + 9) = 1 + 16 * 3 ^ (n + 6) := by
        apply Nat.mod_eq_of_lt
        have h3k6 : 0 < 3 ^ (n + 6) := Nat.pow_pos (by decide : (0 : ℕ) < 3)
        have : (3 : Nat) ^ (n + 9) = 27 * 3 ^ (n + 6) := by ring_nf
        rw [this]; nlinarith
      have ih_mod : 2 ^ uK (n + 6) % 3 ^ (n + 9) =
          (1 + 16 * 3 ^ (n + 6)) % 3 ^ (n + 9) := by
        rw [ih_val, h_bmod]
      have h_cubic := cubic_lift' (2 ^ uK (n + 6)) (1 + 16 * 3 ^ (n + 6))
        (n + 9) (by omega) ih_mod
      rw [h_cubic]
      exact cubic_one_plus_16_mod3K4 (n + 6) (by omega)

/-- 2^(uK K) mod 3^(K+4) = 1 + 16·3^K for K ≥ 6. -/
theorem pow2_uK_mod3K_plus4 (K : Nat) (hK : K ≥ 6) :
    2 ^ uK K % 3 ^ (K + 4) = 1 + 16 * 3 ^ K := by
  revert hK
  induction K using Nat.strongRecOn with
  | _ K ih =>
    intro hK
    match K with
    | 0 => omega
    | 1 => omega
    | 2 => omega
    | 3 => omega
    | 4 => omega
    | 5 => omega
    | 6 => norm_num [uK]
    | n + 7 =>
      have ih_val := ih (n + 6) (by omega) (by omega)
      have h_uK : uK (n + 7) = 3 * uK (n + 6) := by simp [uK]; ring_nf
      rw [h_uK, show 3 * uK (n + 6) = uK (n + 6) * 3 from by ring, Nat.pow_mul]
      have h_bmod : (1 + 16 * 3 ^ (n + 6)) % 3 ^ (n + 10) = 1 + 16 * 3 ^ (n + 6) := by
        apply Nat.mod_eq_of_lt
        have h3k6 : 0 < 3 ^ (n + 6) := Nat.pow_pos (by decide : (0 : ℕ) < 3)
        have : (3 : Nat) ^ (n + 10) = 81 * 3 ^ (n + 6) := by ring_nf
        rw [this]; nlinarith
      have ih_mod : 2 ^ uK (n + 6) % 3 ^ (n + 10) =
          (1 + 16 * 3 ^ (n + 6)) % 3 ^ (n + 10) := by
        rw [ih_val, h_bmod]
      have h_cubic := cubic_lift' (2 ^ uK (n + 6)) (1 + 16 * 3 ^ (n + 6))
        (n + 10) (by omega) ih_mod
      rw [h_cubic]
      exact cubic_one_plus_16_mod3K5 (n + 6) (by omega)

/-- 2^(uK K) mod 3^(K+5) = 1 + 178·3^K for K ≥ 6. -/
theorem pow2_uK_mod3K_plus5 (K : Nat) (hK : K ≥ 6) :
    2 ^ uK K % 3 ^ (K + 5) = 1 + 178 * 3 ^ K := by
  revert hK
  induction K using Nat.strongRecOn with
  | _ K ih =>
    intro hK
    match K with
    | 0 => omega
    | 1 => omega
    | 2 => omega
    | 3 => omega
    | 4 => omega
    | 5 => omega
    | 6 => norm_num [uK]
    | n + 7 =>
      have ih_val := ih (n + 6) (by omega) (by omega)
      have h_uK : uK (n + 7) = 3 * uK (n + 6) := by simp [uK]; ring_nf
      rw [h_uK, show 3 * uK (n + 6) = uK (n + 6) * 3 from by ring, Nat.pow_mul]
      have h_bmod : (1 + 178 * 3 ^ (n + 6)) % 3 ^ (n + 11) = 1 + 178 * 3 ^ (n + 6) := by
        apply Nat.mod_eq_of_lt
        have h3n6 : 0 < 3 ^ (n + 6) := Nat.pow_pos (by decide : (0 : ℕ) < 3)
        have : (3 : Nat) ^ (n + 11) = 243 * 3 ^ (n + 6) := by ring_nf
        rw [this]; nlinarith
      have ih_mod : 2 ^ uK (n + 6) % 3 ^ (n + 11) =
          (1 + 178 * 3 ^ (n + 6)) % 3 ^ (n + 11) := by
        rw [ih_val, h_bmod]
      have h_cubic := cubic_lift' (2 ^ uK (n + 6)) (1 + 178 * 3 ^ (n + 6))
        (n + 11) (by omega) ih_mod
      rw [h_cubic]
      exact cubic_one_plus_178_mod3K6 (n + 6) (by omega)

/-- Digit at position K+2 of 2^(8+uK K) is 2, via 256·2^(uK K) mod 3^(K+3). -/
private lemma digit_K2_of_256_pow_uK (K : Nat) (hK : K ≥ 6) :
    (256 * 2 ^ uK K % 3 ^ (K + 3) / 3 ^ (K + 2)) % 3 = 2 := by
  have h3k6 : 3 ^ 6 ≤ 3 ^ K := Nat.pow_le_pow_right (by omega) hK
  have h256mod : 256 % 3 ^ (K + 3) = 256 := by
    apply Nat.mod_eq_of_lt
    rw [show 3 ^ (K + 3) = 27 * 3 ^ K from by ring_nf]
    nlinarith [show (3 : ℕ) ^ 6 = 729 from by norm_num]
  have hfac : 256 * (1 + 16 * 3 ^ K) =
      256 + 3 ^ K + 2 * 3 ^ (K + 2) + 151 * 3 ^ (K + 3) := by ring
  have hstep : 256 * 2 ^ uK K % 3 ^ (K + 3) = 256 + 3 ^ K + 2 * 3 ^ (K + 2) := by
    have hmul_mod : 256 * 2 ^ uK K % 3 ^ (K + 3) =
      (256 % 3 ^ (K + 3) * (2 ^ uK K % 3 ^ (K + 3))) % 3 ^ (K + 3) := by rw [Nat.mul_mod]
    have hmod_add :
        ((256 + 3 ^ K + 2 * 3 ^ (K + 2)) + 151 * 3 ^ (K + 3)) % 3 ^ (K + 3) =
        (256 + 3 ^ K + 2 * 3 ^ (K + 2)) % 3 ^ (K + 3) := by
      rw [show 151 * 3 ^ (K + 3) = 3 ^ (K + 3) * 151 from by ring,
        Nat.add_mul_mod_self_left]
    calc 256 * 2 ^ uK K % 3 ^ (K + 3)
        = (256 % 3 ^ (K + 3) * (2 ^ uK K % 3 ^ (K + 3))) % 3 ^ (K + 3) := hmul_mod
    _ = (256 * (2 ^ uK K % 3 ^ (K + 3))) % 3 ^ (K + 3) := by rw [h256mod]
    _ = (256 * (1 + 16 * 3 ^ K)) % 3 ^ (K + 3) := by rw [pow2_uK_mod3K_plus3 K hK]
    _ = ((256 + 3 ^ K + 2 * 3 ^ (K + 2)) + 151 * 3 ^ (K + 3)) % 3 ^ (K + 3) := by rw [hfac]
    _ = (256 + 3 ^ K + 2 * 3 ^ (K + 2)) % 3 ^ (K + 3) := hmod_add
    _ = 256 + 3 ^ K + 2 * 3 ^ (K + 2) := by
      apply Nat.mod_eq_of_lt
      rw [show 3 ^ (K + 3) = 27 * 3 ^ K from by ring_nf,
        show 3 ^ (K + 2) = 9 * 3 ^ K from by ring_nf]
      nlinarith [show (3 : ℕ) ^ 6 = 729 from by norm_num]
  rw [hstep]
  have h3pos : 0 < 3 ^ (K + 2) := Nat.pow_pos (by omega)
  have hsmall : 3 ^ K + 256 < 3 ^ (K + 2) := by
    rw [show 3 ^ (K + 2) = 9 * 3 ^ K from by ring_nf]
    nlinarith [show (3 : ℕ) ^ 6 = 729 from by norm_num]
  have hdecomp : (256 + 3 ^ K + 2 * 3 ^ (K + 2) : ℕ) =
      3 ^ (K + 2) * 2 + (3 ^ K + 256) := by ring
  rw [hdecomp, show 3 ^ (K + 2) * 2 + (3 ^ K + 256) =
      (3 ^ K + 256) + 3 ^ (K + 2) * 2 from by ring,
    show (3 : ℕ) ^ (K + 2) * 2 = 3 ^ (K + 2) + 3 ^ (K + 2) from by ring,
    ← Nat.add_assoc,
    Nat.add_div_right _ h3pos,
    Nat.add_div_right _ h3pos,
    Nat.div_eq_of_lt hsmall]

private lemma digit_K3_of_4_pow_uK (K : Nat) (hK : K ≥ 6) :
    (4 * 2 ^ uK K % 3 ^ (K + 4) / 3 ^ (K + 3)) % 3 = 2 := by
  have h3k6 : 3 ^ 6 ≤ 3 ^ K := Nat.pow_le_pow_right (by omega) hK
  have h4mod : 4 % 3 ^ (K + 4) = 4 := by
    apply Nat.mod_eq_of_lt
    rw [show 3 ^ (K + 4) = 81 * 3 ^ K from by ring_nf]
    nlinarith [show (3 : ℕ) ^ 6 = 729 from by norm_num]
  have hfac : 4 * (1 + 16 * 3 ^ K) =
      4 + 3 ^ K + 3 ^ (K + 2) + 2 * 3 ^ (K + 3) := by ring
  have hstep : 4 * 2 ^ uK K % 3 ^ (K + 4) =
      4 + 3 ^ K + 3 ^ (K + 2) + 2 * 3 ^ (K + 3) := by
    have hmul_mod : 4 * 2 ^ uK K % 3 ^ (K + 4) =
      (4 % 3 ^ (K + 4) * (2 ^ uK K % 3 ^ (K + 4))) % 3 ^ (K + 4) := by rw [Nat.mul_mod]
    calc 4 * 2 ^ uK K % 3 ^ (K + 4)
        = (4 % 3 ^ (K + 4) * (2 ^ uK K % 3 ^ (K + 4))) % 3 ^ (K + 4) := hmul_mod
    _ = (4 * (2 ^ uK K % 3 ^ (K + 4))) % 3 ^ (K + 4) := by rw [h4mod]
    _ = (4 * (1 + 16 * 3 ^ K)) % 3 ^ (K + 4) := by rw [pow2_uK_mod3K_plus4 K hK]
    _ = (4 + 3 ^ K + 3 ^ (K + 2) + 2 * 3 ^ (K + 3)) % 3 ^ (K + 4) := by rw [hfac]
    _ = 4 + 3 ^ K + 3 ^ (K + 2) + 2 * 3 ^ (K + 3) := by
      apply Nat.mod_eq_of_lt
      rw [show 3 ^ (K + 4) = 81 * 3 ^ K from by ring_nf]
      nlinarith [show (3 : ℕ) ^ 6 = 729 from by norm_num]
  rw [hstep]
  have h3pos : 0 < 3 ^ (K + 3) := Nat.pow_pos (by omega)
  have hsmall : 3 ^ K + 3 ^ (K + 2) + 4 < 3 ^ (K + 3) := by
    rw [show 3 ^ (K + 3) = 27 * 3 ^ K from by ring_nf,
      show 3 ^ (K + 2) = 9 * 3 ^ K from by ring_nf]
    nlinarith [show (3 : ℕ) ^ 6 = 729 from by norm_num]
  have hdecomp : (4 + 3 ^ K + 3 ^ (K + 2) + 2 * 3 ^ (K + 3) : ℕ) =
      3 ^ (K + 3) * 2 + (3 ^ K + 3 ^ (K + 2) + 4) := by ring
  rw [hdecomp, show 3 ^ (K + 3) * 2 + (3 ^ K + 3 ^ (K + 2) + 4) =
      (3 ^ K + 3 ^ (K + 2) + 4) + 3 ^ (K + 3) * 2 from by ring,
    show (3 : ℕ) ^ (K + 3) * 2 = 3 ^ (K + 3) + 3 ^ (K + 3) from by ring,
    ← Nat.add_assoc,
    Nat.add_div_right _ h3pos,
    Nat.add_div_right _ h3pos,
    Nat.div_eq_of_lt hsmall]

/-- Escape for s=0: the digit at position K+1 of 2^(uK K) is 2,
    so 2^(uK K) has a digit 2 and is not Cantor. -/
theorem escape_s0 (K : Nat) (hK : K ≥ 6) :
    ternaryDigit (2 ^ uK K) (K + 1) = 2 := by
  unfold ternaryDigit
  rw [digit_eq_of_modPow (2 ^ uK K) (K + 1) (K + 2) (by omega)]
  exact digit_K1_of_two_pow_uK K hK

/-- Escape for s=2: 2^(2 + uK K) has a digit 2 at position K+3. -/
theorem escape_s2 (K : Nat) (hK : K ≥ 6) :
    ∃ j, ternaryDigit (2 ^ (2 + uK K)) j = 2 := by
  refine ⟨K + 3, ?_⟩
  unfold ternaryDigit
  rw [digit_eq_of_modPow (2 ^ (2 + uK K)) (K + 3) (K + 4) (by omega)]
  show (2 ^ (2 + uK K) % 3 ^ (K + 4) / 3 ^ (K + 3)) % 3 = 2
  rw [show 2 ^ (2 + uK K) = 4 * 2 ^ uK K from by ring]
  exact digit_K3_of_4_pow_uK K hK

/-- Escape for s=8: 2^(8 + uK K) has a digit 2 at position K+2. -/
theorem escape_s8 (K : Nat) (hK : K ≥ 6) :
    ∃ j, ternaryDigit (2 ^ (8 + uK K)) j = 2 := by
  refine ⟨K + 2, ?_⟩
  unfold ternaryDigit
  rw [digit_eq_of_modPow (2 ^ (8 + uK K)) (K + 2) (K + 3) (by omega)]
  show (2 ^ (8 + uK K) % 3 ^ (K + 3) / 3 ^ (K + 2)) % 3 = 2
  rw [show 2 ^ (8 + uK K) = 256 * 2 ^ uK K from by ring]
  exact digit_K2_of_256_pow_uK K hK

/-- Main escape theorem: for s ∈ {0,2,8} and K ≥ 6,
    2^(s + uK K) has a digit 2, hence is NOT Cantor. -/
theorem exceptional_escape (s K : Nat)
    (hs : s = 0 ∨ s = 2 ∨ s = 8) (hK : K ≥ 6) :
    ∃ j, ternaryDigit (2 ^ (s + uK K)) j = 2 := by
  rcases hs with rfl | rfl | rfl
  · show ∃ j, ternaryDigit (2 ^ (0 + uK K)) j = 2
    simp only [zero_add]
    exact ⟨K + 1, escape_s0 K hK⟩
  · exact escape_s2 K hK
  · exact escape_s8 K hK

/-! ## Part 6: The descent lemma —

    If s ∈ {0,2,8}, K ≥ 6, s < uK K, and memCantorNat(2^(s + q·uK K)),
    then q = 0.  The proof is strong induction on q:
    • q%3 = 2 is ruled out by cantor_q_mod3_ne_two.
    • q%3 = 1 forces the state beyond the exceptionals (state_pushes_beyond_exceptionals),
      and the digit at position K of 2^r is 1; by the escape theorems applied at the
      appropriate higher level, a digit 2 must appear.  (This is the hard case.)
    • q%3 = 0 gives q = 3q', and r = s + q'·uK(K+1), so we recurse. -/

/-- The key descent: Cantor + exceptional state ⟹ quotient is zero.
    The q%3=1 case is the structural core — the state leaves {0,2,8} and the
    escape mechanism produces a digit-2 obstruction. -/
theorem cantor_exceptional_forces_zero (s q K : Nat)
    (hs : s = 0 ∨ s = 2 ∨ s = 8)
    (hK : K ≥ 6)
    (hs_lt : s < uK K)
    (hc : memCantorNat (2 ^ (s + q * uK K))) :
    q = 0 := by
  by_contra hq
  have hq_pos : q > 0 := by omega
  induction q using Nat.strongRecOn generalizing K with
  | _ q ih =>
    -- q%3 cannot be 2 (Cantor forces quotient digit ≤ 1)
    have hq3 := cantor_quotient_restricted _ s q K hc hs hK hs_lt rfl
    have hq3_cases : q % 3 = 0 ∨ q % 3 = 1 := by omega
    rcases hq3_cases with h0 | h1
    · -- q%3 = 0: q = 3q', recurse to level K+1
      have h3q : 3 ∣ q := by omega
      obtain ⟨q', hq'_eq⟩ := h3q
      have hq'_lt : q' < q := by omega
      have hq_eq : q = 3 * q' := hq'_eq
      -- r = s + 3q'·uK K = s + q'·uK(K+1)
      have huK_succ : uK (K + 1) = 3 * uK K := by
        have hK1 : K ≥ 1 := by omega
        unfold uK
        have h1 : K + 1 - 1 = K := by omega
        have hpow : (3 : Nat) ^ K = 3 ^ (K - 1) * 3 := by
          conv_lhs => rw [show K = (K - 1) + 1 from by omega, Nat.pow_succ]
        rw [h1, hpow]; ring
      have hr_eq : s + q * uK K = s + q' * uK (K + 1) := by
        rw [hq_eq, huK_succ]; ring
      rw [hr_eq] at hc
      have hK1 : K + 1 ≥ 6 := by omega
      have hs_lt1 : s < uK (K + 1) := by
        rw [huK_succ]; omega
      have hq'_ne : q' ≠ 0 := by
        by_contra h; subst h; omega
      have hq'_pos : q' > 0 := by omega
      exact ih q' hq'_lt (K + 1) hK1 hs_lt1 hc hq'_ne hq'_pos
    · -- q%3 = 1: two sub-cases
      by_cases hq1 : q = 1
      · -- q = 1: r = s + uK K. exceptional_escape gives digit 2.
        -- 2^(s + uK K) has a digit 2 at position K+1 (s=0), K+2 (s=8), or K+3 (s=2).
        -- Hence 2^r is not Cantor, contradicting hc.
        have hr_eq : s + q * uK K = s + uK K := by rw [hq1]; ring
        rw [hr_eq] at hc
        obtain ⟨j, hj⟩ := exceptional_escape s K hs hK
        exact absurd hc (memCantorNat_def.mp · j hj)
      · -- q > 1, q%3 = 1: q = 3q' + 1 with q' ≥ 1.
        -- BLOCKER: This case requires showing 2^(s+q·uK K) has digit 2
        -- when q>1 and q%3=1. The state at level K+1 is s₁=s+uK K > 8,
        -- which is not exceptional, so we cannot reapply the IH.
        --
        -- The digit at position K+1 is (2+q')%3 (for s=0, from the
        -- binomial expansion of (1+7·3^K)^q mod 3^(K+2)). This is 2
        -- when q'≡0(mod 3), i.e., q≡1(mod 9). For other q values,
        -- the digit-2 appears at a position that depends on the ternary
        -- structure of q, but the carry analysis for general q>1 remains
        -- unformalized.
        --
        -- NOTE: The existing q%3=0 branch handles descent through trailing
        -- zeros. Combined with the q=1 sub-case above, this covers all
        -- q whose ternary representation ends in exactly one nonzero digit.
        -- The q>1 sub-case covers numbers with more complex ternary structure.
        have hs_next := state_pushes_beyond_exceptionals s q K hs hK h1
        sorry

end ErdosTernary.LiftingDynamics
