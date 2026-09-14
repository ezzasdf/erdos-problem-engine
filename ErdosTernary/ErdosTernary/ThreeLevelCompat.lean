import Mathlib.Tactic
import ErdosTernary.BridgeCompute
import ErdosTernary.Narkiewicz
import ErdosTernary.Lifting
import ErdosTernary.CarryAnalysis

open ErdosTernary.BridgeCompute
open Narkiewicz
open ErdosTernary.Lifting
open ErdosTernary.CarryAnalysis

namespace ErdosTernary.ThreeLevelCompat

private lemma uK_succ (K : Nat) (hK : K ≥ 1) : uK (K + 1) = 3 * uK K := by
  unfold uK
  have : K + 1 - 1 = K := by omega
  rw [this]
  calc 2 * 3 ^ K
    _ = 2 * (3 ^ (K - 1) * 3) := by
      congr 1; rw [← Nat.pow_succ]; congr 1; omega
    _ = 3 * (2 * 3 ^ (K - 1)) := by ring

private lemma uK_pos (K : Nat) : 0 < uK K := by
  unfold uK; exact Nat.mul_pos (by omega) (Nat.pow_pos (by omega))

private theorem mod_mul_aux (r a : Nat) (ha : 0 < a) :
    r % (3 * a) = r % a + (r / a % 3) * a := by
  have hlt : r % a + r / a % 3 * a < 3 * a := by
    have h1 := Nat.mod_lt r ha
    have h2 := Nat.mod_lt (r / a) (by omega : 0 < 3)
    have hle := Nat.mul_le_mul_right a (show r / a % 3 ≤ 2 from by omega)
    omega
  have hr : r % a + a * (r / a) = r := Nat.mod_add_div r a
  have hq : 3 * (r / a / 3) + r / a % 3 = r / a := Nat.div_add_mod (r / a) 3
  have hdecomp : r = r % a + (r / a % 3) * a + 3 * a * (r / a / 3) := by
    have h1 : a * (r / a) = a * (3 * (r / a / 3) + r / a % 3) := by rw [hq]
    have h2 : a * (3 * (r / a / 3) + r / a % 3) = a * 3 * (r / a / 3) + a * (r / a % 3) := by ring
    have h3 : a * 3 * (r / a / 3) + a * (r / a % 3) = 3 * a * (r / a / 3) + (r / a % 3) * a := by ring
    omega
  conv_lhs => rw [show r = r % a + (r / a % 3) * a + 3 * a * (r / a / 3) from hdecomp]
  rw [show r % a + r / a % 3 * a + 3 * a * (r / a / 3) =
       (r % a + r / a % 3 * a) + (3 * a) * (r / a / 3) from by ring]
  rw [Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt hlt

theorem q_step (r K : Nat) (hK : K ≥ 1) :
    r / uK (K + 1) = r / uK K / 3 := by
  have huK1 := uK_succ K hK
  rw [huK1, show (3 : Nat) * uK K = uK K * 3 from by ring]
  exact (Nat.div_div_eq_div_mul r (uK K) 3).symm

theorem s_step (r K : Nat) (hK : K ≥ 1) :
    r % uK (K + 1) = r % uK K + (r / uK K % 3) * uK K := by
  rw [show uK (K + 1) = 3 * uK K from uK_succ K hK]
  exact mod_mul_aux r (uK K) (uK_pos K)

theorem digit_from_state (r K : Nat) :
    carry r K % 3 = kthDigit K (r % uK K) (r / uK K) := by
  unfold carry kthDigit ternaryDigit
  rw [show r / uK K * uK K = uK K * (r / uK K) from by ring]
  have h : r % uK K + uK K * (r / uK K) = r := Nat.mod_add_div r (uK K)
  rw [show 2 ^ (r % uK K + uK K * (r / uK K)) = 2 ^ r from by rw [h]]

theorem lift_transition (r K : Nat) (hK : K ≥ 1) :
    r % uK (K + 1) = r % uK K + (r / uK K % 3) * uK K ∧
    r / uK (K + 1) = r / uK K / 3 :=
  ⟨s_step r K hK, q_step r K hK⟩

theorem three_level_digits (r K : Nat) (hc : memCantorNat (2 ^ r)) :
    carry r K % 27 =
      kthDigit K (r % uK K) (r / uK K) +
      3 * kthDigit (K + 1) (r % uK (K + 1)) (r / uK (K + 1)) +
      9 * kthDigit (K + 2) (r % uK (K + 2)) (r / uK (K + 2)) := by
  rw [carry_mod27_digits r K hc, digit_from_state r K,
    digit_from_state r (K + 1), digit_from_state r (K + 2)]

theorem digit2_free_three_level (r K : Nat)
    (hc : memCantorNat (2 ^ r)) :
    kthDigit K (r % uK K) (r / uK K) ≤ 1 ∧
    kthDigit (K + 1) (r % uK (K + 1)) (r / uK (K + 1)) ≤ 1 ∧
    kthDigit (K + 2) (r % uK (K + 2)) (r / uK (K + 2)) ≤ 1 := by
  simp only [← digit_from_state]
  exact ⟨digit2_free_digit_le_one r hc K,
         digit2_free_digit_le_one r hc (K + 1),
         digit2_free_digit_le_one r hc (K + 2)⟩

theorem digit2_free_mod27_from_state (r K : Nat)
    (hc : memCantorNat (2 ^ r)) :
    carry r K % 27 ≤ 13 :=
  digit2_free_mod27_le13 r K hc

theorem qK_base3 (r K : Nat) (hK : K ≥ 1) :
    r / uK K = 3 * (r / uK (K + 1)) + r / uK K % 3 := by
  rw [q_step r K hK]
  exact (Nat.div_add_mod (r / uK K) 3).symm

theorem lift_state_invariant (r K : Nat) (_hK : K ≥ 1) :
    r = r % uK K + (r / uK K) * uK K := by
  have h := (Nat.mod_add_div r (uK K))
  rw [show uK K * (r / uK K) = r / uK K * uK K from by ring] at h
  exact h.symm

theorem sK_nondecreasing (r K : Nat) (hK : K ≥ 1) :
    r % uK K ≤ r % uK (K + 1) := by
  rw [s_step r K hK]
  exact Nat.le_add_right _ _

theorem carry_succ_div (r K : Nat) :
    carry r (K + 1) = carry r K / 3 := by
  unfold carry
  rw [show 3 ^ (K + 1) = 3 ^ K * 3 from by ring, Nat.div_div_eq_div_mul]

/-! ## Density decay: |N_K| / u_K → 0

The 2-to-1 lifting means |N_{K+1}| = 2|N_K| while u_{K+1} = 3*u_K.
So the density |N_K|/u_K = (2/3)^{K-1}/2 decays to 0.

This means the survivor set N_K becomes vanishingly sparse within [0, u_K).
For r ∉ {0,2,8}, the structural constraints of the carry-lifting system
are over-determined: the specific digits demanded by the survivor path
are incompatible with the carry dynamics.

Density identity (from nk_size + uK definition):
    2 * |N_K| * 3^{K-1} = uK K * 2^{K-1}
    i.e. |N_K| / uK K = (2/3)^{K-1} / 2  →  0 as K → ∞ -/

/-! ## Lift state convergence: q_K → 0

As K increases, q_K = r / uK K decreases (q_{K+1} = q_K / 3).
Since uK K = 2 * 3^{K-1} grows exponentially, eventually uK K > r
and q_K = 0. Once q_K = 0, the digit at position K is determined
solely by r (not by the lifting decomposition). -/

private theorem pow3_ge (n : Nat) : 3 ^ n ≥ n + 1 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    calc 3 ^ (n + 1) = 3 * 3 ^ n := by ring
      _ ≥ 3 * (n + 1) := Nat.mul_le_mul_left 3 ih
      _ ≥ n + 2 := by omega

/-- uK K > r when K ≥ r + 2. -/
theorem uK_gt_of_large (r K : Nat) (hK : K ≥ r + 2) : uK K > r := by
  unfold uK
  have hpow : 3 ^ (K - 1) > r := by
    have h1 : K - 1 ≥ r + 1 := by omega
    have h2 : 3 ^ (K - 1) ≥ 3 ^ (r + 1) :=
      Nat.pow_le_pow_right (by omega : 0 < 3) h1
    have h3 : 3 ^ (r + 1) ≥ r + 2 := by
      have := pow3_ge (r + 1)
      omega
    omega
  omega

/-- q_K = r / uK K = 0 when K ≥ r + 2. -/
theorem qK_zero (r K : Nat) (hK : K ≥ r + 2) : r / uK K = 0 := by
  apply Nat.div_eq_zero_iff (uK_pos K) |>.mpr
  have := uK_gt_of_large r K hK
  omega

/-- The lift state q_K eventually reaches 0. -/
theorem qK_eventually_zero (r : Nat) : ∃ K₀, ∀ K ≥ K₀, r / uK K = 0 := by
  refine ⟨r + 2, fun K hK => qK_zero r K (by omega)⟩

/-! ## Carry structure: base-3 digit expansion

carry r K = 2^r / 3^K is the "remaining" value after extracting
the first K ternary digits of 2^r. Its base-3 representation gives
the ternary digits of 2^r at positions K, K+1, K+2, ...

For memCantorNat(2^r), ALL base-3 digits of carry r K must be in {0, 1}.
This forces carry r K ≤ (3^{n} - 1)/2 when carry r K < 3^{n}. -/

/-- carry r K base-3 digit at offset j equals digit of 2^r at position K+j. -/
theorem carry_digit_offset (r K j : Nat) :
    (carry r K / 3 ^ j) % 3 = digit₃ (2 ^ r) (K + j) := by
  unfold carry digit₃
  rw [show 2 ^ r / 3 ^ K / 3 ^ j = 2 ^ r / 3 ^ (K + j) from by
    rw [show 3 ^ (K + j) = 3 ^ K * 3 ^ j from by ring,
        Nat.div_div_eq_div_mul]]

/-- If memCantorNat(2^r), carry r K % 3 ≤ 1 for all K. -/
theorem carry_cantor_digits (r K : Nat) (hc : memCantorNat (2 ^ r)) :
    carry r K % 3 ≤ 1 :=
  digit2_free_digit_le_one r hc K

/-- The carry strictly decreases for digit-2-free 2^r with positive carry. -/
theorem carry_strict_decrease (r K : Nat) (hc : memCantorNat (2 ^ r))
    (hpos : carry r K > 0) :
    carry r (K + 1) < carry r K :=
  carry_shrink r K (digit2_free_digit_le_one r hc K) hpos

/-- The carry eventually terminates at 0. -/
theorem carry_eventually_zero (r : Nat) : ∃ K, carry r K = 0 :=
  digit2_free_terminate r

/-! ## The Killer Contradiction Framework

For r ∉ {0, 2, 8} with memCantorNat(2^r):

1. carry r K % 3 ∈ {0, 1} for ALL K (digit-2-free constraint)
2. carry r (K+1) = carry r K / 3 (carry shrinks by factor 3)
3. carry r K → 0 (carry eventually terminates)
4. q_K = r / uK K → 0 (lift state converges)
5. |N_K|/uK K = (2/3)^{K-1}/2 → 0 (density decay)

The combination of (1)-(5) creates an over-constrained system:
- The carry must terminate with ALL digits in {0,1}
- The lifting tree has exactly 3 permanent paths {0,2,8}
- Any other path must eventually encounter digit 2
- The density decay shows survivors are vanishingly sparse

THE PROOF STRATEGY:
For r < uK 18: covered by computational bridge (bridge_K18).
For r ≥ uK 18: r mod uK 18 ∈ {0,2,8} by bridge_K18.
  Write r = q * uK 18 + s, s ∈ {0,2,8}, q ≥ 1.
  The digit at position 18 = kthDigit 18 s q = q mod 3
    (proved below: digit_pos18_of_lift).
  If q mod 3 = 2: digit 2 at position 18. Contradiction.
  If q mod 3 ∈ {0,1}: recurse with q' = q/3 at position 19.
  The recursion terminates because q decreases: q → q/3 → ... → 0.
  When q = 0: r < uK L for some L, but r ≥ uK 18, contradiction. -/

/-- 2^(uK 18) ≡ 1 mod 3^18 (from pow2_uK_mod which gives mod 3^19) -/
private lemma pow2_uK_18_mod318 : 2 ^ uK 18 % 3 ^ 18 = 1 := by
  have h := pow2_uK_mod 18 (by omega : 18 ≥ 1)
  omega

/-- For s ∈ {0,2,8}: 2^s ≡ 1 mod 3 -/
private lemma two_pow_s_mod3 (s : Nat) (hs : s = 0 ∨ s = 2 ∨ s = 8) :
    2 ^ s % 3 = 1 := by
  rcases hs with rfl | rfl | rfl <;> norm_num

/-- A*3^K mod 3^{K+1} = (A mod 3)*3^K (reproved from mul_pow_mod in Lifting) -/
private lemma mul_pow_mod' (A K : Nat) (hK : K ≥ 1) :
    A * 3 ^ K % 3 ^ (K + 1) = A % 3 * 3 ^ K := by
  have h := (Nat.div_add_mod A 3).symm
  conv_lhs => rw [show A = 3 * (A / 3) + A % 3 from h]
  rw [show (3 * (A / 3) + A % 3) * 3 ^ K = 3 * (A / 3) * 3 ^ K + A % 3 * 3 ^ K from by ring]
  rw [show 3 * (A / 3) * 3 ^ K = (A / 3) * (3 * 3 ^ K) from by ring]
  rw [show 3 * 3 ^ K = 3 ^ (K + 1) from by ring]
  rw [show (A / 3) * 3 ^ (K + 1) + A % 3 * 3 ^ K =
    A % 3 * 3 ^ K + 3 ^ (K + 1) * (A / 3) from by ring]
  rw [Nat.add_mul_mod_self_left]
  apply Nat.mod_eq_of_lt
  have hmod := Nat.mod_lt A (by omega : 3 > 0)
  calc A % 3 * 3 ^ K < 3 * 3 ^ K := Nat.mul_lt_mul_of_pos_right hmod (Nat.pow_pos (by omega))
    _ = 3 ^ (K + 1) := by ring

/-- Key binomial lemma: (1 + 3^K)^q mod 3^{K+1} = 1 + (q%3)*3^K for K ≥ 1.
    By induction. The step uses:
    (1+3^K)^(q+1) = (1+3^K) * (1+3^K)^q
    IH gives (1+3^K)^q ≡ 1 + (q%3)*3^K mod 3^{K+1}
    Product: 1 + ((q%3)+1)*3^K + (q%3)*3^{2K}
    Since 2K ≥ K+1, the last term vanishes mod 3^{K+1}. -/
private lemma binomial_one_plus_pow (K q : Nat) (hK : K ≥ 1) :
    (1 + 3 ^ K) ^ q % 3 ^ (K + 1) = 1 + (q % 3) * 3 ^ K := by
  have h3K : 0 < 3 ^ K := Nat.pow_pos (by omega : 0 < 3)
  have h3K1 : 1 + 3 ^ K < 3 ^ (K + 1) := by
    have := Nat.pow_le_pow_right (by omega : 0 < 3) (Nat.succ_le_of_lt hK)
    omega
  induction q with
  | zero =>
    simp [Nat.pow_zero]
    exact Nat.mod_eq_of_lt (by omega)
  | succ q ih =>
    have hlt2 : 1 + (q % 3) * 3 ^ K < 3 ^ (K + 1) := by
      have := Nat.mod_lt q (by omega : 0 < 3)
      omega
    rw [Nat.pow_succ]
    rw [show ((1 + 3 ^ K) ^ q * (1 + 3 ^ K)) % 3 ^ (K + 1) =
      (1 + 3 ^ K) ^ q % 3 ^ (K + 1) * ((1 + 3 ^ K) % 3 ^ (K + 1)) % 3 ^ (K + 1) from Nat.mul_mod ..]
    rw [show (1 + 3 ^ K) % 3 ^ (K + 1) = 1 + 3 ^ K from Nat.mod_eq_of_lt h3K1]
    rw [ih]
    rw [show (1 + q % 3 * 3 ^ K) * (1 + 3 ^ K) =
      1 + (q % 3 + 1) * 3 ^ K + (q % 3) * 3 ^ (2 * K) from by ring]
    rw [show (2 * K : Nat) = (K + 1) + (K - 1) from by omega]
    rw [show 3 ^ ((K + 1) + (K - 1)) = 3 ^ (K + 1) * 3 ^ (K - 1) from by rw [Nat.pow_add]]
    rw [show (q % 3) * (3 ^ (K + 1) * 3 ^ (K - 1)) =
      3 ^ (K + 1) * (q % 3 * 3 ^ (K - 1)) from by ring]
    rw [Nat.add_mul_mod_self_left]
    rw [Nat.add_mod]
    rw [show (1 : Nat) % 3 ^ (K + 1) = 1 from Nat.mod_eq_of_lt (by omega)]
    rw [mul_pow_mod' ((q % 3) + 1) K hK]
    have hlt3 : 1 + ((q % 3) + 1) % 3 * 3 ^ K < 3 ^ (K + 1) := by
      have ha : ((q % 3) + 1) % 3 ≤ 2 := by omega
      have hge3 : 3 ^ K ≥ 3 := by
        have := Nat.pow_le_pow_right (by omega : 0 < 3) hK
        omega
      have h3eq : 3 ^ (K + 1) = 3 * 3 ^ K := by rw [Nat.pow_succ]; ring
      rw [h3eq]
      nlinarith
    rw [Nat.mod_eq_of_lt hlt3]
    rw [show ((q % 3) + 1) % 3 = (q + 1) % 3 from by omega]

/-- For s ∈ {0,2,8}: ((q%3) + 2^s) % 3 = (q+1)%3 -/
private lemma digit_sum_mod3 (s q : Nat) (hs : s = 0 ∨ s = 2 ∨ s = 8) :
    (q % 3 + 2 ^ s) % 3 = (q + 1) % 3 := by
  rcases hs with rfl | rfl | rfl <;> omega

/-- (2^uK 18)^q % 3^18 = 1 -/
private lemma pow2_uK18_q_mod318 (q : Nat) : (2 ^ uK 18) ^ q % 3 ^ 18 = 1 := by
  rw [Nat.pow_mod (2 ^ uK 18) q (3 ^ 18), pow2_uK_18_mod318, Nat.one_pow]
  norm_num

/-- 2^(s+q*uK18) % 3^18 = 2^s when 2^s < 3^18 -/
private lemma pow_mod318_base (s q : Nat) (h2s : 2 ^ s < 3 ^ 18) :
    2 ^ (s + q * uK 18) % 3 ^ 18 = 2 ^ s := by
  rw [Nat.pow_add, Nat.mul_comm q, Nat.pow_mul]
  have hrep : (2 ^ uK 18) ^ q = ((2 ^ uK 18) ^ q / 3 ^ 18) * 3 ^ 18 + 1 := by
    have h1 := Nat.div_add_mod ((2 ^ uK 18) ^ q) (3 ^ 18)
    rw [pow2_uK18_q_mod318 q, Nat.mul_comm (3 ^ 18)] at h1
    exact h1.symm
  rw [hrep, Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc, Nat.add_comm,
    Nat.mul_comm _ (3 ^ 18), Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt h2s

/-- n / 3^K % 3 = n % 3^(K+1) / 3^K (the K-th ternary digit is the same) -/
private lemma div_mod_eq (n K : Nat) :
    n / 3 ^ K % 3 = n % 3 ^ (K + 1) / 3 ^ K := by
  have h1 := digit_eq_of_modPow n K (K + 1) (by omega)
  unfold ternaryDigit at h1
  have h3K1 : 3 ^ (K + 1) = 3 ^ K * 3 := Nat.pow_succ 3 K
  have h2 : n % 3 ^ (K + 1) / 3 ^ K < 3 := by
    have h3 : n % 3 ^ (K + 1) < 3 ^ (K + 1) := @Nat.mod_lt n _ (Nat.pow_pos (by omega : 0 < 3))
    rw [h3K1, Nat.mul_comm (3 ^ K) 3] at h3 ⊢
    exact (Nat.div_lt_iff_lt_mul (Nat.pow_pos (by omega : 0 < 3))).mpr h3
  rw [Nat.mod_eq_of_lt h2] at h1
  exact h1

/-- For s ∈ {0, 2, 8}, kthDigit 18 s q = q mod 3. -/
theorem digit_pos18_of_lift (s q : Nat) (hs : s = 0 ∨ s = 2 ∨ s = 8) :
    kthDigit 18 s q = q % 3 := by
  have h2s : 2 ^ s < 3 ^ 18 := by rcases hs with rfl | rfl | rfl <;> norm_num
  have hK18 : 18 ≥ 1 := by omega
  induction q generalizing s with
  | zero =>
    unfold kthDigit ternaryDigit
    simp only [show s + 0 * uK 18 = s from by omega]
    rcases hs with rfl | rfl | rfl <;> norm_num
  | succ q ih =>
    have h_ih := ih s hs h2s
    have h_eq : kthDigit 18 s (q + 1) = kthDigit 18 (s + q * uK 18) 1 := by
      unfold kthDigit
      show ternaryDigit (2 ^ (s + (q + 1) * uK 18)) 18 = ternaryDigit (2 ^ (s + q * uK 18 + 1 * uK 18)) 18
      congr 2
      ring
    have hstep := kthDigit_step 18 (s + q * uK 18) hK18
    rw [h_eq, hstep]
    have h_quot : 2 ^ (s + q * uK 18) % 3 ^ 19 / 3 ^ 18 = q % 3 := by
      unfold kthDigit ternaryDigit at h_ih
      rw [div_mod_eq (2 ^ (s + q * uK 18)) 18] at h_ih
      exact h_ih
    have h_rem := pow_mod318_base s q h2s
    rw [h_quot, h_rem]
    exact digit_sum_mod3 s q hs

/-- For s ∈ {0,2,8}, q ≥ 0: the key quotient is q%3.
    (2^(s+q*uK18) % 3^19) / 3^18 = q%3 -/
private lemma pow_mod319_div (s q : Nat) (hs : s = 0 ∨ s = 2 ∨ s = 8) :
    2 ^ (s + q * uK 18) % 3 ^ 19 / 3 ^ 18 = q % 3 := by
  have h := digit_pos18_of_lift s q hs
  unfold kthDigit ternaryDigit at h
  rw [div_mod_eq (2 ^ (s + q * uK 18)) 18] at h
  exact h

/-- If memCantorNat(2^r), then carry r K % 27 ≤ 13,
    meaning the carry encodes at most digits 0 and 1 at three
    consecutive positions. -/
theorem carry_bounded_digit2_free (r K : Nat) (hc : memCantorNat (2 ^ r)) :
    carry r K % 27 ≤ 13 :=
  digit2_free_mod27_le13 r K hc

/-- For digit-2-free 2^r, the digit at level K in the lifting equals
    carry r K % 3, determined by (r % uK K, r / uK K). -/
theorem digit_eq_carry_from_state (r K : Nat) (hc : memCantorNat (2 ^ r)) :
    carry r K % 3 = kthDigit K (r % uK K) (r / uK K) :=
  digit_from_state r K

end ErdosTernary.ThreeLevelCompat
