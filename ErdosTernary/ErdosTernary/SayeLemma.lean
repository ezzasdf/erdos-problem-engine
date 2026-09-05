/-
  Saye's Lemma: The key property powering the recursive algorithm.

  For u_k = 2·3^{k-1} (period of 2^n mod 3^k):
  The (k+1)st ternary digit of 2^{i·u_k + j} satisfies:
    d_{k+1}(2^{i·u_k+j}) ≡ d_{k+1}(2^j) + i · d₁(2^j)  (mod 3)

  This means adding multiples of u_k cycles the (k+1)st ternary digit through {0,1,2},
  allowing recursive construction of powers of 2 with prescribed trailing digits.

  Reference: Robert I. Saye, arXiv:2202.13256, 2022.
-/

import Mathlib.Tactic
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic

namespace ErdosTernary.SayeLemma

/- The k-th ternary digit of n (1-indexed from least significant).
    d_k(n) = ⌊n / 3^{k-1}⌋ mod 3 -/
def ternaryDigit (n k : Nat) : Nat :=
  (n / 3 ^ (k - 1)) % 3

/- u_k = 2 · 3^{k-1}: the period of 2^n mod 3^k -/
def u (k : Nat) : Nat :=
  2 * 3 ^ (k - 1)

/- c_k: the "coefficient" such that 2^{u_k} = 1 + c_k · 3^k.
   We prove c_k ≡ 1 (mod 3) by induction. -/
def c (k : Nat) : Nat :=
  (2 ^ u k - 1) / 3 ^ k

/- ============================================================ -/
/- Part 1: Basic properties                                      -/
/- ============================================================ -/

@[simp] theorem ternaryDigit_zero (k : Nat) : ternaryDigit 0 k = 0 := by
  simp [ternaryDigit]

@[simp] theorem ternaryDigit_lt_three (n k : Nat) : ternaryDigit n k < 3 :=
  Nat.mod_lt _ (by omega)

/- u_k values -/
@[simp] theorem u_1 : u 1 = 2 := by native_decide
@[simp] theorem u_2 : u 2 = 6 := by native_decide
@[simp] theorem u_3 : u 3 = 18 := by native_decide
@[simp] theorem u_4 : u 4 = 54 := by native_decide

/- c_k values (computed) -/
@[simp] theorem c_1 : c 1 = 1 := by native_decide
@[simp] theorem c_2 : c 2 = 7 := by native_decide
@[simp] theorem c_3 : c 3 = 9709 := by native_decide

/- c_k ≡ 1 (mod 3) for small k -/
example : c 1 % 3 = 1 := by native_decide
example : c 2 % 3 = 1 := by native_decide
example : c 3 % 3 = 1 := by native_decide
example : c 4 % 3 = 1 := by native_decide
example : c 5 % 3 = 1 := by native_decide

/- ============================================================ -/
/- Part 2: pow_u_mod — 2^{u_k} ≡ 1 (mod 3^k)                    -/
/- ============================================================ -/

/- Helper: cube of (1 + a·3^k) is ≡ 1 (mod 3^{k+1}) -/
theorem cube_one_add (a k : Nat) (hk : k ≥ 1) :
    (1 + a * 3 ^ k) ^ 3 % 3 ^ (k + 1) = 1 := by
  have h1 : (1 + a * 3 ^ k) ^ 3 =
      1 + a * 3 ^ (k + 1) + a ^ 2 * 3 ^ (2 * k + 1) + a ^ 3 * 3 ^ (3 * k) := by ring
  rw [h1]
  have hA : a * 3 ^ (k + 1) % 3 ^ (k + 1) = 0 := by
    exact Nat.mod_eq_zero_of_dvd (by simpa [mul_comm] using dvd_mul_right (3 ^ (k + 1)) a)
  have hB : a ^ 2 * 3 ^ (2 * k + 1) % 3 ^ (k + 1) = 0 := by
    have hdvd : 3 ^ (k + 1) ∣ 3 ^ (2 * k + 1) := Nat.pow_dvd_pow 3 (by omega)
    exact Nat.mod_eq_zero_of_dvd (by simpa [mul_comm, mul_left_comm, mul_assoc] using hdvd.mul_right (a ^ 2))
  have hC : a ^ 3 * 3 ^ (3 * k) % 3 ^ (k + 1) = 0 := by
    have hdvd : 3 ^ (k + 1) ∣ 3 ^ (3 * k) := Nat.pow_dvd_pow 3 (by omega : k + 1 ≤ 3 * k)
    exact Nat.mod_eq_zero_of_dvd (by simpa [mul_comm, mul_left_comm, mul_assoc] using hdvd.mul_right (a ^ 3))
  have hSum : (a * 3 ^ (k + 1) + a ^ 2 * 3 ^ (2 * k + 1) + a ^ 3 * 3 ^ (3 * k)) % 3 ^ (k + 1) = 0 := by
    simp [Nat.add_mod, hA, hB, hC]
  rw [show 1 + a * 3 ^ (k + 1) + a ^ 2 * 3 ^ (2 * k + 1) + a ^ 3 * 3 ^ (3 * k) =
      1 + (a * 3 ^ (k + 1) + a ^ 2 * 3 ^ (2 * k + 1) + a ^ 3 * 3 ^ (3 * k)) by ring]
  rw [Nat.add_mod, hSum]
  have hlt : 1 < 3 ^ (k + 1) := by omega
  simpa [Nat.mod_eq_of_lt hlt]

/- Main theorem: 2^{u_k} ≡ 1 (mod 3^k) -/
theorem pow_u_mod (k : Nat) (hk : k ≥ 1) :
    2 ^ u k % 3 ^ k = 1 := by
  unfold u
  -- We prove a stronger statement by induction on m:
  -- For all m ≥ 1: 2^(2*3^(m-1)) % 3^m = 1
  have hmain : ∀ m, m ≥ 1 → 2 ^ (2 * 3 ^ (m - 1)) % 3 ^ m = 1 := by
    intro m
    induction m with
    | zero => intro hm; omega
    | succ m ih =>
      intro hm
      by_cases h0 : m = 0
      · -- m = 0: 2^(2*3^0) % 3^1 = 2^2 % 3 = 4 % 3 = 1
        subst h0; simp
      · -- m ≥ 1: use IH and cube_one_add
        have hk : m ≥ 1 := by omega
        have ih_val := ih hk
        -- ih_val : 2^(2*3^(m-1)) % 3^m = 1
        -- We need: 2^(2*3^m) % 3^(m+1) = 1
        -- Note: 2^(2*3^m) = (2^(2*3^(m-1)))^3
        have h1 : 2 ^ (2 * 3 ^ m) = (2 ^ (2 * 3 ^ (m - 1))) ^ 3 := by
          rw [← Nat.pow_mul]
          have hpow : 3 ^ m = 3 ^ (m - 1) * 3 := by
            have hm1 : m = m - 1 + 1 := by omega
            nth_rewrite 1 [hm1]
            rw [pow_succ]
          rw [show 2 * 3 ^ m = (2 * 3 ^ (m - 1)) * 3 by rw [hpow]; ring]
        have hsub : (m + 1) - 1 = m := by omega
        rw [hsub]
        rw [h1]
        -- From ih_val: 2^(2*3^(m-1)) = 1 + c*3^m for some c
        -- where c = (2^(2*3^(m-1)) - 1) / 3^m
        have h2 : 2 ^ (2 * 3 ^ (m - 1)) = 1 + (2 ^ (2 * 3 ^ (m - 1)) - 1) / 3 ^ m * 3 ^ m := by
          have hmodadd := Nat.mod_add_div (2 ^ (2 * 3 ^ (m - 1))) (3 ^ m)
          rw [ih_val] at hmodadd
          rw [← hmodadd]
          have hsub : (1 + 3 ^ m * (2 ^ (2 * 3 ^ (m - 1)) / 3 ^ m)) - 1 =
              3 ^ m * (2 ^ (2 * 3 ^ (m - 1)) / 3 ^ m) := by omega
          rw [hsub]
          rw [Nat.mul_div_right _ (by omega : 0 < 3 ^ m)]
          ring
        rw [h2]
        apply cube_one_add
        exact hk
  exact hmain k hk

/- ============================================================ -/
/- Part 3: c_k ≡ 1 (mod 3) — by induction                        -/
/- ============================================================ -/

/- Helper: if a ≡ b (mod 3) and z ≡ 0 (mod 3), then a + z ≡ b (mod 3) -/
theorem add_mod_three (x y z : Nat) (hx : x % 3 = y % 3) (hz : z % 3 = 0) :
    (x + z) % 3 = y % 3 := by omega

/- Helper: a * 3^k ≡ 0 (mod 3) for k ≥ 1 -/
theorem mul_pow_three_mod (a k : Nat) (hk : k ≥ 1) :
    (a * 3 ^ k) % 3 = 0 := by
  have hdvd : 3 ∣ 3 ^ k := by
    simpa using Nat.pow_dvd_pow 3 (by omega : 1 ≤ k)
  exact Nat.mod_eq_zero_of_dvd (hdvd.mul_left a)

/- Helper: a^2 * 3^(2k+1) ≡ 0 (mod 3) for k ≥ 1 -/
theorem mul_sq_pow_three_mod (a k : Nat) (hk : k ≥ 1) :
    (a ^ 2 * 3 ^ (2 * k + 1)) % 3 = 0 := by
  have hdvd : 3 ∣ 3 ^ (2 * k + 1) := by
    simpa using Nat.pow_dvd_pow 3 (by omega : 1 ≤ 2 * k + 1)
  exact Nat.mod_eq_zero_of_dvd (hdvd.mul_left (a ^ 2))

/- Helper: a^3 * 3^(3k) ≡ 0 (mod 3) for k ≥ 1 -/
theorem mul_cu_pow_three_mod (a k : Nat) (hk : k ≥ 1) :
    (a ^ 3 * 3 ^ (3 * k)) % 3 = 0 := by
  have hdvd : 3 ∣ 3 ^ (3 * k) := by
    simpa using Nat.pow_dvd_pow 3 (by omega : 1 ≤ 3 * k)
  exact Nat.mod_eq_zero_of_dvd (hdvd.mul_left (a ^ 3))

/- Helper: (x + m·3^{k+1})^3 ≡ x^3 (mod 3^{k+2}) -/
private theorem cube_cong_mod_aux (x m k : Nat) :
    (x + m * 3 ^ (k + 1)) ^ 3 % 3 ^ (k + 2) = x ^ 3 % 3 ^ (k + 2) := by
  rw [show (x + m * 3 ^ (k + 1)) ^ 3 =
    x ^ 3 + 3 * x ^ 2 * (m * 3 ^ (k + 1)) + 3 * x * (m * 3 ^ (k + 1)) ^ 2 + (m * 3 ^ (k + 1)) ^ 3 by ring]
  have h1 : (3 * x ^ 2 * (m * 3 ^ (k + 1))) % 3 ^ (k + 2) = 0 := by
    refine Nat.mod_eq_zero_of_dvd ⟨x ^ 2 * m, ?_⟩
    rw [show 3 * x ^ 2 * (m * 3 ^ (k + 1)) = 3 * (3 ^ (k + 1)) * (x ^ 2 * m) from by ring]
    rw [show 3 * 3 ^ (k + 1) = 3 ^ (k + 2) from by rw [mul_comm, ← pow_succ]]
  have h2 : (3 * x * (m * 3 ^ (k + 1)) ^ 2) % 3 ^ (k + 2) = 0 := by
    refine Nat.mod_eq_zero_of_dvd ⟨x * m ^ 2 * 3 ^ (k + 1), ?_⟩
    rw [show (m * 3 ^ (k + 1)) ^ 2 = (3 ^ (k + 1)) ^ 2 * m ^ 2 from by ring]
    rw [show (3 ^ (k + 1)) ^ 2 = 3 ^ (2 * (k + 1)) from by
      rw [← Nat.pow_mul]
      congr 1
      omega]
    rw [show 2 * (k + 1) = 2 * k + 2 from by omega]
    rw [show 3 * x * (3 ^ (2 * k + 2) * m ^ 2) = 3 * (3 ^ (2 * k + 2)) * (x * m ^ 2) from by ring]
    rw [show 3 * 3 ^ (2 * k + 2) = 3 ^ (2 * k + 3) from by rw [mul_comm, ← pow_succ]]
    rw [show 3 ^ (2 * k + 3) = 3 ^ (k + 2) * 3 ^ (k + 1) from by
      rw [show 2 * k + 3 = (k + 2) + (k + 1) from by omega, ← pow_add]]
    ring
  have h3 : ((m * 3 ^ (k + 1)) ^ 3) % 3 ^ (k + 2) = 0 := by
    refine Nat.mod_eq_zero_of_dvd ⟨m ^ 3 * 3 ^ (2 * k + 1), ?_⟩
    rw [show (m * 3 ^ (k + 1)) ^ 3 = (3 ^ (k + 1)) ^ 3 * m ^ 3 from by ring]
    rw [show (3 ^ (k + 1)) ^ 3 = 3 ^ (3 * (k + 1)) from by
      rw [← Nat.pow_mul]
      congr 1
      omega]
    rw [show 3 * (k + 1) = 3 * k + 3 from by omega]
    rw [show 3 ^ (3 * k + 3) = 3 ^ (k + 2) * 3 ^ (2 * k + 1) from by
      rw [show 3 * k + 3 = (k + 2) + (2 * k + 1) from by omega, ← pow_add]]
    ring
  have hSum : (3 * x ^ 2 * (m * 3 ^ (k + 1)) + 3 * x * (m * 3 ^ (k + 1)) ^ 2 + (m * 3 ^ (k + 1)) ^ 3) % 3 ^ (k + 2) = 0 := by
    rw [show 3 * x ^ 2 * (m * 3 ^ (k + 1)) + 3 * x * (m * 3 ^ (k + 1)) ^ 2 + (m * 3 ^ (k + 1)) ^ 3 =
        3 * x ^ 2 * (m * 3 ^ (k + 1)) + (3 * x * (m * 3 ^ (k + 1)) ^ 2 + (m * 3 ^ (k + 1)) ^ 3) by ring]
    rw [Nat.add_mod, h1]
    rw [show (3 * x * (m * 3 ^ (k + 1)) ^ 2 + (m * 3 ^ (k + 1)) ^ 3) % 3 ^ (k + 2) = 0 from by
      rw [Nat.add_mod, h2, h3]
      simp]
    simp
  rw [show x ^ 3 + 3 * x ^ 2 * (m * 3 ^ (k + 1)) + 3 * x * (m * 3 ^ (k + 1)) ^ 2 + (m * 3 ^ (k + 1)) ^ 3 =
      x ^ 3 + (3 * x ^ 2 * (m * 3 ^ (k + 1)) + 3 * x * (m * 3 ^ (k + 1)) ^ 2 + (m * 3 ^ (k + 1)) ^ 3) by ring]
  rw [Nat.add_mod, hSum]
  simp

/- Helper: if a ≡ b (mod 3^{k+1}), then a^3 ≡ b^3 (mod 3^{k+2}) for k ≥ 1 -/
theorem cube_cong_mod (a b k : Nat) (hk : k ≥ 1) (h : a % 3 ^ (k + 1) = b % 3 ^ (k + 1)) :
    a ^ 3 % 3 ^ (k + 2) = b ^ 3 % 3 ^ (k + 2) := by
  by_cases hge : b ≤ a
  · have hdiv : 3 ^ (k + 1) ∣ a - b := (Nat.modEq_iff_dvd' hge).mp h.symm
    obtain ⟨t, ht⟩ := hdiv
    rw [← Nat.sub_add_cancel hge, ht, mul_comm]
    simpa [add_comm] using cube_cong_mod_aux b t k
  · have hle : a ≤ b := le_of_not_ge hge
    have hdiv : 3 ^ (k + 1) ∣ b - a := (Nat.modEq_iff_dvd' hle).mp h
    obtain ⟨t, ht⟩ := hdiv
    rw [← Nat.sub_add_cancel hle, ht, mul_comm]
    symm
    simpa [add_comm] using cube_cong_mod_aux a t k

/- (1 + 3^k)^3 ≡ 1 + 3^{k+1} (mod 3^{k+2}) -/
theorem cube_three_pow (k : Nat) (hk : k ≥ 1) :
    (1 + 3 ^ k) ^ 3 % 3 ^ (k + 2) = 1 + 3 ^ (k + 1) := by
  have h1 : (1 + 3 ^ k) ^ 3 = 1 + 3 * 3 ^ k + 3 * (3 ^ k) ^ 2 + (3 ^ k) ^ 3 := by ring
  rw [h1]
  rw [show 3 * 3 ^ k = 3 ^ (k + 1) from by rw [mul_comm, ← pow_succ]]
  rw [show 3 * (3 ^ k) ^ 2 = 3 ^ (2 * k + 1) from by
    rw [show (3 ^ k) ^ 2 = 3 ^ (2 * k) from by
      rw [← Nat.pow_mul]
      congr 1
      omega]
    rw [show 3 * 3 ^ (2 * k) = 3 ^ (2 * k + 1) from by rw [mul_comm, ← pow_succ]]]
  rw [show (3 ^ k) ^ 3 = 3 ^ (3 * k) from by
    rw [← Nat.pow_mul]
    congr 1
    omega]
  have hk2 : 2 * k + 1 ≥ k + 2 := by omega
  have h2 : 3 ^ (2 * k + 1) % 3 ^ (k + 2) = 0 := by
    exact Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 3 hk2)
  have hk3 : 3 * k ≥ k + 2 := by omega
  have h3 : 3 ^ (3 * k) % 3 ^ (k + 2) = 0 := by
    exact Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 3 hk3)
  rw [show 1 + 3 ^ (k + 1) + 3 ^ (2 * k + 1) + 3 ^ (3 * k) = (1 + 3 ^ (k + 1)) + (3 ^ (2 * k + 1) + 3 ^ (3 * k)) from by ring]
  rw [Nat.add_mod]
  rw [show (3 ^ (2 * k + 1) + 3 ^ (3 * k)) % 3 ^ (k + 2) = 0 from by
    rw [Nat.add_mod, h2, h3]
    simp]
  simp
  apply Nat.mod_eq_of_lt
  rw [show 3 ^ (k + 2) = 3 * 3 ^ (k + 1) from by rw [pow_succ, mul_comm]]
  have hpos : 3 ^ (k + 1) > 0 := pow_pos (by norm_num) (k + 1)
  omega

/- Stronger form: 2^{u_k} mod 3^{k+1} = 1 + 3^k -/
theorem pow_u_mod_strong (k : Nat) (hk : k ≥ 1) :
    2 ^ u k % 3 ^ (k + 1) = 1 + 3 ^ k := by
  have hmain : ∀ m : Nat, 2 ^ (2 * 3 ^ m) % 3 ^ (m + 2) = 1 + 3 ^ (m + 1) := by
    intro m
    induction m with
    | zero =>
      norm_num
    | succ m ih =>
      have h1 : 2 ^ (2 * 3 ^ (m + 1)) = (2 ^ (2 * 3 ^ m)) ^ 3 := by
        rw [← Nat.pow_mul]
        congr 1
        rw [show 2 * 3 ^ (m + 1) = (2 * 3 ^ m) * 3 from by
          rw [pow_succ]
          ring]
      rw [h1]
      have h_cong : 2 ^ (2 * 3 ^ m) % 3 ^ (m + 2) = (1 + 3 ^ (m + 1)) % 3 ^ (m + 2) := by
        rw [ih]
        symm
        apply Nat.mod_eq_of_lt
        rw [show 3 ^ (m + 2) = 3 * 3 ^ (m + 1) from by rw [pow_succ, mul_comm]]
        have hpos : 3 ^ (m + 1) > 0 := pow_pos (by norm_num) (m + 1)
        omega
      have hk' : m + 1 ≥ 1 := by omega
      have h_lift := cube_cong_mod (2 ^ (2 * 3 ^ m)) (1 + 3 ^ (m + 1)) (m + 1) hk' h_cong
      have h_pow : (1 + 3 ^ (m + 1)) ^ 3 % 3 ^ (m + 3) = 1 + 3 ^ (m + 2) := by
        rw [show (1 + 3 ^ (m + 1)) ^ 3 =
            1 + 3 * 3 ^ (m + 1) + 3 * (3 ^ (m + 1)) ^ 2 + (3 ^ (m + 1)) ^ 3 by ring]
        have h2 : (3 * (3 ^ (m + 1)) ^ 2) % 3 ^ (m + 3) = 0 := by
          refine Nat.mod_eq_zero_of_dvd ⟨3 ^ m, ?_⟩
          rw [show 3 * (3 ^ (m + 1)) ^ 2 = 3 ^ (m + 3) * 3 ^ m from by
            rw [show (3 ^ (m + 1)) ^ 2 = 3 ^ (2 * (m + 1)) from by
              rw [← Nat.pow_mul]
              congr 1
              omega]
            rw [show 2 * (m + 1) = 2 * m + 2 from by omega]
            rw [show 3 * 3 ^ (2 * m + 2) = 3 ^ (2 * m + 3) from by rw [mul_comm, ← pow_succ]]
            rw [show 2 * m + 3 = (m + 3) + m from by omega, ← pow_add]]
        have h3 : ((3 ^ (m + 1)) ^ 3) % 3 ^ (m + 3) = 0 := by
          refine Nat.mod_eq_zero_of_dvd ⟨3 ^ (2 * m), ?_⟩
          rw [show (3 ^ (m + 1)) ^ 3 = 3 ^ (3 * (m + 1)) from by
            rw [← Nat.pow_mul]
            congr 1
            omega]
          rw [show 3 * (m + 1) = 3 * m + 3 from by omega]
          rw [show 3 ^ (3 * m + 3) = 3 ^ (m + 3) * 3 ^ (2 * m) from by
            rw [show 3 * m + 3 = (m + 3) + (2 * m) from by omega, ← pow_add]]
        rw [show 1 + 3 * 3 ^ (m + 1) + 3 * (3 ^ (m + 1)) ^ 2 + (3 ^ (m + 1)) ^ 3 =
            (1 + 3 * 3 ^ (m + 1)) + (3 * (3 ^ (m + 1)) ^ 2 + (3 ^ (m + 1)) ^ 3) by ring]
        rw [Nat.add_mod]
        rw [show (3 * (3 ^ (m + 1)) ^ 2 + (3 ^ (m + 1)) ^ 3) % 3 ^ (m + 3) = 0 from by
          rw [Nat.add_mod, h2, h3]
          simp]
        rw [add_zero, Nat.mod_mod]
        rw [show (1 + 3 * 3 ^ (m + 1)) % 3 ^ (m + 3) = 1 + 3 * 3 ^ (m + 1) from by
          apply Nat.mod_eq_of_lt
          rw [show 3 ^ (m + 3) = 3 * 3 ^ (m + 2) from by rw [pow_succ, mul_comm]]
          have hp : 3 ^ (m + 2) > 0 := pow_pos (by norm_num) (m + 2)
          omega]
        rw [show 3 * 3 ^ (m + 1) = 3 ^ (m + 2) from by rw [mul_comm, ← pow_succ]]
      rw [h_pow] at h_lift
      rw [h_lift]
  unfold u
  rw [show k + 1 = (k - 1) + 2 from by omega]
  rw [show k = (k - 1) + 1 from by omega]
  exact hmain (k - 1)

/- Main result: c_k ≡ 1 (mod 3) for all k ≥ 1 -/
theorem c_mod_three (k : Nat) (hk : k ≥ 1) :
    c k % 3 = 1 := by
  unfold c
  obtain ⟨t, ht⟩ : ∃ t, 2 ^ u k = 1 + 3 ^ k + t * 3 ^ (k + 1) := by
    refine ⟨2 ^ u k / 3 ^ (k + 1), ?_⟩
    rw [← pow_u_mod_strong k hk]
    conv_lhs => rw [← Nat.div_add_mod (2 ^ u k) (3 ^ (k + 1))]
    rw [mul_comm, add_comm]
  rw [ht]
  have hcalc : (1 + 3 ^ k + t * 3 ^ (k + 1) - 1) / 3 ^ k = 1 + t * 3 := by
    rw [show 3 ^ (k + 1) = 3 * 3 ^ k from by rw [pow_succ, mul_comm]]
    have hnum : 1 + 3 ^ k + t * (3 * 3 ^ k) = (1 + t * 3) * 3 ^ k + 1 := by ring
    rw [hnum]
    have hsub : (1 + t * 3) * 3 ^ k + 1 - 1 = (1 + t * 3) * 3 ^ k := by
      rw [Nat.add_sub_cancel]
    rw [hsub]
    rw [Nat.mul_div_left (1 + t * 3) (pow_pos (by norm_num) k)]
  rw [hcalc]
  rw [mul_comm, Nat.add_mul_mod_self_left, Nat.one_mod]

/- The inductive step: c_{k+1} ≡ c_k (mod 3) -/
theorem c_succ_mod_three (k : Nat) (hk : k ≥ 1) :
    c (k + 1) % 3 = c k % 3 := by
  rw [c_mod_three (k + 1) (by omega), c_mod_three k hk]

/- Base case: c_1 = 1 -/
theorem c_base : c 1 = 1 := by native_decide

/- ============================================================ -/
/- Part 4: The main lemma                                        -/
/- ============================================================ -/

private theorem two_pow_even_mod_three (j : Nat) : 2 ^ (2 * j) % 3 = 1 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show 2 * (j + 1) = 2 * j + 2 from by omega]
    rw [pow_add]
    rw [Nat.mul_mod, ih]
    norm_num

/- d₁(2^j) — the least significant ternary digit of 2^j.
   This cycles with period 2: d₁(2^j) = 1 if j even, 2 if j odd. -/
def d1 (j : Nat) : Nat :=
  ternaryDigit (2 ^ j) 1

theorem d1_pow_two_even (j : Nat) : d1 (2 * j) = 1 := by
  unfold d1 ternaryDigit
  simp [two_pow_even_mod_three]

theorem d1_pow_two_odd (j : Nat) : d1 (2 * j + 1) = 2 := by
  unfold d1 ternaryDigit
  have h1 : 2 ^ (2 * j + 1) % 3 = 2 := by
    rw [pow_add, Nat.mul_mod, two_pow_even_mod_three]
    norm_num
  simp [ternaryDigit, h1]

theorem d1_eq (j : Nat) : d1 j = if j % 2 = 0 then 1 else 2 := by
  have h : j = 2 * (j / 2) + j % 2 := by omega
  by_cases hj : j % 2 = 0
  · rw [h, hj]
    simp
    exact d1_pow_two_even (j / 2)
  · have hj1 : j % 2 = 1 := by omega
    rw [h, hj1]
    have hmod : (2 * (j / 2) + 1) % 2 = 1 := by omega
    simp [hmod]
    exact d1_pow_two_odd (j / 2)

/- Helper: (1 + 3^k)^i ≡ 1 + i·3^k (mod 3^{k+1}) for i ∈ {0, 1, 2} and k ≥ 1 -/
theorem pow_one_add_three (i k : Nat) (hi : i ≤ 2) (hk : k ≥ 1) :
    (1 + 3 ^ k) ^ i % 3 ^ (k + 1) = (1 + i * 3 ^ k) % 3 ^ (k + 1) := by
  match i with
  | 0 => simp
  | 1 => simp [Nat.pow_one]
  | 2 =>
    rw [show (1 + 3 ^ k) ^ 2 = 1 + 2 * 3 ^ k + (3 ^ k) ^ 2 from by ring]
    rw [show (3 ^ k) ^ 2 = 3 ^ (2 * k) from by
      rw [← Nat.pow_mul]
      congr 1
      omega]
    have hk2 : 2 * k ≥ k + 1 := by omega
    have h3k : 3 ^ (2 * k) % 3 ^ (k + 1) = 0 := by
      exact Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 3 hk2)
    rw [show 1 + 2 * 3 ^ k + 3 ^ (2 * k) = (1 + 2 * 3 ^ k) + 3 ^ (2 * k) from by ring]
    rw [Nat.add_mod, h3k, add_zero, Nat.mod_mod]
  | n + 3 => exact absurd (by omega : n + 3 ≤ 2) (by omega)

/- Helper: if a ≡ b (mod m), then a·c ≡ b·c (mod m) -/
theorem mul_cong_mod (a b c m : Nat) (h : a % m = b % m) :
    (a * c) % m = (b * c) % m := by
  exact Nat.ModEq.mul_right c h

/- 2^{u_k} ≡ 1 + 3^k (mod 3^{k+1}), as a congruence -/
theorem pow_u_mod_strong_mod (k : Nat) (hk : k ≥ 1) :
    2 ^ u k % 3 ^ (k + 1) = (1 + 3 ^ k) % 3 ^ (k + 1) := by
  rw [pow_u_mod_strong k hk]
  rw [show (1 + 3 ^ k) % 3 ^ (k + 1) = 1 + 3 ^ k from by
    apply Nat.mod_eq_of_lt
    rw [show 3 ^ (k + 1) = 3 * 3 ^ k from by rw [pow_succ, mul_comm]]
    have hpos : 3 ^ k > 0 := pow_pos (by norm_num) k
    omega]

/- Helper: 2^{i·u_k} ≡ (1 + 3^k)^i (mod 3^{k+1}) -/
theorem pow_u_pow_i (i k : Nat) (hi : i ≤ 2) (hk : k ≥ 1) :
    2 ^ (i * u k) % 3 ^ (k + 1) = (1 + 3 ^ k) ^ i % 3 ^ (k + 1) := by
  match i with
  | 0 => simp
  | 1 => simp [u]; exact pow_u_mod_strong_mod k hk
  | 2 =>
    rw [show 2 * u k = u k + u k from by ring]
    rw [Nat.pow_add]
    rw [mul_cong_mod (2 ^ u k) (1 + 3 ^ k) (2 ^ u k) (3 ^ (k + 1)) (pow_u_mod_strong_mod k hk)]
    rw [mul_comm]
    rw [mul_cong_mod (2 ^ u k) (1 + 3 ^ k) (1 + 3 ^ k) (3 ^ (k + 1)) (pow_u_mod_strong_mod k hk)]
    congr 1
    ring
  | n + 3 => exact absurd (by omega : n + 3 ≤ 2) (by omega)

/- Helper: (n % 3^k) % 3 = n % 3 for k ≥ 1 -/
theorem mod_pow_mod (n k : Nat) (hk : k ≥ 1) :
    n % 3 ^ k % 3 = n % 3 := by
  have hdvd : 3 ∣ 3 ^ k := Nat.pow_dvd_pow 3 (by omega : 1 ≤ k)
  exact Nat.mod_mod_of_dvd n hdvd

/- Helper: (n + i·r·3^k) / 3^k = n / 3^k + i·r when r = n % 3 and k ≥ 1 -/
theorem div_add_mul_mod (n i r k : Nat) (hr : r = n % 3) (hk : k ≥ 1) :
    (n + i * r * 3 ^ k) / 3 ^ k = n / 3 ^ k + i * r := by
  let q := n / 3 ^ k
  let s := n % 3 ^ k
  have hn : n = q * 3 ^ k + s := by
    simpa [q, s, Nat.mul_comm] using (Nat.div_add_mod n (3 ^ k)).symm
  have hs : s < 3 ^ k := by
    simpa [s] using Nat.mod_lt n (by omega : 0 < 3 ^ k)
  rw [hn]
  rw [show q * 3 ^ k + s + i * r * 3 ^ k = s + (q + i * r) * 3 ^ k from by ring]
  rw [Nat.add_mul_div_right s (q + i * r) (by omega : 0 < 3 ^ k)]
  have hs0 : s / 3 ^ k = 0 := Nat.div_eq_of_lt hs
  rw [hs0]
  rw [show q * 3 ^ k + s = s + q * 3 ^ k from by omega]
  rw [Nat.add_mul_div_right s q (by omega : 0 < 3 ^ k)]
  rw [hs0]
  omega

/- The main lemma: d_{k+1}(2^{i·u_k+j}) = (d_{k+1}(2^j) + i·d₁(2^j)) mod 3 -/
theorem saye_main_lemma (k : Nat) (i j : Nat) (hk : k ≥ 1) (hi : i ≤ 2) :
    ternaryDigit (2 ^ (i * u k + j)) (k + 1) =
    (ternaryDigit (2 ^ j) (k + 1) + i * d1 j) % 3 := by
  unfold d1 ternaryDigit u
  rw [show (k + 1) - 1 = k from by omega]
  rw [show 3 ^ (1 - 1) = 1 from by norm_num]
  rw [Nat.div_one]
  rw [Nat.div_mod_eq_mod_mul_div]
  rw [show 3 ^ k * 3 = 3 ^ (k + 1) from by rw [← pow_succ]]
  have hcong : 2 ^ (i * (2 * 3 ^ (k - 1)) + j) % 3 ^ (k + 1) =
      (2 ^ j + i * (2 ^ j % 3) * 3 ^ k) % 3 ^ (k + 1) := by
    have h_ui : 2 ^ (i * (2 * 3 ^ (k - 1))) % 3 ^ (k + 1) =
        (1 + i * 3 ^ k) % 3 ^ (k + 1) := by
      rw [← pow_one_add_three i k hi hk, ← pow_u_pow_i i k hi hk]
      rfl
    rw [show i * (2 * 3 ^ (k - 1)) + j = j + i * (2 * 3 ^ (k - 1)) from by ring,
        Nat.pow_add]
    rw [mul_comm]
    rw [mul_cong_mod (2 ^ (i * (2 * 3 ^ (k - 1)))) (1 + i * 3 ^ k) (2 ^ j) (3 ^ (k + 1)) h_ui]
    rw [show (1 + i * 3 ^ k) * 2 ^ j = 2 ^ j + i * 2 ^ j * 3 ^ k from by ring]
    rw [show i * 2 ^ j * 3 ^ k = i * (2 ^ j % 3) * 3 ^ k +
        i * (2 ^ j / 3) * 3 ^ (k + 1) from by
      conv_lhs => rw [show 2 ^ j = 3 * (2 ^ j / 3) + 2 ^ j % 3 from (Nat.div_add_mod (2 ^ j) 3).symm]
      rw [show 3 ^ (k + 1) = 3 ^ k * 3 from by rw [pow_succ]]
      ring]
    rw [show i * (2 ^ j / 3) * 3 ^ (k + 1) = 3 ^ (k + 1) * (i * (2 ^ j / 3)) from by ring]
    rw [← add_assoc]
    rw [Nat.add_mul_mod_self_left]
  rw [hcong]
  conv_lhs =>
    rw [show 3 ^ (k + 1) = 3 ^ k * 3 from by rw [pow_succ]]
    rw [Nat.mod_mul_right_div_self]
  have hdiv : (2 ^ j + i * (2 ^ j % 3) * 3 ^ k) / 3 ^ k = 2 ^ j / 3 ^ k + i * (2 ^ j % 3) := by
    exact div_add_mul_mod (2 ^ j) i (2 ^ j % 3) k (by rfl) hk
  rw [hdiv]
  rw [Nat.add_mod]
  conv_rhs => rw [Nat.add_mod, Nat.mod_mod]

/- ============================================================ -/
/- Part 5: Branching lemma — at least 2 of 3 branches survive     -/
/- ============================================================ -/

/- d₁(2^j) ∈ {1, 2}, never 0 mod 3 -/
theorem d1_mod3_ne_zero (j : Nat) : d1 j % 3 ≠ 0 := by
  unfold d1 ternaryDigit
  induction j with
  | zero => native_decide
  | succ j ih =>
    rw [show 3 ^ (1 - 1) = 1 from by norm_num, Nat.div_one]
    rw [show 2 ^ (j + 1) = 2 * 2 ^ j from by ring, Nat.mul_mod]
    have h0 : 2 ^ j % 3 ≠ 0 := by simpa using ih
    have hlt : 2 ^ j % 3 < 3 := Nat.mod_lt _ (by norm_num)
    have h12 : 2 ^ j % 3 = 1 ∨ 2 ^ j % 3 = 2 := by omega
    rcases h12 with h1 | h2
    · rw [h1]; norm_num
    · rw [h2]; norm_num

/- The map i ↦ (base + i * d) % 3 is injective on {0,1,2} when d % 3 ≠ 0 -/
private theorem affine_inj_mod3 (base d : Nat) (hd : d % 3 ≠ 0) :
    ∀ i₁ i₂, i₁ < 3 → i₂ < 3 →
      (base + i₁ * d) % 3 = (base + i₂ * d) % 3 → i₁ = i₂ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro i₁ i₂ h₁ h₂ heq
  have hmod : (base + i₁ * d) ≡ (base + i₂ * d) [MOD 3] := by
    simpa [Nat.ModEq] using heq
  have hcancel := Nat.ModEq.add_left_cancel (n := 3) (a := base) (b := base) (c := i₁ * d) (d := i₂ * d) (by rfl) hmod
  have h₁₂ : (↑(i₁ * d) : ZMod 3) = ↑(i₂ * d) :=
    (ZMod.natCast_eq_natCast_iff (i₁ * d) (i₂ * d) 3).mpr hcancel
  have hz : (i₁ : ZMod 3) * (d : ZMod 3) = (i₂ : ZMod 3) * (d : ZMod 3) := by
    exact_mod_cast h₁₂
  have hd0 : (d : ZMod 3) ≠ 0 := by
    intro h
    have hdvd : 3 ∣ d := (ZMod.natCast_zmod_eq_zero_iff_dvd d 3).mp h
    have : d % 3 = 0 := (Nat.dvd_iff_mod_eq_zero 3 d).mp hdvd
    exact hd this
  have hi : (i₁ : ZMod 3) = (i₂ : ZMod 3) := by
    exact mul_right_cancel₀ hd0 hz
  have hmeq : i₁ ≡ i₂ [MOD 3] := (ZMod.natCast_eq_natCast_iff i₁ i₂ 3).mp hi
  have hi₁' : i₁ % 3 = i₁ := Nat.mod_eq_of_lt h₁
  have hi₂' : i₂ % 3 = i₂ := Nat.mod_eq_of_lt h₂
  simpa [Nat.ModEq, hi₁', hi₂'] using hmeq

/- Exactly one i ∈ {0,1,2} maps to any given chi when d % 3 ≠ 0 -/
theorem exact_one_eq (base d chi : Nat) (hd : d % 3 ≠ 0) (hchi : chi < 3) :
    {i : Nat | i < 3 ∧ (base + i * d) % 3 = chi}.ncard = 1 := by
  have h3 : (3 : Nat) > 0 := by omega
  have hfin : ({i : Nat | i < 3 ∧ (base + i * d) % 3 = chi} : Set Nat).Finite :=
    (Set.finite_Iio 3).subset (fun _ h => h.1)
  have hb3 : base % 3 < 3 := Nat.mod_lt base (by norm_num)
  apply le_antisymm
  · rw [Set.ncard_le_one hfin]
    intro x hx y hy
    have hxy : (base + x * d) % 3 = (base + y * d) % 3 := by
      rw [hx.2, hy.2]
    exact affine_inj_mod3 base d hd x y hx.1 hy.1 hxy
  · have hd12 : d % 3 = 1 ∨ d % 3 = 2 := by omega
    rcases hd12 with hd1 | hd2
    · have hfind : (chi + 3 - base % 3) % 3 < 3 :=
        Nat.mod_lt _ h3
      have hmem : (chi + 3 - base % 3) % 3 ∈
          {i : Nat | i < 3 ∧ (base + i * d) % 3 = chi} := by
        constructor
        · exact hfind
        · rw [Nat.add_mod, Nat.mul_mod, hd1, Nat.mul_one]
          simp only [Nat.mod_mod]
          interval_cases base % 3 <;> interval_cases chi <;> norm_num
      exact (Set.ncard_pos hfin).mpr ⟨_, hmem⟩
    · have hfind : ((chi + 3 - base % 3) * 2) % 3 < 3 :=
        Nat.mod_lt _ h3
      have hmem : ((chi + 3 - base % 3) * 2) % 3 ∈
          {i : Nat | i < 3 ∧ (base + i * d) % 3 = chi} := by
        constructor
        · exact hfind
        · rw [Nat.add_mod, Nat.mul_mod, hd2]
          simp only [Nat.mod_mod]
          interval_cases base % 3 <;> interval_cases chi <;> norm_num
      exact (Set.ncard_pos hfin).mpr ⟨_, hmem⟩

/- The branching lemma: at each level k of Saye's search tree, for any base
   exponent j and forbidden digit chi ∈ {0,1,2}, among the three candidate
   extensions i·u_k + j for i ∈ {0,1,2}, at most one has its (k+1)-st ternary
   digit equal to chi. Hence at least two branches survive the pruning filter. -/
theorem saye_branching (k j chi : Nat) (hchi : chi < 3) (hk : k ≥ 1) :
    {i : Nat | i < 3 ∧ ternaryDigit (2 ^ (i * u k + j)) (k + 1) ≠ chi}.ncard ≥ 2 := by
  have hd := d1_mod3_ne_zero j
  have hbase : ternaryDigit (2 ^ j) (k + 1) < 3 := ternaryDigit_lt_three _ _
  -- The two sets are equal by saye_main_lemma
  have hset :
      {i : Nat | i < 3 ∧ ternaryDigit (2 ^ (i * u k + j)) (k + 1) ≠ chi} =
      {i : Nat | i < 3 ∧ (ternaryDigit (2 ^ j) (k + 1) + i * d1 j) % 3 ≠ chi} := by
    ext i; constructor <;> intro ⟨hi1, hi2⟩
    · exact ⟨hi1, fun h => hi2 (by rw [saye_main_lemma k i j hk (by omega : i ≤ 2)]; exact h)⟩
    · exact ⟨hi1, fun h => hi2 (by rw [← saye_main_lemma k i j hk (by omega : i ≤ 2)]; exact h)⟩
  rw [hset]
  -- The complement set has exactly 1 element (injectivity + existence)
  have h_eq1 : {i : Nat | i < 3 ∧ (ternaryDigit (2 ^ j) (k + 1) + i * d1 j) % 3 = chi}.ncard = 1 :=
    exact_one_eq (ternaryDigit (2 ^ j) (k + 1)) (d1 j) chi hd hchi
  have h_total : ({i : Nat | i < 3} : Set Nat).ncard = 3 := by
    have h : ({i : Nat | i < 3} : Set Nat) = ({0, 1, 2} : Set Nat) := by
      ext i
      constructor
      · intro hi; simp at hi; simp; omega
      · intro hi; simp at hi; simp; omega
    rw [h]; norm_num
  have h_union :
      {i : Nat | i < 3 ∧ (ternaryDigit (2 ^ j) (k + 1) + i * d1 j) % 3 ≠ chi} ∪
      {i : Nat | i < 3 ∧ (ternaryDigit (2 ^ j) (k + 1) + i * d1 j) % 3 = chi} =
      {i : Nat | i < 3} := by
    ext i; constructor
    · rintro (h | h) <;> exact h.1
    · intro h
      by_cases hc : (ternaryDigit (2 ^ j) (k + 1) + i * d1 j) % 3 = chi
      · exact Or.inr ⟨h, hc⟩
      · exact Or.inl ⟨h, hc⟩
  have h_disj :
      Disjoint {i : Nat | i < 3 ∧ (ternaryDigit (2 ^ j) (k + 1) + i * d1 j) % 3 ≠ chi}
        {i : Nat | i < 3 ∧ (ternaryDigit (2 ^ j) (k + 1) + i * d1 j) % 3 = chi} := by
    rw [Set.disjoint_left]; intro i his hit; exact his.2 hit.2
  have hfin1 : {i : Nat | i < 3 ∧ (ternaryDigit (2 ^ j) (k + 1) + i * d1 j) % 3 ≠ chi}.Finite :=
    (Set.finite_Iio 3).subset (fun _ h => h.1)
  have hfin2 : {i : Nat | i < 3 ∧ (ternaryDigit (2 ^ j) (k + 1) + i * d1 j) % 3 = chi}.Finite :=
    (Set.finite_Iio 3).subset (fun _ h => h.1)
  have hncard := Set.ncard_union_eq h_disj hfin1 hfin2
  rw [h_union, h_total, h_eq1] at hncard
  omega

/- ============================================================ -/
/- Part 6: Computational verification for small values           -/
/- ============================================================ -/

-- Main lemma verified computationally
-- k=3, j=5: d₄(2^5) = 1, d₁(2^5) = 2
example : ternaryDigit (2 ^ (0 * u 3 + 5)) 4 = (ternaryDigit (2 ^ 5) 4 + 0 * d1 5) % 3 := by native_decide
example : ternaryDigit (2 ^ (1 * u 3 + 5)) 4 = (ternaryDigit (2 ^ 5) 4 + 1 * d1 5) % 3 := by native_decide
example : ternaryDigit (2 ^ (2 * u 3 + 5)) 4 = (ternaryDigit (2 ^ 5) 4 + 2 * d1 5) % 3 := by native_decide

-- k=2, j=3: d₃(2^3) = 0, d₁(2^3) = 2
example : ternaryDigit (2 ^ (0 * u 2 + 3)) 3 = (ternaryDigit (2 ^ 3) 3 + 0 * d1 3) % 3 := by native_decide
example : ternaryDigit (2 ^ (1 * u 2 + 3)) 3 = (ternaryDigit (2 ^ 3) 3 + 1 * d1 3) % 3 := by native_decide
example : ternaryDigit (2 ^ (2 * u 2 + 3)) 3 = (ternaryDigit (2 ^ 3) 3 + 2 * d1 3) % 3 := by native_decide

-- k=4, j=0: d₅(2^0) = 1, d₁(2^0) = 1
example : ternaryDigit (2 ^ (0 * u 4 + 0)) 5 = (ternaryDigit (2 ^ 0) 5 + 0 * d1 0) % 3 := by native_decide
example : ternaryDigit (2 ^ (1 * u 4 + 0)) 5 = (ternaryDigit (2 ^ 0) 5 + 1 * d1 0) % 3 := by native_decide
example : ternaryDigit (2 ^ (2 * u 4 + 0)) 5 = (ternaryDigit (2 ^ 0) 5 + 2 * d1 0) % 3 := by native_decide

end ErdosTernary.SayeLemma