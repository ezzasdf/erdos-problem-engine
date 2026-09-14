import Mathlib.Tactic
import ErdosTernary.BridgeCompute
import ErdosTernary.Narkiewicz
import ErdosTernary.Lifting

open ErdosTernary.BridgeCompute
open Narkiewicz
open ErdosTernary.Lifting

namespace ErdosTernary.CarryAnalysis

def carry (r K : Nat) : Nat := 2 ^ r / 3 ^ K

theorem digit3_eq_carry (r K : Nat) :
    digit₃ (2 ^ r) K = carry r K % 3 := by
  unfold digit₃ carry; rfl

theorem carry_zero_survivor : ∀ K, carry 0 K % 3 ≠ 2 := by
  intro K; unfold carry; simp only [Nat.pow_zero, Nat.div_one]
  rcases K with _ | K
  · norm_num
  · have h1 : 1 < 3 ^ (K + 1) := by
      have h := Nat.pow_le_pow_right (n := 3) (by omega) (i := 1) (j := K + 1) (by omega)
      linarith
    have h2 : 0 < 3 ^ (K + 1) := Nat.pow_pos (by omega)
    rw [(Nat.div_eq_zero_iff h2).mpr h1]; norm_num

theorem carry_two_survivor : ∀ K, carry 2 K % 3 ≠ 2 := by
  intro K; unfold carry; simp only [show 2 ^ 2 = 4 from rfl]
  rcases K with _ | K
  · norm_num
  · rcases K with _ | K
    · norm_num
    · have h4lt : 4 < 3 ^ (K + 2) := by
        have h := Nat.pow_le_pow_right (n := 3) (by omega) (i := 2) (j := K + 2) (by omega)
        linarith
      have h2 : 0 < 3 ^ (K + 2) := Nat.pow_pos (by omega)
      rw [(Nat.div_eq_zero_iff h2).mpr h4lt]; norm_num

theorem carry_eight_survivor : ∀ K, carry 8 K % 3 ≠ 2 := by
  intro K; unfold carry; simp only [show 2 ^ 8 = 256 from rfl]
  rcases Nat.lt_or_ge K 6 with hK | hK
  · interval_cases K <;> norm_num
  · have h256lt : 256 < 3 ^ K := by
      have h := Nat.pow_le_pow_right (n := 3) (by omega) (i := 6) (j := K) hK
      linarith
    have h2 : 0 < 3 ^ K := Nat.pow_pos (by omega)
    rw [(Nat.div_eq_zero_iff h2).mpr h256lt]; norm_num

/-! ## Carry decomposition: the fundamental identity

The carry at position K decomposes as:

    carry(r, K) = digit_K(2^r) + 3 * carry(r, K+1)

This means the carry at position K depends on BOTH:
1. The digit at position K (local information, given by the lifting structure)
2. The carry at position K+1 (global information, depends on 2^r / 3^{K+1})

The lifting structure provides (1) but not (2). The full carry sequence
is determined by the COMPLETE base-3 representation of 2^r.
-/

theorem div3_eq (a K : Nat) : a / 3 ^ K / 3 = a / 3 ^ (K + 1) := by
  rw [show 3 ^ (K + 1) = 3 ^ K * 3 from by ring, Nat.div_div_eq_div_mul]

theorem carry_decomp (r K : Nat) :
    carry r K = (2 ^ r / 3 ^ K) % 3 + 3 * carry r (K + 1) := by
  simp only [carry]
  have h := Nat.div_add_mod (2 ^ r / 3 ^ K) 3
  rw [div3_eq] at h
  linarith

theorem carry_digit_link (r K : Nat) :
    carry r K = digit₃ (2 ^ r) K + 3 * carry r (K + 1) := by
  show carry r K = carry r K % 3 + 3 * carry r (K + 1)
  exact carry_decomp r K

/-!
The lifting picture says: r = q_K * u_K + r_K, and the digit at position K
is determined by (r_K, q_K). But carry(r, K) = digit_K(2^r) + 3 * carry(r, K+1)
involves carry(r, K+1), which depends on 2^r / 3^{K+1} — a GLOBAL quantity
that cannot be recovered from (r_K, q_K) alone.

This is why the lifting structure alone cannot determine the carry sequence.
The carry sequence requires knowledge of the FULL value of 2^r.
-/

end ErdosTernary.CarryAnalysis

namespace ErdosTernary.CarryAnalysis

theorem digit2_free_digits (r : Nat) (hc : memCantorNat (2 ^ r)) :
    ∀ K, carry r K % 3 ≠ 2 := by
  intro K
  rw [← digit3_eq_carry]
  exact hc K

theorem digit2_free_recurrence (r : Nat) (_hc : memCantorNat (2 ^ r)) :
    ∀ K, carry r K = 3 * carry r (K + 1) + carry r K % 3 := by
  intro K
  have h := carry_decomp r K
  omega

theorem digit2_free_digit_le_one (r : Nat) (hc : memCantorNat (2 ^ r)) :
    ∀ K, carry r K % 3 ≤ 1 := by
  intro K
  have := digit2_free_digits r hc K
  have := Nat.mod_lt (carry r K) (by omega : (0 : Nat) < 3)
  omega

theorem pow2_le_pow3 : ∀ r, 2 ^ r ≤ 3 ^ r
  | 0 => by norm_num
  | r + 1 => by
    have ih := pow2_le_pow3 r
    calc 2 ^ (r + 1) = 2 * 2 ^ r := by ring
      _ ≤ 3 * 2 ^ r := Nat.mul_le_mul_right _ (by norm_num)
      _ ≤ 3 * 3 ^ r := Nat.mul_le_mul_left _ ih
      _ = 3 ^ (r + 1) := by ring

theorem pow2_lt_pow3_succ (r : Nat) : 2 ^ r < 3 ^ (r + 1) := by
  calc 2 ^ r ≤ 3 ^ r := pow2_le_pow3 r
    _ < 3 ^ (r + 1) := Nat.pow_lt_pow_right (by norm_num : 1 < 3) (by omega)

theorem digit2_free_terminate (r : Nat) : ∃ K, carry r K = 0 := by
  refine ⟨r + 1, ?_⟩
  unfold carry
  rw [Nat.div_eq_zero_iff (Nat.pow_pos (by omega : 0 < 3))]
  exact pow2_lt_pow3_succ r

theorem carry_shrink (r K : Nat) (hd : carry r K % 3 ≤ 1) (hpos : carry r K > 0) :
    carry r (K + 1) < carry r K := by
  have h := carry_decomp r K
  unfold carry at h hpos hd ⊢
  have hmod := Nat.mod_lt (2 ^ r / 3 ^ K) (by omega : (0 : Nat) < 3)
  omega

theorem carry_lift_bridge (r K s q : Nat) (hr : r = s + q * uK K) (_hq : q ≤ 2) :
    carry r K % 3 = kthDigit K s q := by
  unfold carry kthDigit ternaryDigit
  subst hr
  rfl

theorem survivor_carry_step (r K s q : Nat) (hr : r = s + q * uK K) (hq : q ≤ 2)
    (_hd2 : kthDigit K s q ≠ 2) :
    carry r (K + 1) = (carry r K - kthDigit K s q) / 3 := by
  have hbridge := carry_lift_bridge r K s q hr hq
  have hdecomp := carry_decomp r K
  have hmod := Nat.mod_lt (carry r K) (by omega : (0 : Nat) < 3)
  omega

theorem digit2_free_descent (r : Nat) (hc : memCantorNat (2 ^ r)) :
    ∀ K, carry r K > 0 → carry r (K + 1) < carry r K := by
  intro K hpos
  have hd := digit2_free_digit_le_one r hc K
  exact carry_shrink r K hd hpos

theorem digit2_free_carry_le (r K : Nat) (hc : memCantorNat (2 ^ r)) :
    carry r (K + 1) ≤ carry r K / 3 := by
  have h := carry_decomp r K
  have hd := digit2_free_digit_le_one r hc K
  unfold carry at h hd ⊢
  have hmod := Nat.mod_lt (2 ^ r / 3 ^ K) (by omega : (0 : Nat) < 3)
  omega

/-! ## Three-level compatibility

The core idea: for a digit-2-free 2^r, three consecutive carry values
are linked by the digit constraints:

  C_K % 9 = d_K + 3 * d_{K+1}   where d_K, d_{K+1} ∈ {0, 1}

This forces C_K % 9 ∈ {0, 1, 3, 4}.  More generally, C_K % 3^m must
have all base-3 digits in {0, 1}.

The lifting state links consecutive levels:
  s_{K+1} = s_K + q_K * uK K

so the digit at K+1 depends on the choice at K.
Three consecutive levels create a system of congruences on r. -/

theorem carry_mod9_digits (r K : Nat) (hc : memCantorNat (2 ^ r)) :
    carry r K % 9 = carry r K % 3 + 3 * (carry r (K + 1) % 3) := by
  have h := carry_decomp r K
  have h9 := Nat.mod_lt (carry r K) (by omega : (0 : Nat) < 9)
  have h3 := Nat.mod_lt (carry r K) (by omega : (0 : Nat) < 3)
  have h3' := Nat.mod_lt (carry r (K + 1)) (by omega : (0 : Nat) < 3)
  omega

theorem digit2_free_mod9_le4 (r K : Nat) (hc : memCantorNat (2 ^ r)) :
    carry r K % 9 ≤ 4 := by
  have h1 := digit2_free_digit_le_one r hc K
  have h2 := digit2_free_digit_le_one r hc (K + 1)
  have hmod := carry_mod9_digits r K hc
  omega

theorem digit2_free_mod9_values (r K : Nat) (hc : memCantorNat (2 ^ r)) :
    carry r K % 9 = 0 ∨ carry r K % 9 = 1 ∨ carry r K % 9 = 3 ∨ carry r K % 9 = 4 := by
  have hd0 := digit2_free_digit_le_one r hc K
  have hd1 := digit2_free_digit_le_one r hc (K + 1)
  have hmod := carry_mod9_digits r K hc
  have h9 := Nat.mod_lt (carry r K) (by omega : (0 : Nat) < 9)
  have h3a := Nat.mod_lt (carry r K) (by omega : (0 : Nat) < 3)
  have h3b := Nat.mod_lt (carry r (K + 1)) (by omega : (0 : Nat) < 3)
  omega

/-! ## Mod 27: three consecutive digits encoded in the carry

C_K % 27 = d_K + 3*d_{K+1} + 9*d_{K+2}

For digit-2-free: d_i ∈ {0,1}, so C_K % 27 ∈ {0,1,3,4,9,10,12,13}.
Only 8 of 27 residues allowed — a genuine congruence constraint. -/

private lemma carry_div3 (r K : Nat) : carry r K / 3 = carry r (K + 1) := by
  have h := carry_decomp r K
  rw [h]
  omega

private lemma carry_div9 (r K : Nat) : carry r K / 9 = carry r (K + 2) := by
  rw [show (9 : Nat) = 3 * 3 from by norm_num]
  rw [← Nat.div_div_eq_div_mul]
  rw [carry_div3, carry_div3]

private lemma mod27_eq (n : Nat) : n % 27 = n % 9 + 9 * (n / 9 % 3) := by
  omega

theorem carry_mod27_digits (r K : Nat) (hc : memCantorNat (2 ^ r)) :
    carry r K % 27 =
      carry r K % 3 + 3 * (carry r (K + 1) % 3) + 9 * (carry r (K + 2) % 3) := by
  rw [mod27_eq, carry_mod9_digits r K hc, carry_div9]

theorem digit2_free_mod27_le13 (r K : Nat) (hc : memCantorNat (2 ^ r)) :
    carry r K % 27 ≤ 13 := by
  have h1 := digit2_free_digit_le_one r hc K
  have h2 := digit2_free_digit_le_one r hc (K + 1)
  have h3 := digit2_free_digit_le_one r hc (K + 2)
  have hmod := carry_mod27_digits r K hc
  omega

theorem digit2_free_mod27_values (r K : Nat) (hc : memCantorNat (2 ^ r)) :
    carry r K % 27 = 0 ∨ carry r K % 27 = 1 ∨ carry r K % 27 = 3 ∨
    carry r K % 27 = 4 ∨ carry r K % 27 = 9 ∨ carry r K % 27 = 10 ∨
    carry r K % 27 = 12 ∨ carry r K % 27 = 13 := by
  have h1 := digit2_free_digit_le_one r hc K
  have h2 := digit2_free_digit_le_one r hc (K + 1)
  have h3 := digit2_free_digit_le_one r hc (K + 2)
  have hmod := carry_mod27_digits r K hc
  have h27 := Nat.mod_lt (carry r K) (by omega : (0 : Nat) < 27)
  omega

/-! ## Lift state linking

At level K: r = s_K + q_K * uK K (s_K < uK K)
At level K+1: r = s_{K+1} + q_{K+1} * uK(K+1) (s_{K+1} < uK(K+1))

Since uK(K+1) = 3*uK K and s_K + q_K*uK K < 3*uK K (when q_K ≤ 2):
  s_{K+1} = s_K + q_K * uK K

This means the lifting state at K+1 is determined by the state at K
and the choice q_K. The digit at K+1 depends on the digit at K. -/

private lemma uK_succ (K : Nat) (hK : K ≥ 1) : uK (K + 1) = 3 * uK K := by
  unfold uK
  have : K + 1 - 1 = K := by omega
  rw [this]
  calc 2 * 3 ^ K
    _ = 2 * (3 ^ (K - 1) * 3) := by
      congr 1
      rw [← Nat.pow_succ]
      congr 1
      omega
    _ = 3 * (2 * 3 ^ (K - 1)) := by ring

theorem lift_step (r K : Nat) (hK : K ≥ 1)
    (s q : Nat) (hs : s < uK K) (hq : q ≤ 2) (hr : r = s + q * uK K) :
    let s' := r % uK (K + 1)
    s' = s + q * uK K := by
  have huK1 := uK_succ K hK
  subst hr
  rw [huK1]
  apply Nat.mod_eq_of_lt
  have hlt : s + q * uK K < 3 * uK K := by
    have hq2 := Nat.mul_le_mul_right (uK K) hq
    omega
  exact hlt

/-!
The key structural fact: for a digit-2-free 2^r, the carry sequence
satisfies C_K = 3*C_{K+1} + d_K with d_K ∈ {0, 1}.

This means C_{K+1} = (C_K - d_K) / 3, so the carry shrinks by roughly
a factor of 3 at each step (minus a small digit 0 or 1).

The lifting structure determines d_K via the formula:
  d_K = kthDigit(K, s, q) where r = s + q*u_K

For a fixed r, as K grows, the lifting decomposition r = s_K + q_K*u_K
changes (since u_K grows). The sequence of q_K values is uniquely
determined by r.

A counterexample would be a sequence q_0, q_1, q_2, ... such that
the resulting d_K values are all in {0, 1} AND the carry terminates.

The constraint is: the carry C_K = floor(2^r / 3^K) must satisfy
C_K = 3*C_{K+1} + d_K with d_K = kthDigit(K, s_K, q_K).

This is a genuine arithmetic constraint linking the lifting choices
to the carry dynamics. It is not automatically satisfiable.
-/

end ErdosTernary.CarryAnalysis
