/-
  Block1Invariant.lean — Block-1 digit invariant for the Erdos ternary conjecture.
  This file contains NO sorry, NO admit, NO axioms.
-/
import Mathlib.Tactic
import ErdosTernary.BridgeCompute
import ErdosTernary.Narkiewicz

open ErdosTernary.BridgeCompute
open Narkiewicz

namespace ErdosTernary.Block1Invariant

def P : Nat := 162 * 59049
theorem P_pos : 0 < P := by unfold P; norm_num
theorem three_pow_15_pos : 0 < 3 ^ 15 := Nat.pow_pos (by norm_num)

theorem P_eq : P = 2 * 3 ^ 14 := by unfold P; norm_num

private theorem coprime_2_3_30 : Nat.Coprime 2 (3 ^ 30) :=
  Nat.Coprime.pow_right 30 (by decide : Nat.Coprime 2 3)

private theorem totient_3_30 : Nat.totient (3 ^ 30) = P * 3 ^ 15 := by
  rw [Nat.totient_prime_pow (by decide : Nat.Prime 3) (by omega : 0 < 30)]
  show 3 ^ (30 - 1) * (3 - 1) = P * 3 ^ 15
  rw [P_eq]; norm_num

private theorem pow2_P_pow_3_15_mod_3_30 :
    (2 ^ P) ^ (3 ^ 15) % 3 ^ 30 = 1 := by
  have hmod := Nat.ModEq.pow_totient coprime_2_3_30
  have key : (2 ^ P) ^ (3 ^ 15) = 2 ^ (Nat.totient (3 ^ 30)) := by
    rw [totient_3_30, P_eq]; norm_num
  rw [key] at hmod
  exact_mod_cast hmod

private theorem pow_eq_one_mod (a d n : Nat) (hn : 1 < n) (ha : a % n = 1) :
    a ^ d % n = 1 := by
  induction d with
  | zero => simp [Nat.mod_eq_of_lt hn]
  | succ d ih =>
    rw [Nat.pow_succ, Nat.mul_mod, ih, ha, Nat.one_mul]
    exact Nat.mod_eq_of_lt hn

private theorem pow2_P_pow_mod_periodic (m r : Nat) (hmr : m % 3 ^ 15 = r % 3 ^ 15) :
    (2 ^ P) ^ m % 3 ^ 30 = (2 ^ P) ^ r % 3 ^ 30 := by
  wlog hle : r <= m generalizing m r
  · have h := this (by omega : m % 3 ^ 15 = r % 3 ^ 15)
    omega
  have h30_pos : 1 < 3 ^ 30 := by norm_num
  obtain ⟨d, hd⟩ := Nat.dvd_of_mod_eq_zero (by omega : (m - r) % 3 ^ 15 = 0)
  have hd' : m - r = 3 ^ 15 * d := by omega
  rw [show m = r + (m - r) from by omega, hd',
      show 3 ^ 15 * d = d * 3 ^ 15 from by ring,
      Nat.pow_add, show (2 ^ P) ^ (d * 3 ^ 15) = ((2 ^ P) ^ (3 ^ 15)) ^ d from by
        rw [show d * 3 ^ 15 = 3 ^ 15 * d from by ring]; rw [Nat.pow_mul],
      Nat.mul_mod, pow_eq_one_mod _ _ _ h30_pos pow2_P_pow_3_15_mod_3_30, Nat.mul_one]

theorem lift_mod_P (m r s : Nat)
    (hmr : m % 3 ^ 15 = r % 3 ^ 15) :
    2 ^ (s + P * m) % 3 ^ 30 = 2 ^ (s + P * r) % 3 ^ 30 := by
  have key : forall k : Nat, 2 ^ (s + P * k) % 3 ^ 30 =
      (2 ^ s % 3 ^ 30) * ((2 ^ P) ^ k % 3 ^ 30) % 3 ^ 30 := by
    intro k
    have h : 2 ^ (s + P * k) = 2 ^ s * (2 ^ P) ^ k := by rw [Nat.pow_add, Nat.pow_mul]
    rw [h]; exact Nat.mul_mod _ _ _
  rw [key m, key r, pow2_P_pow_mod_periodic m r hmr]

theorem digit_transfer (s m r t : Nat)
    (hmr : m % 3 ^ 15 = r % 3 ^ 15)
    (ht : t < 15) :
    (2 ^ (s + P * m) / 3 ^ (15 + t)) % 3 =
    (2 ^ (s + P * r) / 3 ^ (15 + t)) % 3 := by
  have h30 : 15 + t + 1 <= 30 := by omega
  have hdigit := digit_eq_of_modPow (2 ^ (s + P * m)) (15 + t) 30 h30
  have hdigit' := digit_eq_of_modPow (2 ^ (s + P * r)) (15 + t) 30 h30
  rw [show (2 ^ (s + P * m) / 3 ^ (15 + t)) % 3 =
      (2 ^ (s + P * m) % 3 ^ 30 / 3 ^ (15 + t)) % 3 from by rw [hdigit],
      show (2 ^ (s + P * r) / 3 ^ (15 + t)) % 3 =
      (2 ^ (s + P * r) % 3 ^ 30 / 3 ^ (15 + t)) % 3 from by rw [hdigit'],
      lift_mod_P m r s hmr]

def isBlock1Caught (s : Nat) (r : Nat) : Prop :=
    0 < r /\ r < 3 ^ 15 /\ exists j, 15 <= j /\ j < 30 /\ (2 ^ (s + P * r) / 3 ^ j) % 3 = 2

def isBlock1Exceptional (s : Nat) (r : Nat) : Prop :=
    0 < r /\ r < 3 ^ 15 /\ forall j, 15 <= j -> j < 30 -> (2 ^ (s + P * r) / 3 ^ j) % 3 != 2

theorem caught_transfer (s m r : Nat)
    (hmr : m % 3 ^ 15 = r % 3 ^ 15)
    (hcaught : isBlock1Caught s r) :
    isBlock1Caught s (m % 3 ^ 15) := by
  obtain ⟨r_pos, r_lt, j, hj15, hj30, hj2⟩ := hcaught
  have hpos : 0 < m % 3 ^ 15 := by
    rw [Nat.mod_eq_of_lt (by omega : r < 3 ^ 15)] at hmr
    omega
  have hlt : m % 3 ^ 15 < 3 ^ 15 := Nat.mod_lt _ three_pow_15_pos
  refine ⟨hpos, hlt, j, hj15, hj30, ?_⟩
  have hmr' : (m % 3 ^ 15) % 3 ^ 15 = r % 3 ^ 15 := by
    rw [Nat.mod_eq_of_lt (Nat.mod_lt _ three_pow_15_pos)]
    exact hmr
  have hdt := digit_transfer s (m % 3 ^ 15) r (j - 15) hmr' (by omega)
  simp only [show 15 + (j - 15) = j from by omega] at hdt
  omega

theorem large_r_has_digit2_of_caught (r m s : Nat)
    (hr : r = s + P * m)
    (hcaught : isBlock1Caught s (m % 3 ^ 15)) :
    exists j, 15 <= j /\ j < 30 /\ (2 ^ r / 3 ^ j) % 3 = 2 := by
  obtain ⟨_, _, j, hj15, hj30, hj2⟩ := hcaught
  refine ⟨j, hj15, hj30, ?_⟩
  have hle15 : j - 15 < 15 := by omega
  have hmod_self : m % 3 ^ 15 = (m % 3 ^ 15) % 3 ^ 15 :=
    (Nat.mod_eq_of_lt (Nat.mod_lt _ three_pow_15_pos)).symm
  rw [hr]
  conv_lhs => rw [show j = 15 + (j - 15) from by omega]
  rw [digit_transfer s m (m % 3 ^ 15) (j - 15) hmod_self hle15]
  rw [show 15 + (j - 15) = j from by omega]
  exact hj2

end ErdosTernary.Block1Invariant
