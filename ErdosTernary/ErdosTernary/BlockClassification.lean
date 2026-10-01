/-
  BlockClassification.lean — Block classification for the Erdős ternary conjecture.

  Proves: the order of 2^P mod 3^30 is exactly 3^15 (via cubing chain + Euler),
  establishing injectivity of the residue map and the block-1 counting bound.

  This file contains NO sorry, NO admit, NO axioms.
-/
import Mathlib.Tactic
import Mathlib.Data.Int.GCD
import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import ErdosTernary.BridgeCompute
import ErdosTernary.Narkiewicz

open ErdosTernary.BridgeCompute
open Narkiewicz

namespace ErdosTernary.BlockClassification

def P : Nat := 2 * 3 ^ 14
theorem P_pos : 0 < P := by unfold P; norm_num

/-- 2^P mod 3^30, as a literal Nat (avoids kernel WF-recursion blowup in native_decide). -/
def pow2Pmod30 : Nat := 82792762922791
theorem pow2Pmod30_eq : pow2Pmod30 = 2 ^ P % 3 ^ 30 := by
  rw [← pow2Mod_eq]; native_decide

/-- 2^P mod 3^45 and 2^P mod 3^60, as literal Nats. -/
def pow2Pmod45 : Nat := 1374779850164398834624
def pow2Pmod60 : Nat := 14907740997429772786119085066

theorem pow2Pmod45_eq : pow2Pmod45 = 2 ^ P % 3 ^ 45 := by
  rw [← pow2Mod_eq]; native_decide
theorem pow2Pmod60_eq : pow2Pmod60 = 2 ^ P % 3 ^ 60 := by
  rw [← pow2Mod_eq]; native_decide

/-- Local copy of pow2ModAux correctness (private in BridgeCompute). -/
private theorem pow2ModAux_eq' (n b md : Nat) :
    pow2ModAux n b md = b ^ n % md := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    unfold pow2ModAux
    split
    · next h_eq => simp [beq_iff_eq] at h_eq; subst h_eq; simp [Nat.pow_zero]
    · next h_neq =>
      simp only [beq_iff_eq] at h_neq
      split
      · next h_even =>
        simp only [beq_iff_eq] at h_even
        have h_div : n / 2 < n := Nat.div_lt_self (by omega) (by norm_num)
        rw [ih (n / 2) h_div]
        rw [← Nat.mul_mod, ← Nat.pow_two, ← Nat.pow_mul]
        rw [Nat.div_mul_cancel (by omega : 2 ∣ n)]
      · next h_odd =>
        simp only [beq_iff_eq] at h_odd
        have h_sub : n - 1 < n := by omega
        rw [ih (n - 1) h_sub]
        rw [Nat.mul_mod_mod, Nat.mul_comm b (b ^ (n - 1)), ← Nat.pow_succ]
        have h_eq : (n - 1).succ = n := by omega
        rw [h_eq]

/-! ## Part 1: Cubing chain proving (2^P)^(3^14) ≢ 1 and (2^P)^(3^15) ≡ 1 mod 3^30 -/

private theorem v0 : 2 ^ P % 3 ^ 30 = 82792762922791 := by
  rw [← pow2Mod_eq]; native_decide
private theorem v1 : (82792762922791 : Nat) ^ 3 % 3 ^ 30 = 42487156673722 := by norm_num
private theorem v2 : (42487156673722 : Nat) ^ 3 % 3 ^ 30 = 127461470021164 := by norm_num
private theorem v3 : (127461470021164 : Nat) ^ 3 % 3 ^ 30 = 176493277968841 := by norm_num
private theorem v4 : (176493277968841 : Nat) ^ 3 % 3 ^ 30 = 117697569717223 := by norm_num
private theorem v5 : (117697569717223 : Nat) ^ 3 % 3 ^ 30 = 147201577057018 := by norm_num
private theorem v6 : (147201577057018 : Nat) ^ 3 % 3 ^ 30 = 29822466981754 := by norm_num
private theorem v7 : (29822466981754 : Nat) ^ 3 % 3 ^ 30 = 89467400945260 := by norm_num
private theorem v8 : (89467400945260 : Nat) ^ 3 % 3 ^ 30 = 62511070741129 := by norm_num
private theorem v9 : (62511070741129 : Nat) ^ 3 % 3 ^ 30 = 187533212223385 := by norm_num
private theorem v10 : (187533212223385 : Nat) ^ 3 % 3 ^ 30 = 150817372480855 := by norm_num
private theorem v11 : (150817372480855 : Nat) ^ 3 % 3 ^ 30 = 40669853253265 := by norm_num
private theorem v12 : (40669853253265 : Nat) ^ 3 % 3 ^ 30 = 122009559759793 := by norm_num
private theorem v13 : (122009559759793 : Nat) ^ 3 % 3 ^ 30 = 160137547184728 := by norm_num
private theorem v14 : (160137547184728 : Nat) ^ 3 % 3 ^ 30 = 68630377364884 := by norm_num

/-! Euler's theorem: (2^P)^(3^15) ≡ 1 mod 3^30 -/

private theorem coprime_2_3_30 : Nat.Coprime 2 (3 ^ 30) :=
  Nat.Coprime.pow_right 30 (by decide : Nat.Coprime 2 3)

private theorem totient_3_30 : Nat.totient (3 ^ 30) = P * 3 ^ 15 := by
  rw [Nat.totient_prime_pow (by decide : Nat.Prime 3) (by omega : 0 < 30)]
  show 3 ^ (30 - 1) * (3 - 1) = P * 3 ^ 15
  rw [show P = 2 * 3 ^ 14 from rfl]; norm_num

private theorem euler_result : (2 ^ P) ^ (3 ^ 15) % 3 ^ 30 = 1 := by
  have h := Nat.ModEq.pow_totient coprime_2_3_30
  rw [totient_3_30] at h
  have key := pow_mul 2 P (3 ^ 15)
  rw [key] at h
  have h2 : 1 % 3 ^ 30 = 1 := by norm_num
  rw [← h2]
  exact h

/-! The cubing chain: (2^P)^(3^k) mod 3^30 = v_k for k = 0..14 -/

/-- Bridge: (2^P)^e % 3^30 via pow2ModAux (term-level composition; avoids
    rw patterns with 2^P that trigger instance-reconciliation blowup). -/
private theorem pow_chain30 (k V : Nat)
    (h3 : pow2ModAux (3 ^ k) pow2Pmod30 (3 ^ 30) = V) :
    (2 ^ P) ^ (3 ^ k) % 3 ^ 30 = V := by
  have h1 : (2 ^ P) ^ (3 ^ k) % 3 ^ 30 = ((2 ^ P) % 3 ^ 30) ^ (3 ^ k) % 3 ^ 30 := Nat.pow_mod ..
  have h1b : ((2 ^ P) % 3 ^ 30) ^ (3 ^ k) % 3 ^ 30 = pow2Pmod30 ^ (3 ^ k) % 3 ^ 30 := by
    rw [← pow2Pmod30_eq]
  have h2 : pow2Pmod30 ^ (3 ^ k) % 3 ^ 30 = pow2ModAux (3 ^ k) pow2Pmod30 (3 ^ 30) :=
    (pow2ModAux_eq' (3 ^ k) pow2Pmod30 (3 ^ 30)).symm
  exact h1.trans (h1b.trans (h2.trans h3))

private theorem pow_P_3_0 : (2 ^ P) ^ (3 ^ 0) % 3 ^ 30 = 82792762922791 :=
  pow_chain30 0 82792762922791 (by native_decide)
private theorem pow_P_3_1 : (2 ^ P) ^ (3 ^ 1) % 3 ^ 30 = 42487156673722 :=
  pow_chain30 1 42487156673722 (by native_decide)
private theorem pow_P_3_2 : (2 ^ P) ^ (3 ^ 2) % 3 ^ 30 = 127461470021164 :=
  pow_chain30 2 127461470021164 (by native_decide)
private theorem pow_P_3_3 : (2 ^ P) ^ (3 ^ 3) % 3 ^ 30 = 176493277968841 :=
  pow_chain30 3 176493277968841 (by native_decide)
private theorem pow_P_3_4 : (2 ^ P) ^ (3 ^ 4) % 3 ^ 30 = 117697569717223 :=
  pow_chain30 4 117697569717223 (by native_decide)
private theorem pow_P_3_5 : (2 ^ P) ^ (3 ^ 5) % 3 ^ 30 = 147201577057018 :=
  pow_chain30 5 147201577057018 (by native_decide)
private theorem pow_P_3_6 : (2 ^ P) ^ (3 ^ 6) % 3 ^ 30 = 29822466981754 :=
  pow_chain30 6 29822466981754 (by native_decide)
private theorem pow_P_3_7 : (2 ^ P) ^ (3 ^ 7) % 3 ^ 30 = 89467400945260 :=
  pow_chain30 7 89467400945260 (by native_decide)
private theorem pow_P_3_8 : (2 ^ P) ^ (3 ^ 8) % 3 ^ 30 = 62511070741129 :=
  pow_chain30 8 62511070741129 (by native_decide)
private theorem pow_P_3_9 : (2 ^ P) ^ (3 ^ 9) % 3 ^ 30 = 187533212223385 :=
  pow_chain30 9 187533212223385 (by native_decide)
private theorem pow_P_3_10 : (2 ^ P) ^ (3 ^ 10) % 3 ^ 30 = 150817372480855 :=
  pow_chain30 10 150817372480855 (by native_decide)
private theorem pow_P_3_11 : (2 ^ P) ^ (3 ^ 11) % 3 ^ 30 = 40669853253265 :=
  pow_chain30 11 40669853253265 (by native_decide)
private theorem pow_P_3_12 : (2 ^ P) ^ (3 ^ 12) % 3 ^ 30 = 122009559759793 :=
  pow_chain30 12 122009559759793 (by native_decide)
private theorem pow_P_3_13 : (2 ^ P) ^ (3 ^ 13) % 3 ^ 30 = 160137547184728 :=
  pow_chain30 13 160137547184728 (by native_decide)
private theorem pow_P_3_14 : (2 ^ P) ^ (3 ^ 14) % 3 ^ 30 = 68630377364884 :=
  pow_chain30 14 68630377364884 (by native_decide)

private theorem pow_P_3_14_ne_1 : (2 ^ P) ^ (3 ^ 14) % 3 ^ 30 ≠ 1 := by
  rw [pow_P_3_14]; norm_num

/-! ## Part 2: Order divisibility via Mathlib's pow_gcd_eq_one -/

-- REMOVED (false + unused): `coprime_2_P : Nat.Coprime 2 (2 ^ P)`
-- is mathematically FALSE (gcd(2, 2^P) = 2 for P >= 1) and was never
-- referenced. Reported per audit rules instead of silently kept.

private theorem euler_mod (d : Nat) (hd : d = 3 ^ 15) :
    (2 ^ P) ^ d % 3 ^ 30 = 1 := by rw [hd]; exact euler_result

private theorem pow_P_3_14_mod : (2 ^ P) ^ (3 ^ 14) % 3 ^ 30 ≠ 1 := pow_P_3_14_ne_1

/-! Key lemma: if (2^P)^a ≡ 1 and (2^P)^b ≡ 1 mod 3^30,
    then (2^P)^(gcd a b) ≡ 1 mod 3^30.
    We prove this by lifting to ZMod (3^30) and using Mathlib's pow_gcd_eq_one. -/

private theorem cast_natCast_pow_mod_eq_zero {m : Nat} (hm : 0 < m) {a : Nat}
    (h : a % m = 0) : (a : ZMod m) = 0 := by
  rw [ZMod.natCast_zmod_eq_zero_iff_dvd]; omega

-- REMOVED (superseded by the LTE proof below): `mod_eq_one_iff_cast` and
-- `pow_gcd_mod30` (ZMod-cast bridge). Applying cast-iff lemmas against
-- file-elaborated hypotheses triggered isDefEq fallbacks that whnf'd 2^P
-- (maxRecDepth/OOM). The order-divisibility result is now proved cast-free
-- via padicValNat + LTE; research history preserved in git.

private theorem coprime_2_3_15 : Nat.Coprime 2 (3 ^ 15) :=
  Nat.Coprime.pow_right 15 (by decide : Nat.Coprime 2 3)

private theorem totient_3_15 : Nat.totient (3 ^ 15) = P := by
  rw [Nat.totient_prime_pow (by decide : Nat.Prime 3) (by omega : 0 < 15)]
  show 3 ^ (15 - 1) * (3 - 1) = P
  rw [show P = 2 * 3 ^ 14 from rfl]; norm_num

private theorem two_pow_P_mod_3_15_eq_1 : 2 ^ P % 3 ^ 15 = 1 := by
  have h := Nat.ModEq.pow_totient coprime_2_3_15
  rw [totient_3_15] at h
  have h2 : 2 ^ P % 3 ^ 15 = 1 % 3 ^ 15 := h
  rwa [Nat.mod_eq_of_lt (by norm_num : 1 < 3 ^ 15)] at h2

/-! The order of 2^P mod 3^30 is 3^15.
    Since (2^P)^(3^15) ≡ 1 and (2^P)^(3^14) ≢ 1, the only divisor of 3^15
    that can be the order is 3^15 itself. -/

private theorem pow_eq_one_implies_order_dvd (d : Nat) (hd : 0 < d) :
    (2 ^ P) ^ d % 3 ^ 30 = 1 → 3 ^ 15 ∣ d := by
  intro h
  -- Cast-free proof via LTE (Lifting The Exponent) on padicValNat.
  -- v_3((2^P)^d - 1) = v_3(2^P - 1) + v_3(d) = 15 + v_3(d),
  -- and (2^P)^d ≡ 1 (mod 3^30) iff v_3((2^P)^d - 1) ≥ 30 iff v_3(d) ≥ 15
  -- iff 3^15 ∣ d.
  haveI hFact3 : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have h1le : 1 ≤ 2 ^ P := Nat.succ_le_of_lt (Nat.pow_pos (n := P) (by norm_num : 0 < 2))
  have hP1 : 1 ≤ P := by unfold P; norm_num
  have h2P : 2 ≤ 2 ^ P := by
    rw [show P = (P - 1) + 1 from by omega, Nat.pow_succ]
    have hp1 : 1 ≤ 2 ^ (P - 1) := Nat.succ_le_of_lt (Nat.pow_pos (n := P - 1) (by norm_num : 0 < 2))
    omega
  have hpow16 : 2 ^ P % 3 ^ 16 = 14348908 := by rw [← pow2Mod_eq]; native_decide
  have h1d : 1 ≤ (2 ^ P) ^ d := Nat.succ_le_of_lt (Nat.pow_pos (n := d) (Nat.pow_pos (n := P) (by norm_num : 0 < 2)))
  have h2d : 2 ≤ (2 ^ P) ^ d := by
    have h1 : (2 ^ P) ^ 1 ≤ (2 ^ P) ^ d := pow_le_pow_right' h1le (Nat.succ_le_of_lt hd)
    rw [Nat.pow_one] at h1
    exact le_trans h2P h1
  have ha_pos : 0 < (2 ^ P) ^ d - 1 :=
    Nat.sub_pos_of_lt (lt_of_lt_of_le (by norm_num : (1:ℕ) < 2) h2d)
  have ha_ne : (2 ^ P) ^ d - 1 ≠ 0 := ne_of_gt ha_pos
  have hb_pos : 0 < 2 ^ P - 1 := Nat.sub_pos_of_lt (lt_of_lt_of_le (by norm_num : (1:ℕ) < 2) h2P)
  have hne : 2 ^ P - 1 ≠ 0 := ne_of_gt hb_pos
  -- A: h -> 3^30 ∣ (2^P)^d - 1
  have hme : (1 : Nat) ≡ (2 ^ P) ^ d [MOD 3 ^ 30] := by
    show (1 : Nat) % 3 ^ 30 = (2 ^ P) ^ d % 3 ^ 30
    rw [show (1 : Nat) % 3 ^ 30 = 1 from by norm_num]
    exact h.symm
  have hdiv : 3 ^ 30 ∣ (2 ^ P) ^ d - 1 := (Nat.modEq_iff_dvd' h1d).mp hme
  -- B: v3(2^P - 1) = 15
  have hpow15 : 2 ^ P % 3 ^ 15 = 1 := two_pow_P_mod_3_15_eq_1
  have hme15 : (1 : Nat) ≡ 2 ^ P [MOD 3 ^ 15] := by
    show (1 : Nat) % 3 ^ 15 = 2 ^ P % 3 ^ 15
    rw [show (1 : Nat) % 3 ^ 15 = 1 from by norm_num]
    exact hpow15.symm
  have hdvd15 : 3 ^ 15 ∣ 2 ^ P - 1 := (Nat.modEq_iff_dvd' h1le).mp hme15
  have hnot16 : ¬3 ^ 16 ∣ 2 ^ P - 1 := by
    intro hdiv16
    have hme16 : (1 : Nat) ≡ 2 ^ P [MOD 3 ^ 16] := (Nat.modEq_iff_dvd' h1le).mpr hdiv16
    have h16eq : 1 % 3 ^ 16 = 2 ^ P % 3 ^ 16 := hme16
    rw [show (1 : Nat) % 3 ^ 16 = 1 from by norm_num] at h16eq
    rw [← h16eq] at hpow16
    omega
  have h15 : 15 ≤ padicValNat 3 (2 ^ P - 1) :=
    (padicValNat_dvd_iff_le (p := 3) hne).mp hdvd15
  have h16 : ¬16 ≤ padicValNat 3 (2 ^ P - 1) := by
    intro hle
    exact hnot16 ((padicValNat_dvd_iff_le (p := 3) hne).mpr hle)
  have hpvB : padicValNat 3 (2 ^ P - 1) = 15 := by
    rcases Nat.lt_or_ge (padicValNat 3 (2 ^ P - 1)) 15 with hlt | hge
    · exact absurd hlt (not_lt.mpr h15)
    · have hlt16 : padicValNat 3 (2 ^ P - 1) < 16 := not_le.mp h16
      have hle15 : padicValNat 3 (2 ^ P - 1) ≤ 15 := Nat.le_of_lt_succ hlt16
      exact Nat.le_antisymm hle15 hge
  -- C: LTE
  have h3 : 2 ^ P % 3 = 1 := by
    have h31 := Nat.mod_mod_of_dvd (2 ^ P) (by norm_num : 3 ∣ 3 ^ 15)
    rw [hpow15] at h31
    rw [show (1 : Nat) % 3 = 1 from by norm_num] at h31
    exact h31.symm
  have hme3 : (1 : Nat) ≡ 2 ^ P [MOD 3] := by
    show (1 : Nat) % 3 = 2 ^ P % 3
    rw [show (1 : Nat) %  3 = 1 from by norm_num]
    exact h3.symm
  have hdvd3 : 3 ∣ 2 ^ P - 1 := (Nat.modEq_iff_dvd' h1le).mp hme3
  have hnot3 : ¬3 ∣ 2 ^ P := by
    intro h
    rw [Nat.dvd_iff_mod_eq_zero] at h
    rw [h3] at h
    omega
  have hodd3 : Odd 3 := ⟨1, by norm_num⟩
  have hmul := multiplicity.Nat.pow_sub_pow (p := 3) (hp := by norm_num) (hp1 := hodd3) hdvd3 hnot3 d
  rw [Nat.one_pow] at hmul
  have hpv_a := padicValNat_def' (by norm_num : 3 ≠ 1) ha_pos
  have hpv_b := padicValNat_def' (by norm_num : 3 ≠ 1) hb_pos
  have hpv_d := padicValNat_def' (by norm_num : 3 ≠ 1) hd
  rw [← hpv_a, ← hpv_b, ← hpv_d] at hmul
  push_cast at hmul
  have hsum : padicValNat 3 ((2 ^ P) ^ d - 1) = padicValNat 3 (2 ^ P - 1) + padicValNat 3 d := by
    exact_mod_cast hmul
  rw [hpvB] at hsum
  -- D: conclusion
  clear h15 h16 hnot16 hdvd15 hme15 hne hpv_b hpvB
  have h30 : 30 ≤ padicValNat 3 ((2 ^ P) ^ d - 1) :=
    (padicValNat_dvd_iff_le (p := 3) ha_ne).mp hdiv
  rw [hsum] at h30
  have hge : 15 ≤ padicValNat 3 d := by omega
  exact (padicValNat_dvd_iff_le (p := 3) (Nat.pos_iff_ne_zero.mp hd)).mpr hge

/-! ## Part 3: Injectivity of the full residue map -/

/-- Helper: equality of residues at r₁ ≤ r₂ implies (2^P)^(r₂-r₁) ≡ 1 (mod 3^30).
    Derived via ModEq arithmetic + LTE-free prime-power divisibility
    (Prime.pow_dvd_of_dvd_mul_left), avoiding coprime-mod cast issues. -/
private theorem hdiff_aux (s r₁ r₂ : Nat) (hle : r₁ ≤ r₂)
    (h : 2 ^ (s + P * r₁) % 3 ^ 30 = 2 ^ (s + P * r₂) % 3 ^ 30) :
    (2 ^ P) ^ (r₂ - r₁) % 3 ^ 30 = 1 := by
  have h2 : s + P * r₂ = s + P * r₁ + P * (r₂ - r₁) := by
    conv_lhs => rw [(Nat.add_sub_of_le hle).symm]
    ring
  have hmeq : (2 ^ (s + P * r₂)) ≡ (2 ^ (s + P * r₁)) [MOD 3 ^ 30] := by
    show 2 ^ (s + P * r₂) % 3 ^ 30 = 2 ^ (s + P * r₁) % 3 ^ 30
    exact h.symm
  rw [h2, Nat.pow_add] at hmeq
  have hle' : 2 ^ (s + P * r₁) ≤ 2 ^ (s + P * r₁) * 2 ^ (P * (r₂ - r₁)) :=
    Nat.le_mul_of_pos_right _ (Nat.pow_pos (n := P * (r₂ - r₁)) (by norm_num : 0 < 2))
  have hdvd : 3 ^ 30 ∣ 2 ^ (s + P * r₁) * 2 ^ (P * (r₂ - r₁)) - 2 ^ (s + P * r₁) :=
    (Nat.modEq_iff_dvd' hle').mp hmeq.symm
  have hident : 2 ^ (s + P * r₁) * 2 ^ (P * (r₂ - r₁)) - 2 ^ (s + P * r₁) =
      2 ^ (s + P * r₁) * (2 ^ (P * (r₂ - r₁)) - 1) :=
    (congrArg (fun z => 2 ^ (s + P * r₁) * 2 ^ (P * (r₂ - r₁)) - z)
      (Nat.mul_one (2 ^ (s + P * r₁))).symm).trans (Nat.mul_sub ..).symm
  rw [hident] at hdvd
  have hcop : Nat.Coprime (2 ^ (s + P * r₁)) 3 :=
    Nat.Coprime.pow_left (s + P * r₁) (by decide : Nat.Coprime 2 3)
  have hnot3X : ¬3 ∣ 2 ^ (s + P * r₁) := by
    intro h3
    have := Nat.eq_one_of_dvd_coprimes hcop h3 (dvd_refl 3)
    omega
  have hdivZ : 3 ^ 30 ∣ 2 ^ (P * (r₂ - r₁)) - 1 :=
    Prime.pow_dvd_of_dvd_mul_left (hp := Nat.prime_iff.mp (by decide : Nat.Prime 3)) 30 hnot3X hdvd
  obtain ⟨t, ht⟩ := hdivZ
  have hY1 : 1 ≤ 2 ^ (P * (r₂ - r₁)) :=
    Nat.succ_le_of_lt (Nat.pow_pos (n := P * (r₂ - r₁)) (by norm_num : 0 < 2))
  have hYeq : 2 ^ (P * (r₂ - r₁)) = 3 ^ 30 * t + 1 := by
    rw [← ht]
    exact (Nat.sub_add_cancel hY1).symm
  rw [show (2 ^ P) ^ (r₂ - r₁) = 2 ^ (P * (r₂ - r₁)) from (Nat.pow_mul 2 P (r₂ - r₁)).symm]
  rw [hYeq]
  omega

theorem full_injective (s r₁ r₂ : Nat)
    (h₁ : r₁ < 3 ^ 15) (h₂ : r₂ < 3 ^ 15) :
    2 ^ (s + P * r₁) % 3 ^ 30 = 2 ^ (s + P * r₂) % 3 ^ 30 → r₁ = r₂ := by
  intro h
  rcases Nat.le_total r₁ r₂ with hle | hle
  · have diff_le : r₂ - r₁ < 3 ^ 15 := Nat.sub_lt_left_of_lt_add hle (by omega)
    have hdiff := hdiff_aux s r₁ r₂ hle h
    by_contra hne
    have hd_pos : 0 < r₂ - r₁ := Nat.sub_pos_of_lt (by omega)
    have hdvd := pow_eq_one_implies_order_dvd (r₂ - r₁) hd_pos hdiff
    omega
  · have diff_le : r₁ - r₂ < 3 ^ 15 := Nat.sub_lt_left_of_lt_add hle (by omega)
    have hdiff := hdiff_aux s r₂ r₁ hle h.symm
    by_contra hne
    have hd_pos : 0 < r₁ - r₂ := Nat.sub_pos_of_lt (by omega)
    have hdvd := pow_eq_one_implies_order_dvd (r₁ - r₂) hd_pos hdiff
    omega

/-! ## Part 4: Block values and digit predicates -/

def block1Val (s r : Nat) : Nat := (2 ^ (s + P * r) % 3 ^ 30 / 3 ^ 15) % 3 ^ 15

theorem block1_val_lt (s r : Nat) : block1Val s r < 3 ^ 15 :=
  Nat.mod_lt _ (Nat.pow_pos (by omega : 0 < 3))

def noDigit2 (n : Nat) : Bool :=
  (List.range 15).all fun t => !decide ((n / 3 ^ t) % 3 = 2)

/-! ## Part 5: Block-1 counting bound

    Key fact: the set {n < 3^15 | noDigit2 n} has exactly 2^15 elements.
    Each of the 15 ternary digits must be 0 or 1 (not 2), giving 2 choices per digit.
    Combined with injectivity of the block-1 map, this bounds exceptions ≤ 2^15.
-/

/-- Injective map: if f is injective on [0,N) and maps into [0,N),
    then |{r < N | P(f r)}| ≤ |{n < N | P n}|. -/
theorem filter_preimage_le_of_injOn {N : Nat} {f : Nat → Nat}
    (hf : ∀ r₁ r₂, r₁ < N → r₂ < N → f r₁ = f r₂ → r₁ = r₂)
    (h_range : ∀ r, r < N → f r < N)
    (P : Nat → Prop) [DecidablePred P] :
    ((Finset.range N).filter fun r => P (f r)).card ≤
    ((Finset.range N).filter P).card := by
  have key :
      ((Finset.range N).filter fun r => P (f r)).image f ⊆
      (Finset.range N).filter P := by
    intro n hn
    simp [Finset.mem_image, Finset.mem_filter] at hn
    obtain ⟨r, hr, rfl⟩ := hn
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨h_range r hr.1, hr.2⟩
  have hcard : (((Finset.range N).filter fun r => P (f r)).image f).card =
      ((Finset.range N).filter fun r => P (f r)).card := by
    apply Finset.card_image_of_injOn
    intro r₁ hr₁ r₂ hr₂ hfeq
    simp [Finset.mem_filter, Finset.mem_range] at hr₁ hr₂
    exact hf r₁ r₂ hr₁.1 hr₂.1 hfeq
  rw [← hcard]; exact Finset.card_le_card key

/-- Subtracting 3^k does not change digits at positions t < k. -/
private theorem digit_below_k_eq {n k t : Nat} (hge : 3 ^ k ≤ n) (ht : t < k) :
    (n / 3 ^ t) % 3 = ((n - 3 ^ k) / 3 ^ t) % 3 := by
  have hnk : n = (n - 3 ^ k) + 3 ^ k :=
    (Nat.add_sub_of_le hge).symm.trans (by rw [Nat.add_comm])
  have hdvd : 3 ^ t ∣ 3 ^ k := by
    have h1 : k = t + (k - t) := by omega
    rw [h1]
    exact ⟨3 ^ (k - t), Nat.pow_add 3 t (k - t)⟩
  conv_lhs => rw [hnk]
  rw [Nat.add_div_of_dvd_left hdvd]
  have hdiv : 3 ^ k / 3 ^ t = 3 ^ (k - t) := by
    conv_lhs => rw [show k = t + (k - t) from by omega]
    rw [Nat.pow_add, Nat.mul_comm]
    exact Nat.mul_div_cancel (3 ^ (k - t)) (by omega : (0:Nat) < 3 ^ t)
  rw [hdiv]
  have hmod : 3 ^ (k - t) % 3 = 0 := by
    rw [show k - t = (k - t - 1) + 1 from by omega, Nat.pow_succ]
    exact Nat.mul_mod_left _ _
  rw [Nat.add_mod, hmod, Nat.add_zero]
  exact Nat.mod_eq_of_lt (Nat.mod_lt _ (by omega : (0:Nat) < 3))

/-- Digit-characterization helpers: for q = n / 3^k with q < 3, the residue
    q % 3 determines q exactly. Proved without omega (omega cannot handle
    division by the variable 3^k when it appears in context). -/
private theorem digit0_eq_zero {q : Nat} (hq3 : q < 3) (hd : q % 3 = 0) : q = 0 := by
  have h2 : q = 3 * (q / 3) + q % 3 := (Nat.div_add_mod q 3).symm
  rw [hd, Nat.add_zero] at h2
  have h1 : q / 3 < 1 := Nat.div_lt_of_lt_mul (by rw [Nat.mul_one]; exact hq3)
  have hqc : q / 3 = 0 := Nat.lt_one_iff.mp h1
  rw [h2, hqc, Nat.mul_zero]

private theorem digit1_eq_one {q : Nat} (hq3 : q < 3) (hd : q % 3 = 1) : q = 1 := by
  have h2 : q = 3 * (q / 3) + q % 3 := (Nat.div_add_mod q 3).symm
  rw [hd, Nat.add_zero] at h2
  have h1 : q / 3 < 1 := Nat.div_lt_of_lt_mul (by rw [Nat.mul_one]; exact hq3)
  have hqc : q / 3 = 0 := Nat.lt_one_iff.mp h1
  rw [h2, hqc, Nat.mul_zero, Nat.zero_add]

/-- Left half (n < 3^k) over range 3^{k+1} agrees with the k-digit filter over range 3^k. -/
private theorem filter_left_eq (k : Nat) :
    ((Finset.range (3 ^ (k + 1))).filter fun n =>
      n < 3 ^ k ∧ ∀ t, t < k → (n / 3 ^ t) % 3 ≠ 2) =
    ((Finset.range (3 ^ k)).filter fun n =>
      ∀ t, t < k → (n / 3 ^ t) % 3 ≠ 2) := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨_, hlt3, hall⟩
    exact ⟨hlt3, hall⟩
  · rintro ⟨hlt3, hall⟩
    have h23 : 3 ^ k * 1 ≤ 3 ^ k * 3 := Nat.mul_le_mul_left (3 ^ k) (by omega)
    rw [Nat.mul_one] at h23
    have hk : 3 ^ k ≤ 3 ^ (k + 1) := by rw [Nat.pow_succ]; exact h23
    exact ⟨Nat.lt_of_lt_of_le hlt3 hk, hlt3, hall⟩

/-- Digit-2-free counting: exactly 2^k values in [0, 3^k) have no digit 2
    in their k-digit ternary representation.
    Proof: induction on k. Each step doubles the count (MSB ∈ {0,1}). -/
private theorem d2f_card_aux :
    ∀ k, ((Finset.range (3 ^ k)).filter fun n =>
      ∀ t, t < k → (n / 3 ^ t) % 3 ≠ 2).card = 2 ^ k
  | 0 => by simp [Finset.range, List.range]
  | k + 1 => by
    -- Split the quantifier at t = k
    have hsplit : ∀ n, (∀ t, t < k + 1 → (n / 3 ^ t) % 3 ≠ 2) ↔
        (∀ t, t < k → (n / 3 ^ t) % 3 ≠ 2) ∧ ((n / 3 ^ k) % 3 ≠ 2) := by
      intro n
      constructor
      · intro h
        exact ⟨fun t ht => h t (by omega), h k (by omega)⟩
      · intro ⟨hall, hk⟩ t ht
        by_cases htk : t < k
        · exact hall t htk
        · have : t = k := by omega
          rw [this]; exact hk
    have hconv : (Finset.range (3 ^ (k + 1))).filter
        (fun n => ∀ t, t < k + 1 → (n / 3 ^ t) % 3 ≠ 2) =
        (Finset.range (3 ^ (k + 1))).filter
        (fun n => (∀ t, t < k → (n / 3 ^ t) % 3 ≠ 2) ∧ ((n / 3 ^ k) % 3 ≠ 2)) := by
      refine Finset.filter_congr ?_
      intro x _hx
      exact hsplit x
    rw [hconv]
    -- S_{k+1} = {n < 3^{k+1} | digit k ≠ 2 ∧ noDigit2 in lower k digits}
    -- Split by MSB: digit k = 0 or digit k = 1
    have hpart :
        ((Finset.range (3 ^ (k + 1))).filter fun n =>
            (∀ t, t < k → (n / 3 ^ t) % 3 ≠ 2) ∧
            (n / 3 ^ k) % 3 ≠ 2) =
        ((Finset.range (3 ^ (k + 1))).filter fun n =>
            n < 3 ^ k ∧ ∀ t, t < k → (n / 3 ^ t) % 3 ≠ 2) ∪
        ((Finset.range (3 ^ (k + 1))).filter fun n =>
            3 ^ k ≤ n ∧ n < 2 * 3 ^ k ∧
            ∀ t, t < k → ((n - 3 ^ k) / 3 ^ t) % 3 ≠ 2) := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union]
      constructor
      · rintro ⟨hlt, hall, hdne⟩
        -- Make digit and remainder variables so omega can reason about them
        set q := n / 3 ^ k with hq
        set r := n % 3 ^ k with hr
        have hd : q % 3 = 0 ∨ q % 3 = 1 := by omega
        have hq3 : q < 3 := by
          rw [hq]
          exact Nat.div_lt_of_lt_mul (by rw [← Nat.pow_succ]; exact hlt)
        have hr' : r < 3 ^ k := by rw [hr]; exact Nat.mod_lt n (Nat.pow_pos (n := k) (by omega : (0:Nat) < 3))
        have h := Nat.div_add_mod n (3 ^ k)
        rw [← hq, ← hr] at h
        -- h : 3 ^ k * q + r = n
        clear hq hr
        rcases hd with hd0 | hd1
        · have hq0 : q = 0 := digit0_eq_zero hq3 hd0
          rw [hq0, Nat.mul_zero, Nat.zero_add] at h
          -- h : r = n
          left
          refine ⟨hlt, ?_, ?_⟩
          · rw [← h]; exact hr'
          · exact fun t ht => hall t ht
        · have hq1 : q = 1 := digit1_eq_one hq3 hd1
          rw [hq1, Nat.mul_one] at h
          -- h : 3 ^ k + r = n
          right
          have hge : 3 ^ k ≤ n := by rw [← h]; exact Nat.le_add_right (3 ^ k) r
          refine ⟨hlt, hge, ?_, ?_⟩
          · rw [← h]; omega
          · intro t ht
            rw [← digit_below_k_eq hge ht]
            exact hall t ht
      · rintro (⟨hlt, hlt3, hall⟩ | ⟨hlt, hge, hlt2, hall'⟩)
        · refine ⟨hlt, ?_, ?_⟩
          · exact fun t ht => hall t ht
          · set q := n / 3 ^ k with hq
            have hq1 : q < 1 := by
              rw [hq]
              exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_one]; exact hlt3)
            have hq0 : q = 0 := Nat.lt_one_iff.mp hq1
            rw [hq0]
            norm_num
        · have hlt1 : n < 3 ^ (k + 1) := by
            have h23 : 2 * 3 ^ k ≤ 3 * 3 ^ k := Nat.mul_le_mul_right (3 ^ k) (by omega)
            calc n < 2 * 3 ^ k := hlt2
              _ ≤ 3 * 3 ^ k := h23
              _ = 3 ^ (k + 1) := by
                rw [Nat.mul_comm 3 (3 ^ k)]
                exact (Nat.pow_succ 3 k).symm
          set q := n / 3 ^ k with hq
          set r := n % 3 ^ k with hr
          have hq3 : q < 3 := by
            rw [hq]
            exact Nat.div_lt_of_lt_mul (by rw [← Nat.pow_succ]; exact hlt1)
          have hr' : r < 3 ^ k := by rw [hr]; exact Nat.mod_lt n (Nat.pow_pos (n := k) (by omega : (0:Nat) < 3))
          have h := Nat.div_add_mod n (3 ^ k)
          rw [← hq, ← hr] at h
          -- h : 3 ^ k * q + r = n
          clear hq hr
          have hge' : 1 ≤ q := by
            by_contra h0
            push_neg at h0
            -- h0 : q < 1
            have hq0 : q = 0 := Nat.lt_one_iff.mp h0
            rw [hq0, Nat.mul_zero, Nat.zero_add] at h
            -- h : r = n
            rw [← h] at hge
            exact absurd hge (not_le.mpr hr')
          have hne2 : q ≠ 2 := by
            intro heq
            rw [heq, Nat.mul_comm] at h
            -- h : 2 * 3 ^ k + r = n
            have hle : 2 * 3 ^ k ≤ n := by
              rw [← h]
              exact Nat.le_add_right (2 * 3 ^ k) r
            omega
          have hq1 : q = 1 := by omega
          refine ⟨hlt, ?_, ?_⟩
          · intro t ht
            rw [digit_below_k_eq hge ht]
            exact hall' t ht
          · rw [hq1]
            norm_num
    -- Right half (digit k = 1) has cardinality 2^k via the shift n ↦ n - 3^k
    have cardR :
        ((Finset.range (3 ^ (k + 1))).filter fun n =>
          3 ^ k ≤ n ∧ n < 2 * 3 ^ k ∧ ∀ t, t < k → ((n - 3 ^ k) / 3 ^ t) % 3 ≠ 2).card = 2 ^ k := by
      have heq :
          ((Finset.range (3 ^ (k + 1))).filter fun n =>
            3 ^ k ≤ n ∧ n < 2 * 3 ^ k ∧ ∀ t, t < k → ((n - 3 ^ k) / 3 ^ t) % 3 ≠ 2) =
          ((Finset.range (3 ^ k)).filter fun m =>
            ∀ t, t < k → (m / 3 ^ t) % 3 ≠ 2).image (fun m => m + 3 ^ k) := by
        ext n
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
        constructor
        · rintro ⟨hlt, hge', hlt2, hall⟩
          refine ⟨n - 3 ^ k, ⟨⟨by omega, hall⟩, by omega⟩⟩
        · rintro ⟨m, ⟨hm, hall⟩, rfl⟩
          have hlt23 : m + 3 ^ k < 2 * 3 ^ k := by omega
          have h23 : 2 * 3 ^ k ≤ 3 ^ (k + 1) := by
            have h2 := Nat.mul_le_mul_right (3 ^ k) (by omega : (2:ℕ) ≤ 3)
            rw [Nat.mul_comm 3 (3 ^ k)] at h2
            rwa [← Nat.pow_succ] at h2
          have hlt1 : m + 3 ^ k < 3 ^ (k + 1) := Nat.lt_of_lt_of_le hlt23 h23
          refine ⟨hlt1, by omega, hlt23, ?_⟩
          intro t ht
          rw [show m + 3 ^ k - 3 ^ k = m from Nat.add_sub_cancel_right m (3 ^ k)]
          exact hall t ht
      rw [heq, Finset.card_image_of_injOn, d2f_card_aux k]
      · intro a₁ _ a₂ _ heq'
        simp only at heq'
        omega
    -- Now count each half
    rw [hpart, Finset.card_union_eq, filter_left_eq, d2f_card_aux k, cardR]
    · rw [show 2 ^ k + 2 ^ k = 2 ^ k * 2 from by ring, ← Nat.pow_succ]
    · -- Disjoint: left half has all elements < 3^k, right half has all ≥ 3^k
      apply Finset.disjoint_left.mpr
      intro n hL hR
      simp only [Finset.mem_filter, Finset.mem_range] at hL hR
      omega

/-- Low 15 bits of 2^(s+P·r) mod 3^30 are constant in r (Euler: 2^P ≡ 1 mod 3^15). -/
private theorem low15_const (s : Nat) : ∀ r, 2 ^ (s + P * r) % 3 ^ 15 = 2 ^ s % 3 ^ 15 := by
  intro r
  have hpow : ∀ r, (2 ^ P) ^ r % 3 ^ 15 = 1 := by
    intro r
    induction r with
    | zero => norm_num [Nat.pow_zero]
    | succ r ih =>
      rw [show (2 ^ P) ^ (r + 1) = (2 ^ P) ^ r * 2 ^ P from by
        rw [show r + 1 = Nat.succ r from rfl, Nat.pow_succ],
        Nat.mul_mod, ih, two_pow_P_mod_3_15_eq_1, Nat.mul_one]
      exact Nat.mod_eq_of_lt (by norm_num : 1 < 3 ^ 15)
  have hsplit : 2 ^ (s + P * r) = 2 ^ s * (2 ^ P) ^ r := by
    rw [Nat.pow_add, Nat.pow_mul]
  rw [hsplit, Nat.mul_mod, hpow r, Nat.mul_one]
  exact Nat.mod_eq_of_lt (Nat.mod_lt _ (by omega : (0:Nat) < 3 ^ 15))

/-- block1Val is injective on r < 3^15: the window (bits 15..29) together with
    the constant low bits (mod 3^15) determines 2^(s+P·r) mod 3^30 fully, so
    equal block1Val implies equal full residues and full_injective applies.
    (This replaces the original direct appeal to full_injective, whose
    hypothesis is equality of the full residues, not of the window.) -/
theorem block1Val_injective (s : Nat) {r₁ r₂ : Nat}
    (h₁ : r₁ < 3 ^ 15) (h₂ : r₂ < 3 ^ 15) :
    block1Val s r₁ = block1Val s r₂ → r₁ = r₂ := by
  intro h
  have hv1 : 2 ^ (s + P * r₁) % 3 ^ 30 < 3 ^ 30 := Nat.mod_lt _ (by omega)
  have hv2 : 2 ^ (s + P * r₂) % 3 ^ 30 < 3 ^ 30 := Nat.mod_lt _ (by omega)
  simp only [block1Val] at h
  have hq : 2 ^ (s + P * r₁) % 3 ^ 30 / 3 ^ 15 = 2 ^ (s + P * r₂) % 3 ^ 30 / 3 ^ 15 := by
    have e1 : 2 ^ (s + P * r₁) % 3 ^ 30 / 3 ^ 15 < 3 ^ 15 :=
      Nat.div_lt_of_lt_mul (by
        rw [show 3 ^ 15 * 3 ^ 15 = 3 ^ 30 from by rw [← Nat.pow_add]]
        exact hv1)
    have e2 : 2 ^ (s + P * r₂) % 3 ^ 30 / 3 ^ 15 < 3 ^ 15 :=
      Nat.div_lt_of_lt_mul (by
        rw [show 3 ^ 15 * 3 ^ 15 = 3 ^ 30 from by rw [← Nat.pow_add]]
        exact hv2)
    rw [← Nat.mod_eq_of_lt e1, ← Nat.mod_eq_of_lt e2]
    exact h
  have hlow₁ : (2 ^ (s + P * r₁) % 3 ^ 30) % 3 ^ 15 = 2 ^ s % 3 ^ 15 := by
    rw [Nat.mod_mod_of_dvd (2 ^ (s + P * r₁)) (by norm_num : 3 ^ 15 ∣ 3 ^ 30)]
    exact low15_const s r₁
  have hlow₂ : (2 ^ (s + P * r₂) % 3 ^ 30) % 3 ^ 15 = 2 ^ s % 3 ^ 15 := by
    rw [Nat.mod_mod_of_dvd (2 ^ (s + P * r₂)) (by norm_num : 3 ^ 15 ∣ 3 ^ 30)]
    exact low15_const s r₂
  have hv1' : 2 ^ (s + P * r₁) % 3 ^ 30 =
      2 ^ s % 3 ^ 15 + 3 ^ 15 * (2 ^ (s + P * r₁) % 3 ^ 30 / 3 ^ 15) := by
    have hd := Nat.div_add_mod (2 ^ (s + P * r₁) % 3 ^ 30) (3 ^ 15)
    calc 2 ^ (s + P * r₁) % 3 ^ 30
        = 3 ^ 15 * (2 ^ (s + P * r₁) % 3 ^ 30 / 3 ^ 15) + (2 ^ (s + P * r₁) % 3 ^ 30) % 3 ^ 15 := by
          exact hd.symm
      _ = 2 ^ s % 3 ^ 15 + 3 ^ 15 * (2 ^ (s + P * r₁) % 3 ^ 30 / 3 ^ 15) := by
          rw [hlow₁, Nat.add_comm]
  have hv2' : 2 ^ (s + P * r₂) % 3 ^ 30 =
      2 ^ s % 3 ^ 15 + 3 ^ 15 * (2 ^ (s + P * r₂) % 3 ^ 30 / 3 ^ 15) := by
    have hd := Nat.div_add_mod (2 ^ (s + P * r₂) % 3 ^ 30) (3 ^ 15)
    calc 2 ^ (s + P * r₂) % 3 ^ 30
        = 3 ^ 15 * (2 ^ (s + P * r₂) % 3 ^ 30 / 3 ^ 15) + (2 ^ (s + P * r₂) % 3 ^ 30) % 3 ^ 15 := by
          exact hd.symm
      _ = 2 ^ s % 3 ^ 15 + 3 ^ 15 * (2 ^ (s + P * r₂) % 3 ^ 30 / 3 ^ 15) := by
          rw [hlow₂, Nat.add_comm]
  apply full_injective s r₁ r₂ h₁ h₂
  rw [hv1', hv2', hq]

/-- Block-1 exceptional count ≤ 2^15 for each s. -/
theorem block1_exceptional_le (s : Nat) :
    ((Finset.range (3 ^ 15)).filter fun r => noDigit2 (block1Val s r) = true).card ≤ 2 ^ 15 := by
  have hinj : ∀ r₁ r₂, r₁ < 3 ^ 15 → r₂ < 3 ^ 15 →
      block1Val s r₁ = block1Val s r₂ → r₁ = r₂ :=
    fun r₁ r₂ h₁ h₂ heq => block1Val_injective s h₁ h₂ heq
  have hpre := filter_preimage_le_of_injOn hinj (fun r _ => block1_val_lt s r)
    (fun r => noDigit2 r = true)
  have hcard : ((Finset.range (3 ^ 15)).filter (fun r => noDigit2 r = true)).card = 2 ^ 15 := by
    have h := d2f_card_aux 15
    have heq :
        (Finset.range (3 ^ 15)).filter (fun r => noDigit2 r = true) =
        (Finset.range (3 ^ 15)).filter (fun n => ∀ t, t < 15 → (n / 3 ^ t) % 3 ≠ 2) := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_range]
      have hiff : noDigit2 r = true ↔ ∀ t, t < 15 → (r / 3 ^ t) % 3 ≠ 2 := by
        simp [noDigit2, List.all_eq_true, List.mem_range, decide_eq_true_eq]
      constructor
      · intro ⟨hr, h1⟩; exact ⟨hr, hiff.mp h1⟩
      · intro ⟨hr, h1⟩; exact ⟨hr, hiff.mpr h1⟩
    rw [heq]
    exact h
  omega

/-! ## Part 6: Convergence facts -/

theorem exception_decay : (2 ^ 15 : Real) / (3 ^ 15 : Real) < 1 / 4 := by norm_num
theorem blocks_three_suffice : (87 : Real) * (2 ^ 15 / 3 ^ 15) < 1 := by norm_num

/-! ## Part 7: Iterative block computation for blocks 2 and 3

    To avoid computing 2^(s+P*r) directly (which creates numbers with ~4M digits),
    we maintain running values: v_{r+1} = v_r * (2^P mod m) mod m.
    This gives O(1) per step with small numbers.
-/

/-- Iterative computation of 2^(s+P*n) mod m.
    Start at 2^s mod m, multiply by 2^P mod m at each step. -/
def iterVal (s m : Nat) : Nat → Nat
  | 0 => 2 ^ s % m
  | n + 1 => (iterVal s m n * (2 ^ P % m)) % m

theorem iterVal_zero (s m : Nat) : iterVal s m 0 = 2 ^ s % m := rfl

theorem iterVal_succ (s m n : Nat) :
    iterVal s m (n + 1) = (iterVal s m n * (2 ^ P % m)) % m := rfl

/-- iterVal agrees with the closed-form: iterVal s m n = 2^(s+P*n) mod m. -/
theorem iterVal_eq (s m n : Nat) : iterVal s m n = 2 ^ (s + P * n) % m := by
  induction n with
  | zero => simp [iterVal, Nat.pow_zero, Nat.add_zero]
  | succ n ih =>
    rw [iterVal_succ, ih]
    have hstep : 2 ^ (s + P * (n + 1)) = 2 ^ (s + P * n) * 2 ^ P := by
      have hexp : s + P * (n + 1) = s + P * n + P := by ring
      rw [hexp, Nat.pow_add]
    rw [hstep]
    exact (Nat.mul_mod ..).symm

/-- Block-2 value: positions 30..44 of 2^(s+P*r). -/
def block2Val (s r : Nat) : Nat :=
  (iterVal s (3 ^ 45) r / 3 ^ 30) % 3 ^ 15

theorem block2Val_lt (s r : Nat) : block2Val s r < 3 ^ 15 :=
  Nat.mod_lt _ (Nat.pow_pos (by omega : 0 < 3))

/-- Block-3 value: positions 45..59 of 2^(s+P*r). -/
def block3Val (s r : Nat) : Nat :=
  (iterVal s (3 ^ 60) r / 3 ^ 45) % 3 ^ 15

theorem block3Val_lt (s r : Nat) : block3Val s r < 3 ^ 15 :=
  Nat.mod_lt _ (Nat.pow_pos (by omega : 0 < 3))

/-- Block-2 value agrees with the direct formula. -/
theorem block2Val_eq (s r : Nat) :
    block2Val s r = (2 ^ (s + P * r) % 3 ^ 45 / 3 ^ 30) % 3 ^ 15 := by
  simp [block2Val, iterVal_eq]

/-- Block-3 value agrees with the direct formula. -/
theorem block3Val_eq (s r : Nat) :
    block3Val s r = (2 ^ (s + P * r) % 3 ^ 60 / 3 ^ 45) % 3 ^ 15 := by
  simp [block3Val, iterVal_eq]

/-! ## Part 8: Block-2/3 verification via native_decide

    We verify computationally that for each s ∈ {0, 2, 8}:
    every r with noDigit2 in block1 AND block2 has digit 2 in block3
    (0 residues survive all 3 blocks).
-/

/-- Structural-down loop for block-3 checking.
    Counts down from n to 0. At each step, checks if all three blocks
    have no digit 2. Returns true iff no checked position has all three blocks clean. -/
def checkBlock3LoopSD (pow30 pow45 pow60 : Nat) : Nat → Nat → Nat → Nat → Bool
  | 0, _v30, _v45, _v60 => true
  | n + 1, v30, v45, v60 =>
    if noDigit2 ((v30 / 3 ^ 15) % 3 ^ 15) &&
       noDigit2 ((v45 / 3 ^ 30) % 3 ^ 15) &&
       noDigit2 ((v60 / 3 ^ 45) % 3 ^ 15)
    then false
    else checkBlock3LoopSD pow30 pow45 pow60 n
      ((v30 * pow30) % (3 ^ 30)) ((v45 * pow45) % (3 ^ 45)) ((v60 * pow60) % (3 ^ 60))

/-- Check that no r < 3^15 has noDigit2 in all three blocks.
    Counts down from 3^15 with running accumulators. -/
def checkBlock3All (s : Nat) : Bool :=
  checkBlock3LoopSD pow2Pmod30 pow2Pmod45 pow2Pmod60 (3 ^ 15)
    (2 ^ s % 3 ^ 30) (2 ^ s % 3 ^ 45) (2 ^ s % 3 ^ 60)

/-- Verify: for s=0, no residue has noDigit2 in all three blocks. -/
set_option maxRecDepth 10000000 in
theorem block3_caught_0 : checkBlock3All 0 = true := by native_decide

/-- Verify: for s=2, no residue has noDigit2 in all three blocks. -/
set_option maxRecDepth 10000000 in
theorem block3_caught_2 : checkBlock3All 2 = true := by native_decide

/-- Verify: for s=8, no residue has noDigit2 in all three blocks. -/
set_option maxRecDepth 10000000 in
theorem block3_caught_8 : checkBlock3All 8 = true := by native_decide

/-! ### Soundness: checkBlock3All = true implies no all-clean residue -/

/-- When v30 = iterVal s (3^30) r, the block1 loop value equals block1Val. -/
private theorem block1_eq_loop (s r : Nat) (v30 : Nat) (hv30 : v30 = iterVal s (3 ^ 30) r) :
    noDigit2 (block1Val s r) = noDigit2 ((v30 / 3 ^ 15) % 3 ^ 15) := by
  subst hv30; simp [block1Val, iterVal_eq]

/-- When v45 = iterVal s (3^45) r, the block2 loop value equals block2Val. -/
private theorem block2_eq_loop (s r : Nat) (v45 : Nat) (hv45 : v45 = iterVal s (3 ^ 45) r) :
    noDigit2 (block2Val s r) = noDigit2 ((v45 / 3 ^ 30) % 3 ^ 15) := by
  subst hv45; simp [block2Val, iterVal_eq]

/-- When v60 = iterVal s (3^60) r, the block3 loop value equals block3Val. -/
private theorem block3_eq_loop (s r : Nat) (v60 : Nat) (hv60 : v60 = iterVal s (3 ^ 60) r) :
    noDigit2 (block3Val s r) = noDigit2 ((v60 / 3 ^ 45) % 3 ^ 15) := by
  subst hv60; simp [block3Val, iterVal_eq]

/-- ¬(a && b && c = true) implies ¬(a = true ∧ b = true ∧ c = true). -/
private theorem bool_clean_not {a b c : Bool} (h : ¬(a && b && c = true)) :
    ¬(a = true ∧ b = true ∧ c = true) := by
  intro ⟨ha, hb, hc⟩; simp [ha, hb, hc] at h

/-- Soundness of the loop: if checkBlock3LoopSD returns true with n remaining steps
    starting from position r = 3^15 - n, then no position i ∈ [r, 3^15) has all
    three blocks digit-2-free. -/
private theorem checkBlock3LoopSD_sound (pow30 pow45 pow60 s : Nat)
    (hp30 : pow30 = 2 ^ P % 3 ^ 30)
    (hp45 : pow45 = 2 ^ P % 3 ^ 45)
    (hp60 : pow60 = 2 ^ P % 3 ^ 60) :
    ∀ (n : Nat) (r : Nat) (v30 v45 v60 : Nat),
    n = 3 ^ 15 - r →
    v30 = iterVal s (3 ^ 30) r →
    v45 = iterVal s (3 ^ 45) r →
    v60 = iterVal s (3 ^ 60) r →
    checkBlock3LoopSD pow30 pow45 pow60 n v30 v45 v60 = true →
    ∀ i, r ≤ i → i < 3 ^ 15 →
    ¬(noDigit2 (block1Val s i) ∧ noDigit2 (block2Val s i) ∧ noDigit2 (block3Val s i)) := by
  intro n
  induction n with
  | zero =>
    intro r v30 v45 v60 hn hv30 hv45 hv60 h i hi_le hi_lt
    omega
  | succ k ih =>
    intro r v30 v45 v60 hn hv30 hv45 hv60 h i hi_le hi_lt
    have hr315 : r < 3 ^ 15 := by omega
    unfold checkBlock3LoopSD at h
    split at h
    · next hcond =>
      contradiction
    · next hcond =>
      by_cases hir : i = r
      · subst hir
        intro ⟨hb1, hb2, hb3⟩
        rw [block1_eq_loop s i v30 hv30] at hb1
        rw [block2_eq_loop s i v45 hv45] at hb2
        rw [block3_eq_loop s i v60 hv60] at hb3
        exact bool_clean_not hcond ⟨hb1, hb2, hb3⟩
      · have hri : r < i := by omega
        have hv30' : (v30 * pow30) % (3 ^ 30) = iterVal s (3 ^ 30) (r + 1) := by
          simp only [iterVal_succ, hv30, hp30]
        have hv45' : (v45 * pow45) % (3 ^ 45) = iterVal s (3 ^ 45) (r + 1) := by
          simp only [iterVal_succ, hv45, hp45]
        have hv60' : (v60 * pow60) % (3 ^ 60) = iterVal s (3 ^ 60) (r + 1) := by
          simp only [iterVal_succ, hv60, hp60]
        exact ih (r + 1) ((v30 * pow30) % (3 ^ 30)) ((v45 * pow45) % (3 ^ 45))
          ((v60 * pow60) % (3 ^ 60)) (by omega) hv30' hv45' hv60' h i (by omega) hi_lt

/-- Block-3 catches everything: for every s ∈ {0,2,8} and every r < 3^15,
    if block1 and block2 have no digit 2, then block3 does have digit 2. -/
set_option maxRecDepth 10000000 in
theorem block3_catches_all (s : Nat) (hs : s = 0 ∨ s = 2 ∨ s = 8) :
    ∀ r < 3 ^ 15, noDigit2 (block1Val s r) → noDigit2 (block2Val s r) →
    ¬noDigit2 (block3Val s r) := by
  have h0 := checkBlock3LoopSD_sound pow2Pmod30 pow2Pmod45 pow2Pmod60 s
    pow2Pmod30_eq pow2Pmod45_eq pow2Pmod60_eq
  intro r hr h1 h2 h3
  have hc : checkBlock3All s = true := by rcases hs with rfl | rfl | rfl <;> native_decide
  unfold checkBlock3All at hc
  exact h0 (3 ^ 15) 0 (2^s%3^30) (2^s%3^45) (2^s%3^60) (by omega) rfl rfl rfl hc r (by omega) hr ⟨h1, h2, h3⟩

/-! ## Part 9: Period lemmas for block values

    Key fact: 2^P ≡ 1 (mod 3^15) by Euler's theorem (φ(3^15) = P).
    Period lemmas proved by reducing to pow2ModAux + native_decide,
    avoiding the general lifting lemma that causes elaborator issues.
-/

/-- Period of block1: (2^P)^(3^15) ≡ 1 (mod 3^30). Restates euler_result. -/
theorem powP_period_block1 : (2 ^ P) ^ (3 ^ 15) % 3 ^ 30 = 1 := euler_result

/-- Period of block2: (2^P)^(3^30) ≡ 1 (mod 3^45).
    Proof: reduce to pow2ModAux + native_decide (term-level composition). -/
theorem powP_period_block2 : (2 ^ P) ^ (3 ^ 30) % 3 ^ 45 = 1 := by
  have h1 : (2 ^ P) ^ (3 ^ 30) % 3 ^ 45 = ((2 ^ P) % 3 ^ 45) ^ (3 ^ 30) % 3 ^ 45 := Nat.pow_mod (2 ^ P) (3 ^ 30) (3 ^ 45)
  have h1b : ((2 ^ P) % 3 ^ 45) ^ (3 ^ 30) % 3 ^ 45 = pow2Pmod45 ^ (3 ^ 30) % 3 ^ 45 := by
    rw [← pow2Pmod45_eq]
  have h2 : pow2Pmod45 ^ (3 ^ 30) % 3 ^ 45 = pow2ModAux (3 ^ 30) pow2Pmod45 (3 ^ 45) :=
    (pow2ModAux_eq' (3 ^ 30) pow2Pmod45 (3 ^ 45)).symm
  have h3 : pow2ModAux (3 ^ 30) pow2Pmod45 (3 ^ 45) = 1 := by native_decide
  exact h1.trans (h1b.trans (h2.trans h3))

/-- Period of block3: (2^P)^(3^45) ≡ 1 (mod 3^60).
    Proof: reduce to pow2ModAux + native_decide (term-level composition). -/
theorem powP_period_block3 : (2 ^ P) ^ (3 ^ 45) % 3 ^ 60 = 1 := by
  have h1 : (2 ^ P) ^ (3 ^ 45) % 3 ^ 60 = ((2 ^ P) % 3 ^ 60) ^ (3 ^ 45) % 3 ^ 60 := Nat.pow_mod (2 ^ P) (3 ^ 45) (3 ^ 60)
  have h1b : ((2 ^ P) % 3 ^ 60) ^ (3 ^ 45) % 3 ^ 60 = pow2Pmod60 ^ (3 ^ 45) % 3 ^ 60 := by
    rw [← pow2Pmod60_eq]
  have h2 : pow2Pmod60 ^ (3 ^ 45) % 3 ^ 60 = pow2ModAux (3 ^ 45) pow2Pmod60 (3 ^ 60) :=
    (pow2ModAux_eq' (3 ^ 45) pow2Pmod60 (3 ^ 60)).symm
  have h3 : pow2ModAux (3 ^ 45) pow2Pmod60 (3 ^ 60) = 1 := by native_decide
  exact h1.trans (h1b.trans (h2.trans h3))

/-! ## Part 10: Block value periodicity

    From the period lemmas, iterVal s m r is periodic in r:
    - Period 3^15 for modulus 3^30 (block1)
    - Period 3^30 for modulus 3^45 (block2)
    - Period 3^45 for modulus 3^60 (block3)
-/

private theorem iterVal_period (s mod : Nat) (period : Nat)
    (hperiod : (2 ^ P) ^ period % mod = 1) :
    ∀ r, iterVal s mod (r + period) = iterVal s mod r := by
  intro r
  rw [iterVal_eq, iterVal_eq]
  rw [show s + P * (r + period) = s + P * r + P * period from by ring, Nat.pow_add]
  have hper : 2 ^ (P * period) % mod = 1 := by rw [Nat.pow_mul]; exact hperiod
  rw [← Nat.mul_mod_mod, hper, Nat.mul_one]

private theorem iterVal_mod_period (s mod period : Nat)
    (hperiod : (2 ^ P) ^ period % mod = 1) :
    ∀ r, iterVal s mod r = iterVal s mod (r % period) := by
  intro r
  suffices ∀ q, iterVal s mod (period * q + r % period) = iterVal s mod (r % period) by
    have h := this (r / period)
    have hr : r = period * (r / period) + r % period := (Nat.div_add_mod r period).symm
    rw [← hr] at h; exact h
  intro q; induction q with
  | zero => simp [Nat.zero_mul, Nat.add_zero]
  | succ q ih =>
    rw [show period * (q + 1) + r % period = (period * q + r % period) + period from by ring]
    rw [iterVal_period s mod period hperiod, ih]

/-- block1Val is periodic in r with period 3^15. -/
theorem block1Val_periodic (s m : Nat) :
    block1Val s m = block1Val s (m % 3 ^ 15) := by
  simp only [block1Val]
  suffices 2 ^ (s + P * m) % 3 ^ 30 = 2 ^ (s + P * (m % 3 ^ 15)) % 3 ^ 30 by rw [this]
  have hexp : s + P * m = s + P * (m % 3 ^ 15) + P * (3 ^ 15 * (m / 3 ^ 15)) := by
    conv_lhs => rw [show m = 3 ^ 15 * (m / 3 ^ 15) + m % 3 ^ 15 from (Nat.div_add_mod m (3 ^ 15)).symm]
    ring
  rw [hexp, Nat.pow_add]
  have hper : 2 ^ (P * (3 ^ 15 * (m / 3 ^ 15))) % 3 ^ 30 = 1 := by
    rw [← Nat.mul_assoc P (3 ^ 15) (m / 3 ^ 15), Nat.pow_mul]
    rw [show 2 ^ (P * 3 ^ 15) = (2 ^ P) ^ (3 ^ 15) from pow_mul 2 P (3 ^ 15)]
    rw [Nat.pow_mod, powP_period_block1, Nat.one_pow]; norm_num
  rw [← Nat.mul_mod_mod, hper, Nat.mul_one]

/-- block2Val is periodic in r with period 3^30. -/
theorem block2Val_periodic (s m : Nat) :
    block2Val s m = block2Val s (m % 3 ^ 30) := by
  simp only [block2Val]
  rw [iterVal_eq, iterVal_eq]
  have hexp : s + P * m = s + P * (m % 3 ^ 30) + P * (3 ^ 30 * (m / 3 ^ 30)) := by
    conv_lhs => rw [show m = 3 ^ 30 * (m / 3 ^ 30) + m % 3 ^ 30 from (Nat.div_add_mod m (3 ^ 30)).symm]
    ring
  rw [hexp, Nat.pow_add]
  have hper : 2 ^ (P * (3 ^ 30 * (m / 3 ^ 30))) % 3 ^ 45 = 1 := by
    rw [← Nat.mul_assoc P (3 ^ 30) (m / 3 ^ 30), Nat.pow_mul]
    rw [show 2 ^ (P * 3 ^ 30) = (2 ^ P) ^ (3 ^ 30) from pow_mul 2 P (3 ^ 30)]
    rw [Nat.pow_mod, powP_period_block2, Nat.one_pow]; norm_num
  rw [← Nat.mul_mod_mod, hper, Nat.mul_one]

/-- block3Val is periodic in r with period 3^45. -/
theorem block3Val_periodic (s m : Nat) :
    block3Val s m = block3Val s (m % 3 ^ 45) := by
  simp only [block3Val]
  rw [iterVal_eq, iterVal_eq]
  have hexp : s + P * m = s + P * (m % 3 ^ 45) + P * (3 ^ 45 * (m / 3 ^ 45)) := by
    conv_lhs => rw [show m = 3 ^ 45 * (m / 3 ^ 45) + m % 3 ^ 45 from (Nat.div_add_mod m (3 ^ 45)).symm]
    ring
  rw [hexp, Nat.pow_add]
  have hper : 2 ^ (P * (3 ^ 45 * (m / 3 ^ 45))) % 3 ^ 60 = 1 := by
    rw [← Nat.mul_assoc P (3 ^ 45) (m / 3 ^ 45), Nat.pow_mul]
    rw [show 2 ^ (P * 3 ^ 45) = (2 ^ P) ^ (3 ^ 45) from pow_mul 2 P (3 ^ 45)]
    rw [Nat.pow_mod, powP_period_block3, Nat.one_pow]; norm_num
  rw [← Nat.mul_mod_mod, hper, Nat.mul_one]

end ErdosTernary.BlockClassification
