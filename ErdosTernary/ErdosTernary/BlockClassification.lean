/-
  BlockClassification.lean — Block classification for the Erdős ternary conjecture.

  Proves: the order of 2^P mod 3^30 is exactly 3^15 (via cubing chain + Euler),
  establishing injectivity of the residue map and the block-1 counting bound.

  This file contains NO sorry, NO admit, NO axioms.
-/
import Mathlib.Tactic
import Mathlib.Data.Int.GCD
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

private theorem coprime_2_P : Nat.Coprime 2 (2 ^ P) := by
  exact Nat.Coprime.symm (Nat.Coprime.pow P_pos (by decide))

private theorem euler_mod (d : Nat) (hd : d = 3 ^ 15) :
    (2 ^ P) ^ d % 3 ^ 30 = 1 := by rw [hd]; exact euler_result

private theorem pow_P_3_14_mod : (2 ^ P) ^ (3 ^ 14) % 3 ^ 30 ≠ 1 := pow_P_3_14_ne_1

/-! Key lemma: if (2^P)^a ≡ 1 and (2^P)^b ≡ 1 mod 3^30,
    then (2^P)^(gcd a b) ≡ 1 mod 3^30.
    We prove this by lifting to ZMod (3^30) and using Mathlib's pow_gcd_eq_one. -/

private theorem cast_natCast_pow_mod_eq_zero {m : Nat} (hm : 0 < m) {a : Nat}
    (h : a % m = 0) : (a : ZMod m) = 0 := by
  rw [ZMod.natCast_zmod_eq_zero_iff_dvd]; omega

private theorem mod_eq_one_iff_cast {m : Nat} (hm : 0 < m) {a : Nat} :
    a % m = 1 ↔ (a : ZMod m) = 1 := by
  constructor
  · intro h; rw [show (1 : ZMod m) = (1 : Nat) from by norm_cast,
      ZMod.natCast_zmod_eq_zero_iff_dvd]; omega
  · intro h; rw [show (1 : ZMod m) = (1 : Nat) from by norm_cast,
      ZMod.natCast_zmod_eq_zero_iff_dvd] at h; omega

private theorem pow_gcd_mod30 (a b : Nat)
    (ha : (2 ^ P) ^ a % 3 ^ 30 = 1) (hb : (2 ^ P) ^ b % 3 ^ 30 = 1) :
    (2 ^ P) ^ (Nat.gcd a b) % 3 ^ 30 = 1 := by
  have h30 : 0 < 3 ^ 30 := by norm_num
  have hza : (2 ^ P : ZMod (3 ^ 30)) ^ a = 1 := (mod_eq_one_iff_cast h30).mp ha |>.symm ▸ by
    rw [show (1 : ZMod (3 ^ 30)) = (1 : Nat) from by norm_cast]; norm_cast
  have hzb : (2 ^ P : ZMod (3 ^ 30)) ^ b = 1 := (mod_eq_one_iff_cast h30).mp hb |>.symm ▸ by
    rw [show (1 : ZMod (3 ^ 30)) = (1 : Nat) from by norm_cast]; norm_cast
  have hz := pow_gcd_eq_one (2 ^ P : ZMod (3 ^ 30)) hza hzb
  exact (mod_eq_one_iff_cast h30).mpr (by rw [show (1 : ZMod (3 ^ 30)) = (1 : Nat) from by norm_cast]; norm_cast; exact hz)

/-! The order of 2^P mod 3^30 is 3^15.
    Since (2^P)^(3^15) ≡ 1 and (2^P)^(3^14) ≢ 1, the only divisor of 3^15
    that can be the order is 3^15 itself. -/

private theorem pow_eq_one_implies_order_dvd (d : Nat) (hd : 0 < d) :
    (2 ^ P) ^ d % 3 ^ 30 = 1 → 3 ^ 15 ∣ d := by
  intro h
  have hgcd := pow_gcd_mod30 d (3 ^ 15) h euler_result
  have hgcd_dvd : Nat.gcd d (3 ^ 15) ∣ 3 ^ 15 := Nat.gcd_dvd_right d (3 ^ 15)
  obtain ⟨k, hk_le, rfl⟩ := (dvd_prime_pow (by decide : Nat.Prime 3)).mp hgcd_dvd
  by_cases hk14 : k < 15
  · -- k ≤ 14: 3^k | 3^14, so (2^P)^(3^14) ≡ 1, contradiction
    have hk14' : k ≤ 14 := by omega
    have h3k : (2 ^ P) ^ (3 ^ k) % 3 ^ 30 = 1 := by
      rwa [Nat.pow_right_comm] at hgcd
    have h314 : (2 ^ P) ^ (3 ^ 14) % 3 ^ 30 = 1 := by
      have : 3 ^ 14 = 3 ^ k * 3 ^ (14 - k) := by rw [← Nat.pow_add]; omega
      rw [this, Nat.pow_mul, ← Nat.pow_mod_mod, h3k, Nat.one_pow, Nat.one_mod]
    exact absurd h314 pow_P_3_14_ne_1
  · -- k ≥ 15 and k ≤ 15, so k = 15
    have : k = 15 := by omega
    subst this; exact Nat.dvd_refl (3 ^ 15)

/-! ## Part 3: Injectivity of the full residue map -/

theorem full_injective (s r₁ r₂ : Nat)
    (h₁ : r₁ < 3 ^ 15) (h₂ : r₂ < 3 ^ 15) :
    2 ^ (s + P * r₁) % 3 ^ 30 = 2 ^ (s + P * r₂) % 3 ^ 30 → r₁ = r₂ := by
  wlog hle : r₁ ≤ r₂ generalizing r₁ r₂ with hle'
  · intro h; symm at h; have := this hle' h₂ h₁ h; omega
  intro h
  have diff_le : r₂ - r₁ < 3 ^ 15 := Nat.sub_lt_left_of_lt_add hle (by omega)
  -- From 2^(s+P*r₁) ≡ 2^(s+P*r₂) [MOD 3^30], derive (2^P)^(r₂-r₁) ≡ 1 [MOD 3^30]
  have hdiff : (2 ^ P) ^ (r₂ - r₁) % 3 ^ 30 = 1 := by
    have h1 : 2 ^ (s + P * r₂) % 3 ^ 30 = 2 ^ (s + P * r₁) % 3 ^ 30 := h.symm
    have h2 : s + P * r₂ = s + P * r₁ + P * (r₂ - r₁) := by omega
    rw [h2, Nat.pow_add, ← Nat.mul_mod] at h1
    have cop : Nat.Coprime (2 ^ (s + P * r₁) % 3 ^ 30) (3 ^ 30) := by
      apply Nat.Coprime.symm; rw [Nat.coprime_comm, Nat.Coprime.pow_right]
      exact coprime_2_3_30
    have hne0 : 2 ^ (s + P * r₁) % 3 ^ 30 ≠ 0 := by
      intro hz; have := cop.eq_one_of_dvd_left (dvd_zero _) hz; norm_num at this
    have := cop.mul_right_cancel hne0 (by omega : (2 ^ (s + P * r₁) % 3 ^ 30) *
      (2 ^ (P * (r₂ - r₁)) % 3 ^ 30) % 3 ^ 30 = 2 ^ (s + P * r₁) % 3 ^ 30)
    rwa [Nat.pow_mul] at this
  -- (2^P)^(r₂-r₁) ≡ 1 with 0 ≤ r₂-r₁ < 3^15 ⟹ 3^15 | (r₂-r₁) ⟹ r₂-r₁ = 0
  by_contra hne
  have hd_pos : 0 < r₂ - r₁ := Nat.sub_pos_of_lt (by omega)
  have hdvd := pow_eq_one_implies_order_dvd (r₂ - r₁) hd_pos hdiff
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
    (P : Nat → Prop) [DecidablePred P] :
    ((Finset.range N).filter fun r => P (f r)).card ≤
    ((Finset.range N).filter P).card := by
  have key :
      ((Finset.range N).filter fun r => P (f r)).image f ⊆
      (Finset.range N).filter P := by
    intro n hn; simp [Finset.mem_image, Finset.mem_filter] at hn
    obtain ⟨r, hr, rfl⟩ := hn; exact hr.2
  have hcard : (((Finset.range N).filter fun r => P (f r)).image f).card =
      ((Finset.range N).filter fun r => P (f r)).card := by
    apply Finset.card_image_of_injOn
    intro r₁ hr₁ r₂ hr₂ hfeq
    simp [Finset.mem_filter, Finset.mem_range] at hr₁ hr₂
    exact hf r₁ r₂ hr₁.1 hr₂.1 hfeq
  rw [← hcard]; exact Finset.card_le_card key

/-- Digit-2-free counting: exactly 2^k values in [0, 3^k) have no digit 2
    in their k-digit ternary representation.
    Proof: induction on k. Each step doubles the count (MSB ∈ {0,1}). -/
private theorem d2f_card_aux :
    ∀ k, ((Finset.range (3 ^ k)).filter fun n =>
      (List.range k).all fun t => (n / 3 ^ t) % 3 ≠ 2).card = 2 ^ k
  | 0 => by simp [List.range, List.all]; norm_num
  | k + 1 => by
    simp only [List.range_succ, List.all, Bool.and_eq_true, decide_eq_true_eq]
    -- S_{k+1} = {n < 3^{k+1} | digit k ≠ 2 ∧ noDigit2 in lower k digits}
    -- Split by MSB: digit k = 0 or digit k = 1
    have hpart :
        ((Finset.range (3 ^ (k + 1))).filter fun n =>
            (n / 3 ^ k) % 3 ≠ 2 ∧
            ∀ t, t < k → (n / 3 ^ t) % 3 ≠ 2) =
        ((Finset.range (3 ^ (k + 1))).filter fun n =>
            n < 3 ^ k ∧ ∀ t, t < k → (n / 3 ^ t) % 3 ≠ 2) ∪
        ((Finset.range (3 ^ (k + 1))).filter fun n =>
            3 ^ k ≤ n ∧ n < 2 * 3 ^ k ∧
            ∀ t, t < k → ((n - 3 ^ k) / 3 ^ t) % 3 ≠ 2) := by
      ext n; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union]
      constructor
      · rintro ⟨hlt, hdne, hall⟩
        have hd : (n / 3 ^ k) % 3 = 0 ∨ (n / 3 ^ k) % 3 = 1 := by omega
        rcases hd with hd0 | hd1
        · left; exact ⟨hlt, hd0, by
            intro t ht; have := hall t ht
            -- For t < k, (n/3^t)%3 is determined by lower digits
            have hle : 3 ^ t < 3 ^ k := Nat.pow_lt_pow_right (by omega : 1 < 3) ht
            have hn0 : n / 3 ^ t % 3 = n % 3 ^ k / 3 ^ t % 3 := by
              rw [Nat.mod_mul_right_div_self n (3 ^ t) (3 ^ (k - t))]
              ring_nf; rw [Nat.add_sub_cancel' (Nat.le_of_lt hle)]
              rw [show 3 ^ t * 3 ^ (k - t) = 3 ^ k from by rw [← Nat.pow_add]; omega]
            rwa [hn0]⟩
        · right; have hn1 : n / 3 ^ k % 3 = 1 := hd1
          have hge : 3 ^ k ≤ n := by
            have h := Nat.div_add_mod n (3 ^ k)
            omega
          have hlt2 : n < 2 * 3 ^ k := by
            have h := Nat.div_add_mod n (3 ^ k)
            omega
          exact ⟨hge, hlt2, by
            intro t ht; have := hall t ht
            have hle : 3 ^ t < 3 ^ k := Nat.pow_lt_pow_right (by omega : 1 < 3) ht
            have hn0 : n / 3 ^ t % 3 = (n - 3 ^ k) / 3 ^ t % 3 := by
              have hnk : n = 3 ^ k + (n - 3 ^ k) := by omega
              rw [hnk, Nat.add_div_of_dvd_left (Dvd.dvd rfl : 3 ^ k ∣ 3 ^ k)]
              rw [show (3 ^ k + (n - 3 ^ k)) / 3 ^ k = 1 + (n - 3 ^ k) / 3 ^ k from by
                rw [Nat.add_div_of_dvd_left (Dvd.dvd rfl : 3 ^ k ∣ 3 ^ k)]; omega]
              rw [show (1 + (n - 3 ^ k) / 3 ^ k) % 3 = (n - 3 ^ k) / 3 ^ k % 3 from by
                have := Nat.div_lt_self (by omega : 0 < n - 3 ^ k) (by omega : 1 < 3)
                omega]
            rwa [hn0]⟩
      · rintro (⟨hlt, hd0, hall⟩ | ⟨hge, hlt2, hall⟩)
        · constructor
          · exact hlt
          · constructor
            · have : n / 3 ^ k = 0 := Nat.div_eq_zero_of_lt hlt
              omega
            · intro t ht; exact hall t ht
        · constructor
          · omega
          · constructor
            · have h := Nat.div_add_mod n (3 ^ k)
              omega
            · intro t ht; have := hall t ht
              have hle : 3 ^ t < 3 ^ k := Nat.pow_lt_pow_right (by omega : 1 < 3) ht
              have hn0 : (n - 3 ^ k) / 3 ^ t % 3 = n / 3 ^ t % 3 := by
                have hnk : n = 3 ^ k + (n - 3 ^ k) := by omega
                rw [hnk] at this ⊢
                rw [Nat.add_div_of_dvd_left (Dvd.dvd rfl : 3 ^ k ∣ 3 ^ k)] at *
                rw [show (3 ^ k + (n - 3 ^ k)) / 3 ^ t = 3 ^ (k - t) + (n - 3 ^ k) / 3 ^ t from by
                  rw [Nat.add_div_of_dvd_left (by rw [show k = t + (k - t) from by omega]; rw [Nat.pow_add]; exact ⟨3 ^ (k - t), by ring⟩ : 3 ^ t ∣ 3 ^ k)]
                  omega]
                omega
              omega
    -- Now count each half
    rw [hpart, Finset.card_union_eq, d2f_card_aux k, d2f_card_aux k]
    · ring
    · -- Disjoint: left half has all elements < 3^k, right half has all ≥ 3^k
      apply Finset.disjoint_left.mpr
      intro n ⟨hlt, _⟩ ⟨hge, _, _⟩; omega

/-- Block-1 exceptional count ≤ 2^15 for each s. -/
theorem block1_exceptional_le (s : Nat) :
    ((Finset.range (3 ^ 15)).filter fun r => noDigit2 (block1Val s r)).card ≤ 2 ^ 15 := by
  have hinj : ∀ r₁ r₂, r₁ < 3 ^ 15 → r₂ < 3 ^ 15 →
      block1Val s r₁ = block1Val s r₂ → r₁ = r₂ :=
    fun r₁ r₂ h₁ h₂ h => full_injective s r₁ r₂ h₁ h₂ h
  have hpre := filter_preimage_le_of_injOn hinj noDigit2
  have hcard : ((Finset.range (3 ^ 15)).filter noDigit2).card = 2 ^ 15 := by
    unfold noDigit2; exact d2f_card_aux 15
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
    rw [show 2 ^ (s + P * (n + 1)) = 2 ^ (s + P * n) * 2 ^ P from by
      rw [show s + P * (n + 1) = s + P * n + P from by ring, Nat.pow_add]
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
theorem block3_caught_0 : checkBlock3All 0 = true := by native_decide

/-- Verify: for s=2, no residue has noDigit2 in all three blocks. -/
theorem block3_caught_2 : checkBlock3All 2 = true := by native_decide

/-- Verify: for s=8, no residue has noDigit2 in all three blocks. -/
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
        rw [block1_eq_loop s r v30 hv30] at hb1
        rw [block2_eq_loop s r v45 hv45] at hb2
        rw [block3_eq_loop s r v60 hv60] at hb3
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
  have h1 : (2 ^ P) ^ (3 ^ 30) % 3 ^ 45 = ((2 ^ P) % 3 ^ 45) ^ (3 ^ 30) % 3 ^ 45 := Nat.pow_mod ..
  have h1b : ((2 ^ P) % 3 ^ 45) ^ (3 ^ 30) % 3 ^ 45 = pow2Pmod45 ^ (3 ^ 30) % 3 ^ 45 := by
    rw [← pow2Pmod45_eq]
  have h2 : pow2Pmod45 ^ (3 ^ 30) % 3 ^ 45 = pow2ModAux (3 ^ 30) pow2Pmod45 (3 ^ 45) :=
    (pow2ModAux_eq' (3 ^ 30) pow2Pmod45 (3 ^ 45)).symm
  have h3 : pow2ModAux (3 ^ 30) pow2Pmod45 (3 ^ 45) = 1 := by native_decide
  exact h1.trans (h1b.trans (h2.trans h3))

/-- Period of block3: (2^P)^(3^45) ≡ 1 (mod 3^60).
    Proof: reduce to pow2ModAux + native_decide (term-level composition). -/
theorem powP_period_block3 : (2 ^ P) ^ (3 ^ 45) % 3 ^ 60 = 1 := by
  have h1 : (2 ^ P) ^ (3 ^ 45) % 3 ^ 60 = ((2 ^ P) % 3 ^ 60) ^ (3 ^ 45) % 3 ^ 60 := Nat.pow_mod ..
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
    rw [show 2 ^ (P * 3 ^ 15) = (2 ^ P) ^ (3 ^ 15) from Nat.pow_mul 2 P (3 ^ 15)]
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
    rw [show 2 ^ (P * 3 ^ 30) = (2 ^ P) ^ (3 ^ 30) from Nat.pow_mul 2 P (3 ^ 30)]
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
    rw [show 2 ^ (P * 3 ^ 45) = (2 ^ P) ^ (3 ^ 45) from Nat.pow_mul 2 P (3 ^ 45)]
    rw [Nat.pow_mod, powP_period_block3, Nat.one_pow]; norm_num
  rw [← Nat.mul_mod_mod, hper, Nat.mul_one]

end ErdosTernary.BlockClassification
