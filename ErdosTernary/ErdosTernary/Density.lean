/-
  Density Zero Theorem for the Erdős Ternary Conjecture.

  Proves: The set S = {n ∈ ℕ : 2ⁿ has no digit 2 in its ternary expansion}
  has natural density 0.

  Proof strategy:
  1. Single-position density: for each k ≥ 1, exactly 1/3 of the values
     n ∈ [0, 2·3^k) have digit_k(2^n) = 2
  2. Joint density bound: density(no 2 in first K+1 digits) = (2/3)^K
  3. Density zero: for any ε > 0, pick K with (2/3)^K < ε
-/

import Mathlib.Tactic
import ErdosTernary.Narkiewicz
import ErdosTernary.SayeLemma

namespace ErdosTernary.Density

open Narkiewicz
open ErdosTernary.SayeLemma

/-! ## Setup -/

/-- The digit-period of digit₃(2^n) k: the order of 2 mod 3^{k+1}, which is 2·3^k. -/
def digitPeriod (k : ℕ) : ℕ := 2 * 3 ^ k

private theorem digitPeriod_pos {k : ℕ} (hk : k ≥ 1) : 0 < digitPeriod k := by
  unfold digitPeriod; positivity

private theorem digitPeriod_eq (k : ℕ) : digitPeriod k = 2 * 3 ^ k := rfl

/-! ## Layer 0: Digit arithmetic helpers -/

/-- digit₃(3·y + s) (k+1) = digit₃ y k, when s < 3. -/
private theorem digit₃_mul_add (y s k : ℕ) (hs : s < 3) :
    digit₃ (3 * y + s) (k + 1) = digit₃ y k := by
  simp only [digit₃]
  rw [show 3 ^ (k + 1) = 3 * 3 ^ k from by rw [pow_succ, mul_comm]]
  have hy : y % 3 ^ k < 3 ^ k := Nat.mod_lt _ (by positivity)
  have hrem : 3 * (y % 3 ^ k) + s < 3 * 3 ^ k := by nlinarith
  have hdiv : (3 * y + s) / (3 * 3 ^ k) = y / 3 ^ k := by
    rw [show 3 * y + s = (3 * (y % 3 ^ k) + s) + (y / 3 ^ k) * (3 * 3 ^ k) from by
      conv_lhs => rw [show y = 3 ^ k * (y / 3 ^ k) + y % 3 ^ k from (Nat.div_add_mod y (3 ^ k)).symm]
      ring]
    rw [Nat.add_mul_div_right _ (y / 3 ^ k) (by positivity : 0 < 3 * 3 ^ k)]
    rw [Nat.div_eq_of_lt hrem, zero_add]
  rw [hdiv]


/-! ## Layer 2: Single-position count in one digit-period -/

/-- digit₃ n k = ternaryDigit n (k+1) -/
private lemma digit3_eq_ternary (n k : Nat) : digit₃ n k = ternaryDigit n (k + 1) := by
  simp [digit₃, ternaryDigit]

-- u (k+1) = 3 * u k
private lemma u_succ_mul (k : Nat) (hk : k ≥ 1) : u (k + 1) = 3 * u k := by
  unfold u
  rw [show (k + 1) - 1 = k from by omega]
  rw [show 3 * (2 * 3 ^ (k - 1)) = 2 * 3 ^ k from by
    rw [show 3 ^ k = 3 ^ (k - 1) * 3 from by
      conv_lhs => rw [show k = (k - 1) + 1 from by omega]
      rw [pow_succ]]
    ring]

-- shifting exponent by one period u(k+1) does not change digit k
private lemma digit_shift_one (k n : Nat) (hk : k ≥ 1) :
    digit₃ (2 ^ (n + u (k + 1))) k = digit₃ (2 ^ n) k := by
  unfold digit₃
  rw [Nat.pow_add]
  have hu : 2 ^ u (k + 1) % 3 ^ (k + 1) = 1 := by exact pow_u_mod (k + 1) (by omega)
  obtain ⟨t, ht⟩ : ∃ t, 2 ^ u (k + 1) = 1 + t * 3 ^ (k + 1) := by
    refine ⟨2 ^ u (k + 1) / 3 ^ (k + 1), ?_⟩
    have hdm := Nat.div_add_mod (2 ^ u (k + 1)) (3 ^ (k + 1))
    rw [hu] at hdm
    rw [show 3 ^ (k + 1) * (2 ^ u (k + 1) / 3 ^ (k + 1)) = (2 ^ u (k + 1) / 3 ^ (k + 1)) * 3 ^ (k + 1)
      from by rw [mul_comm]] at hdm
    rw [show 1 + (2 ^ u (k + 1) / 3 ^ (k + 1)) * 3 ^ (k + 1) = (2 ^ u (k + 1) / 3 ^ (k + 1)) * 3 ^ (k + 1) + 1 from by omega]
    exact hdm.symm
  rw [ht]
  have hdiv : (2 ^ n * (1 + t * 3 ^ (k + 1))) / 3 ^ k = 2 ^ n / 3 ^ k + 2 ^ n * t * 3 := by
    rw [show 3 ^ (k + 1) = 3 * 3 ^ k from by rw [pow_succ, mul_comm]]
    rw [show 2 ^ n * (1 + t * (3 * 3 ^ k)) = 2 ^ n + (2 ^ n * (t * 3)) * 3 ^ k from by ring]
    rw [Nat.add_mul_div_right (2 ^ n) (2 ^ n * (t * 3)) (by omega : 0 < 3 ^ k)]
    ring
  rw [hdiv]
  rw [Nat.add_mod]
  rw [show (2 ^ n * t * 3) % 3 = 0 from by
    exact Nat.mod_eq_zero_of_dvd ⟨2 ^ n * t, by ring⟩]
  simp

-- shifting exponent by a multiple of the period does not change digit k
private lemma digit_shift_period (k n m : Nat) (hk : k ≥ 1) :
    digit₃ (2 ^ (n + m * u (k + 1))) k = digit₃ (2 ^ n) k := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show n + (m + 1) * u (k + 1) = n + m * u (k + 1) + u (k + 1) from by ring]
    rw [Nat.pow_add]
    rw [show 2 ^ (n + m * u (k + 1)) * 2 ^ u (k + 1) =
        2 ^ ((n + m * u (k + 1)) + u (k + 1)) from by rw [← Nat.pow_add]]
    rw [digit_shift_one k (n + m * u (k + 1)) hk]
    exact ih

-- digit k of 2^(i·u_k + j) depends only on i mod 3
private lemma digit_mod3_reduce (k i j : Nat) (hk : k ≥ 1) :
    digit₃ (2 ^ (i * u k + j)) k = digit₃ (2 ^ (i % 3 * u k + j)) k := by
  have hq : i = 3 * (i / 3) + i % 3 := by omega
  conv_lhs => rw [hq]
  rw [show (3 * (i / 3) + i % 3) * u k + j = (i % 3 * u k + j) + (i / 3) * (3 * u k) from by ring]
  rw [← u_succ_mul k hk]
  exact digit_shift_period k (i % 3 * u k + j) (i / 3) hk

-- Saye lemma in digit₃ form, for the digit at position k with step u_k
private lemma digit_saye (k r j : Nat) (hk : k ≥ 1) (hr : r ≤ 2) :
    digit₃ (2 ^ (r * u k + j)) k = (digit₃ (2 ^ j) k + r * d1 j) % 3 := by
  rw [digit3_eq_ternary, digit3_eq_ternary (2 ^ j) k]
  exact saye_main_lemma k r j hk hr

-- counting {i < 9 : Q (i%3)} = 3·{r < 3 : Q r}
private lemma card_mod3_nine (Q : Nat → Prop) [DecidablePred Q] :
    ((Finset.range 9).filter (fun i => Q (i % 3))).card = 3 * ((Finset.range 3).filter Q).card := by
  have hsigma : ((Finset.range 3).sigma (fun _ : Nat => (Finset.range 3).filter Q)).card
      = ∑ x in Finset.range 3, ((Finset.range 3).filter Q).card :=
    Finset.card_sigma _ _
  have hbij : ((Finset.range 3).sigma (fun _ : Nat => (Finset.range 3).filter Q)).card
      = ((Finset.range 9).filter (fun i => Q (i % 3))).card := by
    apply Finset.card_bij (fun p hp => 3 * p.1 + p.2)
    · intro p hp
      have hp1 : p.1 < 3 := by simpa using (Finset.mem_sigma.mp hp).1
      have hp2 : p.2 ∈ (Finset.range 3).filter Q := (Finset.mem_sigma.mp hp).2
      have hp2a : p.2 < 3 := by simpa using (Finset.mem_filter.mp hp2).1
      have hp2b : Q p.2 := (Finset.mem_filter.mp hp2).2
      apply Finset.mem_filter.mpr
      constructor
      · have : 3 * p.1 + p.2 < 9 := by omega
        simpa using this
      · rw [show (3 * p.1 + p.2) % 3 = p.2 % 3 from by
          rw [Nat.add_mod]
          have hz : (3 * p.1) % 3 = 0 := by exact Nat.mod_eq_zero_of_dvd ⟨p.1, by ring⟩
          rw [hz, zero_add, Nat.mod_mod]]
        rw [show p.2 % 3 = p.2 from Nat.mod_eq_of_lt hp2a]
        exact hp2b
    · intro p hp q hq h
      cases p with
      | mk p1 p2 =>
        cases q with
        | mk q1 q2 =>
          have hp2a : p2 < 3 := by
            simpa using (Finset.mem_filter.mp (Finset.mem_sigma.mp hp).2).1
          have hq2a : q2 < 3 := by
            simpa using (Finset.mem_filter.mp (Finset.mem_sigma.mp hq).2).1
          have hp1 : p1 < 3 := by
            simpa using (Finset.mem_sigma.mp hp).1
          have hq1 : q1 < 3 := by
            simpa using (Finset.mem_sigma.mp hq).1
          change 3 * p1 + p2 = 3 * q1 + q2 at h
          have h1 : p1 = q1 := by omega
          have h2 : p2 = q2 := by omega
          subst h1; subst h2; rfl
    · intro y hy
      have hy1 : y < 9 := by simpa using (Finset.mem_filter.mp hy).1
      have hy2 : Q (y % 3) := (Finset.mem_filter.mp hy).2
      refine ⟨Sigma.mk (y / 3) (y % 3), ?_, ?_⟩
      · apply Finset.mem_sigma.mpr
        constructor
        · simpa using (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 3)).mpr hy1
        · apply Finset.mem_filter.mpr
          constructor
          · simpa using Nat.mod_lt y (by norm_num : 0 < 3)
          · exact hy2
      · rw [show 3 * (y / 3) + y % 3 = y from Nat.div_add_mod y 3]
  rw [← hbij, hsigma]
  rw [Finset.sum_const_nat (m := ((Finset.range 3).filter Q).card) (by intro q hq; rfl)]
  norm_num

-- for each residue a < u_k, exactly 3 of the 9 values i give digit k = 2
private lemma inner_count (k a : Nat) (hk : k ≥ 1) :
    ((Finset.range 9).filter (fun i => digit₃ (2 ^ (i * u k + a)) k = 2)).card = 3 := by
  let Q : Nat → Prop := fun r => digit₃ (2 ^ (r * u k + a)) k = 2
  have hred : ∀ i, i < 9 → (digit₃ (2 ^ (i * u k + a)) k = 2 ↔ Q (i % 3)) := by
    intro i hi
    rw [digit_mod3_reduce k i a hk]
  have hcard : ((Finset.range 9).filter (fun i => digit₃ (2 ^ (i * u k + a)) k = 2)).card
      = ((Finset.range 9).filter (fun i => Q (i % 3))).card := by
    apply Finset.card_congr (fun x hx => x)
    · intro x hx
      have hx1 : x < 9 := by simpa using (Finset.mem_filter.mp hx).1
      have hx2 : digit₃ (2 ^ (x * u k + a)) k = 2 := (Finset.mem_filter.mp hx).2
      rw [hred x hx1] at hx2
      exact Finset.mem_filter.mpr ⟨by simpa using hx1, hx2⟩
    · intro x hx y hy hxy
      exact hxy
    · intro y hy
      have hy1 : y < 9 := by simpa using (Finset.mem_filter.mp hy).1
      have hy2 : Q (y % 3) := (Finset.mem_filter.mp hy).2
      refine ⟨y, ?_, rfl⟩
      apply Finset.mem_filter.mpr
      constructor
      · simpa using hy1
      · exact (hred y hy1).mpr hy2
  have hq1 : ((Finset.range 3).filter Q).card = 1 := by
    have hiff : ∀ r, r < 3 → (Q r ↔ (digit₃ (2 ^ a) k + r * d1 a) % 3 = 2) := by
      intro r hr
      rw [← digit_saye k r a hk (by omega)]
    have hset : (Finset.range 3).filter Q =
        (Finset.range 3).filter (fun r => (digit₃ (2 ^ a) k + r * d1 a) % 3 = 2) := by
      ext r
      constructor
      · intro h
        rcases Finset.mem_filter.mp h with ⟨hr, hQ⟩
        exact Finset.mem_filter.mpr ⟨hr, (hiff r (by simpa using hr)).mp hQ⟩
      · intro h
        rcases Finset.mem_filter.mp h with ⟨hr, hP⟩
        exact Finset.mem_filter.mpr ⟨hr, (hiff r (by simpa using hr)).mpr hP⟩
    rw [hset]
    have h := exact_one_eq (digit₃ (2 ^ a) k) (d1 a) 2 (d1_mod3_ne_zero a) (by norm_num)
    have hset2 : {i : Nat | i < 3 ∧ (digit₃ (2 ^ a) k + i * d1 a) % 3 = 2}
        = ↑((Finset.range 3).filter (fun r => (digit₃ (2 ^ a) k + r * d1 a) % 3 = 2)) := by
      ext r; simp
    rw [← Set.ncard_coe_Finset]
    rw [← hset2]
    exact h
  rw [hcard, card_mod3_nine Q, hq1]

-- one fiber {n < 9·u_k : digit=2 ∧ n mod u_k = a} equals {i < 9 : digit₃(2^(i·u_k+a)) k = 2}
private lemma fiber_card (k a : Nat) (hk : k ≥ 1) (ha : a < u k) :
    (((Finset.range (9 * u k)).filter (fun n => digit₃ (2 ^ n) k = 2)).filter (fun n => n % u k = a)).card
    = ((Finset.range 9).filter (fun i => digit₃ (2 ^ (i * u k + a)) k = 2)).card := by
  have huk : 0 < u k := by unfold u; positivity
  apply Finset.card_bij (fun n hn => n / u k)
  · intro n hn
    have hn1 : n ∈ (Finset.range (9 * u k)).filter (fun n => digit₃ (2 ^ n) k = 2) :=
      (Finset.mem_filter.mp hn).1
    have hn2 : n % u k = a := (Finset.mem_filter.mp hn).2
    have hlt : n < 9 * u k := by simpa using (Finset.mem_filter.mp hn1).1
    have hP : digit₃ (2 ^ n) k = 2 := (Finset.mem_filter.mp hn1).2
    have hn_eq : n = (n / u k) * u k + a := by
      conv_lhs => rw [← Nat.div_add_mod n (u k)]
      rw [hn2]
      ring
    apply Finset.mem_filter.mpr
    constructor
    · have : n / u k < 9 := (Nat.div_lt_iff_lt_mul huk).mpr hlt
      simpa using this
    · rw [hn_eq] at hP
      exact hP
  · intro a1 ha1 a2 ha2 h
    have ha1' : a1 % u k = a := (Finset.mem_filter.mp ha1).2
    have ha2' : a2 % u k = a := (Finset.mem_filter.mp ha2).2
    rw [← Nat.div_add_mod a1 (u k), ← Nat.div_add_mod a2 (u k)]
    rw [ha1', ha2', h]
  · intro b hb
    have hb1 : b < 9 := by simpa using (Finset.mem_filter.mp hb).1
    have hb2 : digit₃ (2 ^ (b * u k + a)) k = 2 := (Finset.mem_filter.mp hb).2
    have hmod : (b * u k + a) % u k = a := by
      rw [Nat.add_mod]
      rw [show (b * u k) % u k = 0 from Nat.mod_eq_zero_of_dvd ⟨b, by ring⟩]
      rw [zero_add]
      rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt ha]
    have hdiv : (b * u k + a) / u k = b := by
      rw [show b * u k + a = a + b * u k from by omega]
      rw [Nat.add_mul_div_right a b huk]
      rw [show a / u k = 0 from Nat.div_eq_of_lt ha, zero_add]
    refine ⟨b * u k + a, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_filter.mpr
        constructor
        · have hlt : b * u k + a < 9 * u k := by
            have hb8 : b ≤ 8 := by omega
            have ha1 : a ≤ u k - 1 := by omega
            nlinarith [hb8, ha1, huk]
          simpa using hlt
        · exact hb2
      · exact hmod
    · rw [hdiv]

-- total count over the window [0, 9·u_k)
private lemma count_window_eq_sum (k : Nat) (hk : k ≥ 1) :
    ((Finset.range (9 * u k)).filter (fun n => digit₃ (2 ^ n) k = 2)).card
    = ∑ a in Finset.range (u k),
        ((Finset.range 9).filter (fun i => digit₃ (2 ^ (i * u k + a)) k = 2)).card := by
  have huk : 0 < u k := by unfold u; positivity
  have hfw := Finset.card_eq_sum_card_fiberwise
      (s := (Finset.range (9 * u k)).filter (fun n => digit₃ (2 ^ n) k = 2))
      (f := fun n => n % u k) (t := Finset.range (u k))
      (by intro n hn; simpa using Nat.mod_lt n huk)
  rw [hfw]
  apply Finset.sum_congr rfl
  intro a ha
  exact fiber_card k a hk (by simpa using ha)

/-- Within the range [0, 2·3^{k+1}), exactly 2·3^k values of n
    satisfy digit₃(2^n) k = 2.

    Proof: Decompose n = i·u_{k+1} + j with i ∈ {0,1,2}, j ∈ [0, u_{k+1}).
    By the Saye lemma, for each j, as i varies over {0,1,2}, the digit
    takes all three values {0,1,2}. So exactly 1 out of 3 gives digit=2.
    Total = u_{k+1} = 2·3^k = 2·3^{k+1}/3. -/
theorem count_digit2_in_period (k : ℕ) (hk : k ≥ 1) :
    ((Finset.range (digitPeriod (k + 1))).filter (fun n => digit₃ (2 ^ n) k = 2)).card
      = digitPeriod (k + 1) / 3 := by
  unfold digitPeriod
  rw [show 2 * 3 ^ (k + 1) = 9 * u k from by
    unfold u
    rw [show 3 ^ (k + 1) = 9 * 3 ^ (k - 1) from by
      rw [show k + 1 = (k - 1) + 2 from by omega, pow_add]
      norm_num
      ring]
    ring]
  rw [count_window_eq_sum k hk]
  rw [show (∑ a in Finset.range (u k),
        ((Finset.range 9).filter (fun i => digit₃ (2 ^ (i * u k + a)) k = 2)).card) = 3 * u k from by
    rw [Finset.sum_const_nat (m := 3) (by intro a ha; exact inner_count k a hk)]
    simp [Nat.mul_comm]]
  rw [show (9 * u k) / 3 = 2 * 3 ^ k from by
    rw [show 9 * u k = 3 * (3 * u k) from by ring]
    rw [Nat.mul_div_right _ (by norm_num : 0 < 3)]
    rw [show 3 * u k = 2 * 3 ^ k from by
      unfold u
      rw [show 3 * (2 * 3 ^ (k - 1)) = 2 * 3 ^ k from by
        rw [show 3 ^ k = 3 ^ (k - 1) * 3 from by
          conv_lhs => rw [show k = (k - 1) + 1 from by omega]
          rw [pow_succ]]
        ring]]]
  rw [show 3 * u k = 2 * 3 ^ k from by
    unfold u
    rw [show 3 * (2 * 3 ^ (k - 1)) = 2 * 3 ^ k from by
      rw [show 3 ^ k = 3 ^ (k - 1) * 3 from by
        conv_lhs => rw [show k = (k - 1) + 1 from by omega]
        rw [pow_succ]]
      ring]]

/-! ## Layer 3: Asymptotic density of single digit -/

/-- For k ≥ 1, digit k of 2^n is periodic with period digitPeriod (k+1) = 2·3^{k+1}. -/
private lemma digit_periodic (k : Nat) (hk : k ≥ 1) :
    ∀ n, digit₃ (2 ^ (n + digitPeriod (k + 1))) k = digit₃ (2 ^ n) k := by
  intro n
  unfold digitPeriod
  have h3 : 3 ^ (k + 1) = 3 * 3 ^ k := by rw [pow_succ, mul_comm]
  have hP : 2 * 3 ^ (k + 1) = 3 * u (k + 1) := by
    unfold u
    rw [show (k + 1) - 1 = k from by omega]
    nlinarith [h3]
  rw [hP]
  exact digit_shift_period k n 3 hk

/-- Split a periodic set into its first period and the translated rest. -/
private lemma period_filter_split (p : Nat → Prop) [DecidablePred p] {P : Nat}
    (hperiod : ∀ n, p (n + P) ↔ p n) {M : Nat} (hM : P ≤ M) :
    ((Finset.range M).filter p).card =
      ((Finset.range P).filter p).card + ((Finset.range (M - P)).filter p).card := by
  have hr : Finset.range M = Finset.range P ∪ (Finset.range (M - P)).image (fun m => P + m) := by
    ext n
    constructor
    · intro hn
      rcases lt_or_le n P with hnp | hpn
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_range.mpr hnp))
      · have hnm : n - P < M - P := Nat.sub_lt_sub_right hpn (Finset.mem_range.mp hn)
        have hmem : n ∈ (Finset.range (M - P)).image (fun m => P + m) := by
          apply Finset.mem_image.mpr
          exact ⟨n - P, Finset.mem_range.mpr hnm, Nat.add_sub_cancel' hpn⟩
        exact Finset.mem_union.mpr (Or.inr hmem)
    · intro hn
      rcases Finset.mem_union.mp hn with hn1 | hn2
      · exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hn1) hM)
      · rcases Finset.mem_image.mp hn2 with ⟨m, hm1, hm2⟩
        rw [← hm2]
        exact Finset.mem_range.mpr (by
          simpa [Nat.add_comm] using (Nat.add_lt_of_lt_sub (Finset.mem_range.mp hm1)))
  rw [hr, Finset.filter_union]
  have hdisj : Disjoint (Finset.filter p (Finset.range P))
      (Finset.filter p ((Finset.range (M - P)).image (fun m => P + m))) := by
    rw [Finset.disjoint_left]
    intro n hn hn2
    rcases Finset.mem_filter.mp hn with ⟨hn1, _⟩
    rcases Finset.mem_filter.mp hn2 with ⟨hn2a, _⟩
    rcases Finset.mem_image.mp hn2a with ⟨m, hm1, hm2⟩
    have hlt : P + m < P := by
      rw [hm2]
      exact Finset.mem_range.mp hn1
    omega
  rw [Finset.card_union_of_disjoint hdisj]
  congr 1
  rw [Finset.filter_image, Finset.card_image_of_injOn]
  · congr 1
    apply Finset.filter_congr
    intro m hm
    simpa [Nat.add_comm] using hperiod m
  · intro x hx y hy hxy
    change P + x = P + y at hxy
    exact Nat.add_left_cancel hxy

/-- Generic two-sided count bound for a set that is periodic with period P.
    If c = |{n < P : p n}| then for all N:
    (N/P)·c ≤ |{n < N : p n}| ≤ (N/P)·c + P. -/
private lemma period_count_bounds (p : Nat → Prop) [DecidablePred p] {P : Nat}
    (hP : P ≥ 1) (hperiod : ∀ n, p (n + P) ↔ p n) :
    ∀ N, ((Finset.range N).filter p).card ≤
        (N / P) * ((Finset.range P).filter p).card + P ∧
        (N / P) * ((Finset.range P).filter p).card ≤
        ((Finset.range N).filter p).card := by
  let c := ((Finset.range P).filter p).card
  have hc : c = ((Finset.range P).filter p).card := rfl
  have hsplit : ∀ M, P ≤ M →
      ((Finset.range M).filter p).card = c + ((Finset.range (M - P)).filter p).card := by
    intro M hM
    simpa [c] using period_filter_split p hperiod hM
  have hmain : ∀ N, ((Finset.range N).filter p).card ≤ (N / P) * c + P ∧
      (N / P) * c ≤ ((Finset.range N).filter p).card := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      by_cases hNP : P ≤ N
      · have hsp := hsplit N hNP
        have hdiv : N / P = (N - P) / P + 1 := by
          calc
            N / P = ((N - P) + P) / P := by
              conv_lhs => rw [show N = (N - P) + P from by omega]
            _ = (N - P) / P + 1 := Nat.add_div_right (N - P) (by omega : 0 < P)
        have hIH := ih (N - P) (by omega)
        constructor
        · calc
            ((Finset.range N).filter p).card = c + ((Finset.range (N - P)).filter p).card := hsp
            _ ≤ c + ((N - P) / P * c + P) := by omega
            _ = (N / P) * c + P := by rw [hdiv]; ring
        · calc
            (N / P) * c = ((N - P) / P + 1) * c := by rw [hdiv]
            _ = (N - P) / P * c + c := by ring
            _ ≤ ((Finset.range (N - P)).filter p).card + c := by omega
            _ = ((Finset.range N).filter p).card := by omega
      · have hdiv : N / P = 0 := Nat.div_eq_of_lt (by omega)
        constructor
        · rw [hdiv]
          have hcN : ((Finset.range N).filter p).card ≤ N := by
            simpa using (Finset.card_le_card (Finset.filter_subset p (Finset.range N)))
          omega
        · rw [hdiv]
          simp
  intro N
  rw [← hc]
  exact hmain N

/-- For k ≥ 1, the density of {n : digit₃(2^n) k = 2} is exactly 1/3. -/
theorem density_digit2_eq_third (k : ℕ) (hk : k ≥ 1) :
    ∀ ε > 0, ∃ N₀, ∀ N ≥ N₀,
      |(((Finset.range N).filter (fun n => digit₃ (2 ^ n) k = 2)).card : ℝ) / ↑N - 1/3| < ε := by
  intro ε hε
  set P : ℕ := digitPeriod (k + 1) with hPdef
  have hP1 : P ≥ 1 := by
    rw [hPdef]
    unfold digitPeriod
    have h : 0 < 2 * 3 ^ (k + 1) := by positivity
    omega
  have hper : ∀ n, (fun m => digit₃ (2 ^ m) k = 2) (n + P) ↔
      (fun m => digit₃ (2 ^ m) k = 2) n := by
    intro n
    simpa [hPdef] using (Iff.of_eq (congrArg (fun x => x = 2) (digit_periodic k hk n)))
  have hb := period_count_bounds (fun m => digit₃ (2 ^ m) k = 2) hP1 hper
  have hc : ((Finset.range P).filter (fun n => digit₃ (2 ^ n) k = 2)).card = P / 3 := by
    rw [hPdef]
    exact count_digit2_in_period k hk
  have hPmod : P % 3 = 0 := by
    rw [hPdef]
    unfold digitPeriod
    rw [show 2 * 3 ^ (k + 1) = 3 * (2 * 3 ^ k) from by
      rw [pow_succ]
      ring]
    exact Nat.mod_eq_zero_of_dvd ⟨2 * 3 ^ k, rfl⟩
  have h3P : (P / 3) * 3 = P := by
    have := Nat.div_add_mod P 3
    rw [hPmod, add_zero] at this
    rw [mul_comm] at this
    exact this
  have hmain : ∀ N, 1 ≤ N →
      |(((Finset.range N).filter (fun n => digit₃ (2 ^ n) k = 2)).card : ℝ) / ↑N - (1 : ℝ)/3|
        ≤ (P : ℝ) / (N : ℝ) := by
    intro N hN1
    set A : ℕ := ((Finset.range N).filter (fun n => digit₃ (2 ^ n) k = 2)).card with hA
    set c : ℕ := P / 3 with hcdef
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    have hPpos : (0 : ℝ) < (P : ℝ) := by exact_mod_cast (by omega : 0 < P)
    have hccard : c = ((Finset.range P).filter (fun n => digit₃ (2 ^ n) k = 2)).card := by
      rw [hc]
    have hAub : A ≤ (N / P) * c + P := by
      have := hb N
      rw [← hA, ← hccard] at this
      exact this.1
    have hAlb : (N / P) * c ≤ A := by
      have := hb N
      rw [← hA, ← hccard] at this
      exact this.2
    have h3c : 3 * c = P := by
      rw [mul_comm]
      exact h3P
    have hqP : ((N / P : ℕ) : ℝ) * (P : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast (Nat.div_mul_le_self N P)
    have hAubR : (A : ℝ) ≤ ((N / P : ℕ) : ℝ) * (c : ℝ) + (P : ℝ) := by
      exact_mod_cast hAub
    have hAlbR : ((N / P : ℕ) : ℝ) * (c : ℝ) ≤ (A : ℝ) := by
      exact_mod_cast hAlb
    have h3c' : (c : ℝ) * 3 = (P : ℝ) := by
      rw [mul_comm]
      exact_mod_cast h3c
    have hNlt : (N : ℝ) < ((N / P : ℕ) : ℝ) * (P : ℝ) + (P : ℝ) := by
      have hdiv := Nat.div_add_mod N P
      have hmodR : ((N % P : ℕ) : ℝ) < (P : ℝ) := by
        exact_mod_cast (Nat.mod_lt N (by omega : 0 < P))
      have hdivR : (P : ℝ) * ((N / P : ℕ) : ℝ) + ((N % P : ℕ) : ℝ) = (N : ℝ) := by
        exact_mod_cast hdiv
      nlinarith [hmodR, hdivR]
    have hu : (A : ℝ) / (N : ℝ) - (1 : ℝ) / 3 ≤ (P : ℝ) / (N : ℝ) := by
      have h3ub : 3 * (A : ℝ) - (N : ℝ) ≤ 3 * (P : ℝ) := by
        have h1 : 3 * (A : ℝ) ≤ 3 * ((((N / P : ℕ) : ℝ) * (c : ℝ))) + 3 * (P : ℝ) := by
          nlinarith [hAubR]
        have hq : 3 * ((((N / P : ℕ) : ℝ) * (c : ℝ))) + 3 * (P : ℝ) =
            ((N / P : ℕ) : ℝ) * (P : ℝ) + 3 * (P : ℝ) := by
          rw [show (3 : ℝ) * ((((N / P : ℕ) : ℝ) * (c : ℝ))) = ((N / P : ℕ) : ℝ) * ((c : ℝ) * 3) from by ring]
          rw [h3c']
        nlinarith [h1, hq, hqP]
      have h3Npos : (0 : ℝ) < 3 * (N : ℝ) := by positivity
      have hNne : (N : ℝ) ≠ 0 := by positivity
      calc
        (A : ℝ) / (N : ℝ) - (1 : ℝ) / 3 = (3 * (A : ℝ) - (N : ℝ)) / (3 * (N : ℝ)) := by
          field_simp [hNne]
          ring
        _ ≤ (P : ℝ) / (N : ℝ) := by
          rw [div_le_iff₀' h3Npos]
          have hP : (3 * (N : ℝ) : ℝ) * ((P : ℝ) / (N : ℝ)) = 3 * (P : ℝ) := by
            rw [show (3 * (N : ℝ) : ℝ) * ((P : ℝ) / (N : ℝ)) = 3 * ((N : ℝ) * ((P : ℝ) / (N : ℝ))) from by ring]
            rw [mul_div_cancel₀ (P : ℝ) hNne]
          rw [hP]
          exact h3ub
    have hl : (1 : ℝ) / 3 - (A : ℝ) / (N : ℝ) ≤ (P : ℝ) / (N : ℝ) := by
      have h3lb : (N : ℝ) - 3 * (A : ℝ) ≤ 3 * (P : ℝ) := by
        have h1 : 3 * ((((N / P : ℕ) : ℝ) * (c : ℝ))) ≤ 3 * (A : ℝ) := by
          exact mul_le_mul_of_nonneg_left hAlbR (by positivity)
        have hq : 3 * ((((N / P : ℕ) : ℝ) * (c : ℝ))) = ((N / P : ℕ) : ℝ) * (P : ℝ) := by
          rw [show (3 : ℝ) * ((((N / P : ℕ) : ℝ) * (c : ℝ))) = ((N / P : ℕ) : ℝ) * ((c : ℝ) * 3) from by ring]
          rw [h3c']
        rw [hq] at h1
        have h2 : (N : ℝ) - ((N / P : ℕ) : ℝ) * (P : ℝ) < (P : ℝ) := by
          linarith [hNlt]
        have h3 : (N : ℝ) - 3 * (A : ℝ) ≤ (N : ℝ) - ((N / P : ℕ) : ℝ) * (P : ℝ) := by
          exact sub_le_sub_left h1 (N : ℝ)
        have h4 : (N : ℝ) - ((N / P : ℕ) : ℝ) * (P : ℝ) < 3 * (P : ℝ) := by
          calc
            (N : ℝ) - ((N / P : ℕ) : ℝ) * (P : ℝ) < (P : ℝ) := h2
            _ ≤ 3 * (P : ℝ) := by
              simpa [mul_comm] using (mul_le_mul_of_nonneg_left (by norm_num : (1 : ℝ) ≤ 3) (le_of_lt hPpos))
        exact le_of_lt (lt_of_le_of_lt h3 h4)
      have h3Npos : (0 : ℝ) < 3 * (N : ℝ) := by positivity
      have hNne : (N : ℝ) ≠ 0 := by positivity
      calc
        (1 : ℝ) / 3 - (A : ℝ) / (N : ℝ) = ((N : ℝ) - 3 * (A : ℝ)) / (3 * (N : ℝ)) := by
          field_simp [hNne]
        _ ≤ (P : ℝ) / (N : ℝ) := by
          rw [div_le_iff₀' h3Npos]
          have hP : (3 * (N : ℝ) : ℝ) * ((P : ℝ) / (N : ℝ)) = 3 * (P : ℝ) := by
            rw [show (3 * (N : ℝ) : ℝ) * ((P : ℝ) / (N : ℝ)) = 3 * ((N : ℝ) * ((P : ℝ) / (N : ℝ))) from by ring]
            rw [mul_div_cancel₀ (P : ℝ) hNne]
          rw [hP]
          exact h3lb
    rw [abs_le]
    constructor
    · linarith [hl]
    · exact hu
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt ((P : ℝ) / ε)
  refine ⟨N₀, fun N hN => ?_⟩
  have hbig : (P : ℝ) / ε < (N₀ : ℝ) := hN₀
  have hPε : (0 : ℝ) < (P : ℝ) / ε := by positivity
  have hN0pos : (0 : ℝ) < (N₀ : ℝ) := by linarith
  have hN1 : 1 ≤ N := le_trans (by exact_mod_cast (by linarith : (0 : ℝ) < (N₀ : ℝ)) : 1 ≤ N₀) hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hmainN := hmain N hN1
  have hbound : (P : ℝ) / (N : ℝ) < ε := by
    have hPεN : (P : ℝ) / ε < (N : ℝ) := lt_of_lt_of_le hbig (by exact_mod_cast hN)
    rw [div_lt_iff hNpos]
    have hm := mul_lt_mul_of_pos_right hPεN hε
    rw [div_mul_cancel₀ (P : ℝ) hε.ne'] at hm
    nlinarith [hm]
  exact lt_of_le_of_lt hmainN hbound

/-! ## Layer 4: Joint density bound -/

/-- no digit 2 in positions 0..K of the ternary expansion of 2^n -/
private def no_two (K n : Nat) : Prop := ∀ k ≤ K, digit₃ (2 ^ n) k ≠ 2

private instance noTwoDecidable (K n : Nat) : Decidable (no_two K n) := by
  unfold no_two
  infer_instance

private lemma u_mul_exp (k K : Nat) (hk : k ≤ K) :
    u (K + 1) = 3 ^ (K - k) * u (k + 1) := by
  unfold u
  rw [show (K + 1) - 1 = K from by omega]
  rw [show (k + 1) - 1 = k from by omega]
  rw [show 3 ^ K = 3 ^ (K - k) * 3 ^ k from by
    rw [← pow_add]
    congr 1
    omega]
  ring

private lemma two_pow_u_mod_three (K : Nat) : 2 ^ u (K + 1) % 3 = 1 := by
  have h := d1_pow_two_even (3 ^ K)
  unfold d1 at h
  unfold ternaryDigit at h
  simp at h
  rw [show u (K + 1) = 2 * 3 ^ K from by unfold u; rw [show (K + 1) - 1 = K from by omega]]
  exact h

-- shifting exponent by the joint period u(K+1) does not change digits 0..K
private lemma digit_shift_joint (K n : Nat) :
    ∀ k ≤ K, digit₃ (2 ^ (n + u (K + 1))) k = digit₃ (2 ^ n) k := by
  intro k hk
  by_cases hk0 : k = 0
  · subst hk0
    rw [digit₃, digit₃]
    simp
    rw [Nat.pow_add]
    rw [Nat.mul_mod]
    rw [two_pow_u_mod_three K]
    rw [show (2 ^ n % 3) * 1 % 3 = 2 ^ n % 3 from by rw [mul_one, Nat.mod_mod]]
  · have hk1 : k ≥ 1 := by omega
    rw [u_mul_exp k K hk]
    exact digit_shift_period k n (3 ^ (K - k)) hk1

private lemma joint_periodic (K n : Nat) : no_two K (n + u (K + 1)) ↔ no_two K n := by
  have hsh := digit_shift_joint K n
  constructor
  · intro h k hk
    rw [← hsh k hk]
    exact h k hk
  · intro h k hk
    rw [hsh k hk]
    exact h k hk

private lemma digit_shift_joint_mul (K n m : Nat) :
    ∀ k ≤ K, digit₃ (2 ^ (n + m * u (K + 1))) k = digit₃ (2 ^ n) k := by
  intro k hk
  induction m with
  | zero => simp
  | succ m ih =>
      rw [show n + (m + 1) * u (K + 1) = (n + m * u (K + 1)) + u (K + 1) from by ring]
      rw [digit_shift_joint K (n + m * u (K + 1)) k hk]
      exact ih

private lemma joint_periodic_mul (K n m : Nat) :
    no_two K (n + m * u (K + 1)) ↔ no_two K n := by
  unfold no_two
  constructor
  · intro h k hk
    rw [← digit_shift_joint_mul K n m k hk]
    exact h k hk
  · intro h k hk
    rw [digit_shift_joint_mul K n m k hk]
    exact h k hk

/-- among q < 3, exactly 2 satisfy (base + q·d) % 3 ≠ 2 -/
private lemma card_ne_two_mod3 (base d : Nat) (hd : d % 3 ≠ 0) :
    ((Finset.range 3).filter (fun q => (base + q * d) % 3 ≠ 2)).card = 2 := by
  have hC : ((Finset.range 3).filter (fun q => (base + q * d) % 3 = 2)).card = 1 := by
    have h := exact_one_eq base d 2 hd (by norm_num)
    have hset2 : {i : Nat | i < 3 ∧ (base + i * d) % 3 = 2}
        = ↑((Finset.range 3).filter (fun q => (base + q * d) % 3 = 2)) := by
      ext i; simp
    rw [← Set.ncard_coe_Finset]
    rw [← hset2]
    exact h
  have hB : ((Finset.range 3).filter (fun q => (base + q * d) % 3 ≠ 2)).card +
      ((Finset.range 3).filter (fun q => (base + q * d) % 3 = 2)).card = 3 := by
    have hdisj : Disjoint ((Finset.range 3).filter (fun q => (base + q * d) % 3 ≠ 2))
        ((Finset.range 3).filter (fun q => (base + q * d) % 3 = 2)) := by
      rw [Finset.disjoint_left]
      intro q h1 h2
      exact (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2
    rw [← Finset.card_union_of_disjoint hdisj]
    have hunion : ((Finset.range 3).filter (fun q => (base + q * d) % 3 ≠ 2)) ∪
        ((Finset.range 3).filter (fun q => (base + q * d) % 3 = 2)) = Finset.range 3 := by
      ext q
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro (h | h) <;> exact h.1
      · intro hq
        by_cases hc : (base + q * d) % 3 = 2
        · exact Or.inr ⟨hq, hc⟩
        · exact Or.inl ⟨hq, hc⟩
    rw [hunion]
    simp
  rw [hC] at hB
  omega

/-- within one period u(K+1), exactly 2^K values have no digit 2 in positions 0..K -/
private lemma period_count (K : Nat) :
    ((Finset.range (u (K + 1))).filter (fun n => no_two K n)).card = 2 ^ K := by
  induction K with
  | zero =>
      rw [show u (0 + 1) = 2 from by norm_num]
      native_decide
  | succ K ih =>
      let P : Nat := u (K + 1)
      let E : Finset Nat := (Finset.range (3 * P)).filter (fun n => no_two (K + 1) n)
      have hPpos : 0 < P := by
        rw [show P = u (K + 1) from rfl]
        unfold u; positivity
      have hP : u (K + 2) = 3 * P := by
        rw [u_succ_mul (K + 1) (by omega : K + 1 ≥ 1)]
      have hsplit : ∀ q j : Nat, ∀ (hj : j < P) (hq : q < 3),
          no_two (K + 1) (q * P + j) ↔
            no_two K j ∧ (digit₃ (2 ^ j) (K + 1) + q * d1 j) % 3 ≠ 2 := by
        intro q j hj hq
        unfold no_two
        have hs1 : (∀ k ≤ K + 1, digit₃ (2 ^ (q * P + j)) k ≠ 2) ↔
            (∀ k ≤ K, digit₃ (2 ^ (q * P + j)) k ≠ 2) ∧ digit₃ (2 ^ (q * P + j)) (K + 1) ≠ 2 := by
          constructor
          · intro h
            constructor
            · intro k hk; exact h k (by omega)
            · exact h (K + 1) (by omega)
          · intro h k hk
            by_cases hk' : k = K + 1
            · subst hk'; exact h.2
            · have hk1 : k ≤ K := by omega
              exact h.1 k hk1
        rw [hs1]
        apply and_congr
        · change (no_two K (q * P + j)) ↔ (no_two K j)
          rw [show q * P + j = j + q * u (K + 1) from by rw [show q * P = q * u (K + 1) from rfl]; omega]
          exact joint_periodic_mul K j q
        · rw [digit_saye (K + 1) q j (by omega) (by omega : q ≤ 2)]
      have hB (j : Nat) (hj : j < P) :
          ((Finset.range 3).filter (fun q => digit₃ (2 ^ (q * P + j)) (K + 1) ≠ 2)).card = 2 := by
        have hset : ((Finset.range 3).filter (fun q => digit₃ (2 ^ (q * P + j)) (K + 1) ≠ 2))
            = ((Finset.range 3).filter (fun q => (digit₃ (2 ^ j) (K + 1) + q * d1 j) % 3 ≠ 2)) := by
          apply Finset.filter_congr
          intro q hq
          have hq1 : q < 3 := by simpa using hq
          rw [digit_saye (K + 1) q j (by omega) (by omega : q ≤ 2)]
        rw [hset]
        exact card_ne_two_mod3 (digit₃ (2 ^ j) (K + 1)) (d1 j) (d1_mod3_ne_zero j)
      have hfib : ∀ j : Nat, j < P →
          (E.filter (fun n => n % P = j)).card = if no_two K j then 2 else 0 := by
        intro j hj
        by_cases hgood : no_two K j
        · simp [hgood]
          have hbij : (E.filter (fun n => n % P = j)).card
              = ((Finset.range 3).filter (fun q => digit₃ (2 ^ (q * P + j)) (K + 1) ≠ 2)).card := by
            apply Finset.card_bij (fun n hn => n / P)
            · intro n hn
              rcases Finset.mem_filter.mp hn with ⟨hnE, hnmod⟩
              rcases Finset.mem_filter.mp hnE with ⟨hnr, hnno⟩
              have hq : n / P < 3 := (Nat.div_lt_iff_lt_mul hPpos).mpr (by simpa using hnr)
              have hn_eq : (n / P) * P + j = n := by
                conv_rhs => rw [show n = P * (n / P) + n % P from (Nat.div_add_mod n P).symm]
                rw [hnmod]
                ring
              apply Finset.mem_filter.mpr
              constructor
              · simpa using hq
              · have hd : digit₃ (2 ^ n) (K + 1) ≠ 2 := hnno (K + 1) (by omega)
                rw [← hn_eq] at hd
                exact hd
            · intro a ha b hb h
              have ha' : a % P = j := (Finset.mem_filter.mp ha).2
              have hb' : b % P = j := (Finset.mem_filter.mp hb).2
              rw [← Nat.div_add_mod a P, ← Nat.div_add_mod b P]
              rw [ha', hb', h]
            · intro b hb
              have hb1 : b < 3 := by simpa using (Finset.mem_filter.mp hb).1
              have hb2 : digit₃ (2 ^ (b * P + j)) (K + 1) ≠ 2 := (Finset.mem_filter.mp hb).2
              have hmod : (b * P + j) % P = j := by
                rw [show b * P + j = j + b * P from by omega]
                rw [Nat.mul_comm b P]
                rw [Nat.add_mul_mod_self_left]
                exact Nat.mod_eq_of_lt hj
              have hdiv : (b * P + j) / P = b := by
                rw [show b * P + j = j + b * P from by omega]
                rw [Nat.add_mul_div_right j b (by omega : 0 < P)]
                rw [show j / P = 0 from Nat.div_eq_of_lt hj, zero_add]
              refine ⟨b * P + j, ?_, hdiv⟩
              apply Finset.mem_filter.mpr
              constructor
              · apply Finset.mem_filter.mpr
                constructor
                · have hlt : b * P + j < 3 * P := by
                    have hb0 : b ≤ 2 := by omega
                    nlinarith [hb0, hj, hPpos]
                  simpa using hlt
                · have hb2' : (digit₃ (2 ^ j) (K + 1) + b * d1 j) % 3 ≠ 2 := by
                    rw [digit_saye (K + 1) b j (by omega) (by omega : b ≤ 2)] at hb2
                    exact hb2
                  exact (hsplit b j hj hb1).mpr ⟨hgood, hb2'⟩
              · exact hmod
          rw [hbij, hB j hj]
        · simp [hgood]
          rw [Finset.filter_eq_empty_iff]
          intro n hn hnmod
          rcases Finset.mem_filter.mp hn with ⟨hnr, hnno⟩
          have hq : n / P < 3 := (Nat.div_lt_iff_lt_mul hPpos).mpr (by simpa using hnr)
          have hn_eq : (n / P) * P + j = n := by
            conv_rhs => rw [show n = P * (n / P) + n % P from (Nat.div_add_mod n P).symm]
            rw [hnmod]
            ring
          have hs := hsplit (n / P) j hj hq
          rw [hn_eq] at hs
          have hno2 := hs.mp hnno
          exact False.elim (hgood hno2.1)
      have hcard : E.card = 2 * ((Finset.range P).filter (fun n => no_two K n)).card := by
        have hfw := Finset.card_eq_sum_card_fiberwise
            (s := E) (f := fun n => n % P) (t := Finset.range P)
            (by intro n hn; simpa using Nat.mod_lt n hPpos)
        rw [hfw]
        rw [Finset.sum_congr rfl (by intro j hj; rw [hfib j (by simpa using hj)])]
        rw [← Finset.sum_filter]
        rw [Finset.sum_const_nat (m := 2) (by intro x hx; rfl)]
        rw [mul_comm]
      have hE : E = (Finset.range (u (K + 2))).filter (fun n => no_two (K + 1) n) := by
        rw [hP]
      rw [← hE]
      rw [hcard]
      rw [ih]
      rw [pow_succ]
      rw [mul_comm]

/-- For each K ≥ 1, the density of {n : ∀k≤K, digit₃(2^n) k ≠ 2} is at most (2/3)^K.

    Proof: Within one period [0, 2·3^K), exactly 2^K values satisfy the condition,
    so the density is at most 2^K/(2·3^K) ≤ (2/3)^K, and the period-count bounds
    (period_count_bounds) control the tail. -/
theorem joint_density_bound (K : Nat) (hK : K ≥ 1) :
    ∀ ε > 0, ∃ N₀, ∀ N ≥ N₀,
      (((Finset.range N).filter (fun n => ∀ k ≤ K, digit₃ (2 ^ n) k ≠ 2)).card : ℝ) / ↑N
      < (2/3 : ℝ) ^ K + ε := by
  intro ε hε
  let P : ℕ := u (K + 1)
  let c : ℕ := 2 ^ K
  have hper : ∀ n, no_two K (n + P) ↔ no_two K n := by
    intro n
    rw [show P = u (K + 1) from rfl]
    exact joint_periodic K n
  have hP1 : P ≥ 1 := by
    rw [show P = u (K + 1) from rfl]
    unfold u
    rw [show (K + 1) - 1 = K from by omega]
    have h : 0 < 2 * 3 ^ K := by positivity
    omega
  have hc : ((Finset.range P).filter (fun n => no_two K n)).card = c := by
    simpa [P] using period_count K
  have hbounds := period_count_bounds (fun n => no_two K n) hP1 hper
  have hmain : ∀ N, 1 ≤ N →
      (((Finset.range N).filter (fun n => no_two K n)).card : ℝ) / ↑N
      ≤ (c : ℝ) / (P : ℝ) + (P : ℝ) / (N : ℝ) := by
    intro N hN1
    have hb := (hbounds N).1
    rw [hc] at hb
    have hbR : (((Finset.range N).filter (fun n => no_two K n)).card : ℝ) ≤
        ((N / P : ℕ) : ℝ) * (c : ℝ) + (P : ℝ) := by
      exact_mod_cast hb
    have hNne : (N : ℝ) ≠ 0 := by positivity
    have hPne : (P : ℝ) ≠ 0 := by positivity
    have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
    have hd : (((Finset.range N).filter (fun n => no_two K n)).card : ℝ) / (N : ℝ)
        ≤ (((N / P : ℕ) : ℝ) * (c : ℝ) + (P : ℝ)) / (N : ℝ) := by
      exact div_le_div_of_le (le_of_lt hNpos) hbR
    have hsplit : (((N / P : ℕ) : ℝ) * (c : ℝ) + (P : ℝ)) / (N : ℝ)
        = ((N / P : ℕ) : ℝ) * (c : ℝ) / (N : ℝ) + (P : ℝ) / (N : ℝ) := by
      rw [add_div]
    have hqP : ((N / P : ℕ) : ℝ) * (P : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast (Nat.div_mul_le_self N P)
    have hqPdiv : ((N / P : ℕ) : ℝ) * (P : ℝ) / (N : ℝ) ≤ 1 := by
      rw [div_le_iff₀' hNpos]
      simpa using hqP
    have hq : ((N / P : ℕ) : ℝ) * (c : ℝ) / (N : ℝ) ≤ (c : ℝ) / (P : ℝ) := by
      have hrew : ((N / P : ℕ) : ℝ) * (c : ℝ) / (N : ℝ)
          = ((N / P : ℕ) : ℝ) * (P : ℝ) / (N : ℝ) * ((c : ℝ) / (P : ℝ)) := by
        field_simp [hNne, hPne]
        ring
      rw [hrew]
      have hc0 : (0 : ℝ) ≤ (c : ℝ) / (P : ℝ) := by positivity
      simpa using (mul_le_mul_of_nonneg_right hqPdiv hc0)
    calc
      (((Finset.range N).filter (fun n => no_two K n)).card : ℝ) / (N : ℝ)
          ≤ ((N / P : ℕ) : ℝ) * (c : ℝ) / (N : ℝ) + (P : ℝ) / (N : ℝ) := by
        rw [← hsplit]
        exact hd
      _ ≤ (c : ℝ) / (P : ℝ) + (P : ℝ) / (N : ℝ) := by
        exact add_le_add_right hq ((P : ℝ) / (N : ℝ))
  have hcP : (c : ℝ) / (P : ℝ) ≤ (2/3 : ℝ) ^ K := by
    have hP : P = 2 * 3 ^ K := by
      rw [show P = u (K + 1) from rfl]
      unfold u; rw [show (K + 1) - 1 = K from by omega]
    rw [hP]
    rw [show c = 2 ^ K from rfl]
    norm_num
    have hden : (0 : ℝ) < (2 : ℝ) * (3 : ℝ) ^ K := by positivity
    have h1 : (2 ^ K : ℝ) / ((2 : ℝ) * (3 : ℝ) ^ K) = (1 / 2 : ℝ) * ((2 : ℝ) / 3) ^ K := by
      rw [div_pow]
      field_simp [hden]
    rw [h1]
    have hpow : (0 : ℝ) ≤ ((2 : ℝ) / 3) ^ K := by positivity
    have hhalf : (1 / 2 : ℝ) ≤ 1 := by norm_num
    have hle := mul_le_mul_of_nonneg_right hhalf hpow
    simpa using hle
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt ((P : ℝ) / ε)
  refine ⟨N₀, fun N hN => ?_⟩
  have hbig : (P : ℝ) / ε < (N₀ : ℝ) := hN₀
  have hN01 : (0 : ℝ) < (N₀ : ℝ) :=
    lt_of_lt_of_le (div_pos (by exact_mod_cast (by omega : 0 < P)) hε) (le_of_lt hN₀)
  have hN0p : 0 < N₀ := by exact_mod_cast hN01
  have hN1 : 1 ≤ N := le_trans (by omega : 1 ≤ N₀) hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hmainN := hmain N hN1
  have hbound : (c : ℝ) / (P : ℝ) + (P : ℝ) / (N : ℝ) < (2/3 : ℝ) ^ K + ε := by
    have hPεN : (P : ℝ) / ε < (N : ℝ) := lt_of_lt_of_le hbig (by exact_mod_cast hN)
    have hPN : (P : ℝ) / (N : ℝ) < ε := by
      rw [div_lt_iff hNpos]
      have hm := mul_lt_mul_of_pos_right hPεN hε
      rw [div_mul_cancel₀ (P : ℝ) hε.ne'] at hm
      nlinarith [hm]
    exact add_lt_add_of_le_of_lt hcP hPN
  exact lt_of_le_of_lt hmainN hbound

/-! ## Layer 5: Density zero -/

/-- For k > n, the ternary digit at position k of 2^n is 0 (since 2^n < 3^k). -/
private lemma digit₃_small_pow_lt (n k : Nat) (hk : n < k) : digit₃ (2 ^ n) k = 0 := by
  rw [digit₃]
  have hlt : 2 ^ n < 3 ^ k := by
    by_cases hn0 : n = 0
    · subst hn0
      have hk1 : k ≠ 0 := by omega
      exact one_lt_pow (by norm_num : (1 : ℕ) < 3) hk1
    · have hn1 : n ≠ 0 := hn0
      have h1 : 2 ^ n < 3 ^ n := Nat.pow_lt_pow_left (by norm_num : (2 : ℕ) < 3) hn1
      have h2 : 3 ^ n ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num : (3 : ℕ) > 0) (by omega : n ≤ k)
      exact lt_of_lt_of_le h1 h2
  rw [Nat.div_eq_of_lt hlt]

/-- The set S = {n : 2ⁿ has no digit 2 in its ternary expansion} has density 0. -/
theorem density_zero :
    ∀ ε > 0, ∃ N₀, ∀ N ≥ N₀,
      (((Finset.range N).filter (fun n => ∀ k ≤ n, digit₃ (2 ^ n) k ≠ 2)).card : ℝ) / ↑N < ε := by
  intro ε hε
  obtain ⟨K0, hK0⟩ : ∃ K, (2/3 : ℝ) ^ K < ε := by
    have h : Filter.Tendsto (fun K => (2/3 : ℝ) ^ K) Filter.atTop (nhds 0) := by
      exact tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by
        rw [abs_of_pos (by norm_num : (0 : ℝ) < 2 / 3)]
        norm_num)
    have hev : ∀ᶠ K in Filter.atTop, (2/3 : ℝ) ^ K < ε := by
      have hmem : ∀ᶠ y : ℝ in nhds (0 : ℝ), y < ε := by
        simpa [Set.mem_Iio] using (Iio_mem_nhds hε : Set.Iio ε ∈ nhds (0 : ℝ))
      exact h.eventually hmem
    rcases hev.exists with ⟨K, hK⟩
    exact ⟨K, hK⟩
  let K : ℕ := K0 + 1
  have hK1 : K ≥ 1 := by omega
  have hKsmall : (2/3 : ℝ) ^ K < ε := by
    dsimp [K]
    calc
      (2/3 : ℝ) ^ (K0 + 1) = (2/3 : ℝ) * (2/3 : ℝ) ^ K0 := by rw [pow_succ]; ring
      _ < (2/3 : ℝ) ^ K0 := by
        have hx : 0 < (2/3 : ℝ) ^ K0 := pow_pos (by norm_num) K0
        nlinarith
      _ < ε := hK0
  obtain ⟨N₀, hN₀⟩ := joint_density_bound K hK1 (ε - (2/3 : ℝ) ^ K) (by linarith)
  exact ⟨max N₀ 1, fun N hN => by
    have hN₀N : N ≥ N₀ := by exact le_trans (Nat.le_max_left _ _) hN
    have := hN₀ N hN₀N
    have hNpos : (0 : ℝ) < (N : ℝ) := by
      have hN1 : 1 ≤ N := le_trans (Nat.le_max_right _ _) hN
      exact_mod_cast (by omega : 0 < N)
    have hlt : (((Finset.range N).filter (fun n => ∀ k ≤ K, digit₃ (2 ^ n) k ≠ 2)).card : ℝ) / ↑N < ε := by
      linarith
    have hsub : (Finset.range N).filter (fun n => ∀ k ≤ n, digit₃ (2 ^ n) k ≠ 2) ⊆
                (Finset.range N).filter (fun n => ∀ k ≤ K, digit₃ (2 ^ n) k ≠ 2) := by
      intro n hn
      rcases Finset.mem_filter.mp hn with ⟨hn1, hn2⟩
      exact Finset.mem_filter.mpr ⟨hn1, fun k hk => by
        by_cases hkn : k ≤ n
        · exact hn2 k hkn
        · have hkg : n < k := by omega
          rw [digit₃_small_pow_lt n k hkg]
          norm_num⟩
    have hcard : (((Finset.range N).filter (fun n => ∀ k ≤ n, digit₃ (2 ^ n) k ≠ 2)).card : ℝ) ≤
                 (((Finset.range N).filter (fun n => ∀ k ≤ K, digit₃ (2 ^ n) k ≠ 2)).card : ℝ) :=
      Nat.cast_le.mpr (Finset.card_le_card hsub)
    have hdiv : (((Finset.range N).filter (fun n => ∀ k ≤ n, digit₃ (2 ^ n) k ≠ 2)).card : ℝ) / (N : ℝ)
        ≤ (((Finset.range N).filter (fun n => ∀ k ≤ K, digit₃ (2 ^ n) k ≠ 2)).card : ℝ) / (N : ℝ) := by
      exact div_le_div_of_nonneg_right hcard (le_of_lt hNpos)
    linarith⟩

end ErdosTernary.Density
