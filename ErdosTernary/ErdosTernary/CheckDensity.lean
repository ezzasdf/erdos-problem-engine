import Mathlib.Tactic
import Mathlib.Data.Set.Card
import ErdosTernary.Narkiewicz
import ErdosTernary.SayeLemma

namespace TestDensity

open Narkiewicz
open ErdosTernary.SayeLemma

def digitPeriod (k : ℕ) : ℕ := 2 * 3 ^ k

-- digit₃ n k = ternaryDigit n (k+1)
lemma digit3_eq_ternary (n k : Nat) : digit₃ n k = ternaryDigit n (k + 1) := by
  simp [digit₃, ternaryDigit]

-- u (k+1) = 3 * u k
lemma u_succ_mul (k : Nat) (hk : k ≥ 1) : u (k + 1) = 3 * u k := by
  unfold u
  rw [show (k + 1) - 1 = k from by omega]
  rw [show 3 * (2 * 3 ^ (k - 1)) = 2 * 3 ^ k from by
    rw [show 3 ^ k = 3 ^ (k - 1) * 3 from by
      conv_lhs => rw [show k = (k - 1) + 1 from by omega]
      rw [pow_succ]]
    ring]

-- shifting exponent by one period u(k+1) does not change digit k
lemma digit_shift_one (k n : Nat) (hk : k ≥ 1) :
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
lemma digit_shift_period (k n m : Nat) (hk : k ≥ 1) :
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
lemma digit_mod3_reduce (k i j : Nat) (hk : k ≥ 1) :
    digit₃ (2 ^ (i * u k + j)) k = digit₃ (2 ^ (i % 3 * u k + j)) k := by
  have hq : i = 3 * (i / 3) + i % 3 := by omega
  conv_lhs => rw [hq]
  rw [show (3 * (i / 3) + i % 3) * u k + j = (i % 3 * u k + j) + (i / 3) * (3 * u k) from by ring]
  rw [← u_succ_mul k hk]
  exact digit_shift_period k (i % 3 * u k + j) (i / 3) hk

-- Saye lemma in digit₃ form, for the digit at position k with step u_k
lemma digit_saye (k r j : Nat) (hk : k ≥ 1) (hr : r ≤ 2) :
    digit₃ (2 ^ (r * u k + j)) k = (digit₃ (2 ^ j) k + r * d1 j) % 3 := by
  rw [digit3_eq_ternary, digit3_eq_ternary (2 ^ j) k]
  exact saye_main_lemma k r j hk hr

-- counting {i < 9 : Q (i%3)} = 3·{r < 3 : Q r}
lemma card_mod3_nine (Q : Nat → Prop) [DecidablePred Q] :
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
lemma inner_count (k a : Nat) (hk : k ≥ 1) :
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
lemma fiber_card (k a : Nat) (hk : k ≥ 1) (ha : a < u k) :
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
lemma count_window_eq_sum (k : Nat) (hk : k ≥ 1) :
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

theorem count_digit2_in_period (k : Nat) (hk : k ≥ 1) :
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

end TestDensity