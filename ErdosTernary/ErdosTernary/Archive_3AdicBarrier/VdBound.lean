import Mathlib.Tactic
import ErdosTernary.MomentSystem
import ErdosTernary.TwoAdicObstruction
import ErdosTernary.OddEncObstruction
import ErdosTernary.OddCaseDigit2

/-!
# V(d) ≤ d+3 Bound

Main theorem: for non-zero a : BinVec d, 2^{d+4} does not divide evalP3 a.
-/

namespace VdBound
open MomentSystem
open TwoAdicObstruction (evalBit evalBit_mod evalBit_two_mul evalBit_one_add_mul pow3_eq coprime_dvd_iff
  obstruction_le23)

def NonZeroBinVec (d : ℕ) (a : BinVec d) : Prop :=
  ∃ i : Fin (d + 1), a i ≠ 0

private theorem aVal_le_one {d : ℕ} (a : BinVec d) (i : ℕ) (hi : i < d + 1) :
    aVal a i ≤ 1 := by
  simp only [aVal, dif_pos hi]; have := (a ⟨i, hi⟩).isLt; omega

private theorem sum_powers (n : ℕ) :
    2 * (∑ i in Finset.range n, 3 ^ i) + 1 = 3 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.range_succ, Finset.sum_insert (by simp)]; ring_nf; linarith

private theorem evalP3_le_sum (d : ℕ) (a : BinVec d) :
    evalP3 a ≤ ∑ i in Finset.range (d + 1), 3 ^ i := by
  simp only [evalP3]; apply Finset.sum_le_sum; intro i hi
  rw [Finset.mem_range] at hi
  linarith [Nat.mul_le_mul_right (3 ^ i) (aVal_le_one a i (by omega))]

private theorem evalP3_mul2_add1_le (d : ℕ) (a : BinVec d) :
    evalP3 a * 2 + 1 ≤ 3 ^ (d + 1) := by
  have h1 := evalP3_le_sum d a; have h2 := sum_powers (d + 1); omega

private theorem evalP3_pos {d : ℕ} {a : BinVec d} (hne : NonZeroBinVec d a) : 0 < evalP3 a := by
  obtain ⟨i, hi⟩ := hne; simp only [evalP3]
  rw [Finset.sum_eq_add_sum_diff_singleton (Finset.mem_range.mpr i.isLt)]
  have hv : (a i : ℕ) ≠ 0 := by intro hf; exact hi (Fin.val_injective hf)
  have hvm : 0 < (a i : ℕ) := by omega
  have hpm : 0 < 3 ^ i.val := Nat.pow_pos (by omega)
  have ht : 0 < aVal a i.val * 3 ^ i.val := by
    simp only [aVal, dif_pos i.isLt]; exact Nat.mul_pos hvm hpm
  exact Nat.lt_of_lt_of_le ht (Nat.le_add_right _ _)

private theorem no_pow2_small (d : ℕ) (hd : d ≤ 4) (a : BinVec d) (hne : NonZeroBinVec d a) :
    2 ^ (d + 4) ∣ evalP3 a → False := by
  rintro ⟨k, hk⟩
  have hle := evalP3_mul2_add1_le d a
  have hpos := evalP3_pos hne
  interval_cases d
  all_goals (norm_num at hle hpos hk ⊢; omega)

private def restrict (d : ℕ) (a : BinVec d) : BinVec (d - 1) :=
  fun j => a ⟨j.val, by omega⟩

private theorem restrict_aVal (d : ℕ) (a : BinVec d) (i : ℕ) (hi : i < d) :
    aVal (restrict d a) i = aVal a i := by
  simp only [aVal, restrict]
  by_cases h1 : i < d - 1 + 1
  · by_cases h2 : i < d + 1
    · rw [dif_pos h1, dif_pos h2]
    · omega
  · omega

private theorem restrict_evalP3 (d : ℕ) (a : BinVec d) (hd : 5 ≤ d) (hd0 : aVal a d = 0) :
    evalP3 (restrict d a) = evalP3 a := by
  simp only [evalP3]
  rw [show d - 1 + 1 = d from by omega]
  rw [Finset.range_succ, Finset.sum_insert (by simp)]
  rw [hd0, zero_mul, zero_add]
  apply Finset.sum_congr rfl; intro i hi
  rw [Finset.mem_range] at hi
  have := restrict_aVal d a i hi
  rw [this]

private theorem restrict_nonzero (d : ℕ) (a : BinVec d) (hne : NonZeroBinVec d a)
    (hd : 5 ≤ d) (hd0 : aVal a d = 0) : NonZeroBinVec (d - 1) (restrict d a) := by
  obtain ⟨i, hi⟩ := hne
  have hne_d : i.val ≠ d := by
    intro heq
    have : a i = a ⟨d, by omega⟩ := by congr 1; ext; exact heq
    rw [this] at hi
    simp only [aVal, dif_pos (Nat.lt_succ_self d)] at hd0
    exact hi (Fin.val_injective hd0)
  exact ⟨⟨i.val, by omega⟩, by
    intro hf
    have hrewrite : restrict d a ⟨i.val, by omega⟩ = a i := by
      simp only [restrict]
    exact hi (hrewrite ▸ hf)⟩

private theorem pow_dvd_trans (d : ℕ) (hd : 5 ≤ d) (n : ℕ) (h : 2 ^ (d + 4) ∣ n) :
    2 ^ ((d - 1) + 4) ∣ n := by
  have h1 : 2 ^ ((d - 1) + 4) ∣ 2 ^ (d + 4) := by
    rw [show (d - 1) + 4 = d + 3 from by omega]; exact ⟨2, by ring⟩
  exact h1.trans h

-- Two-adic bridge helpers

private theorem testBit_split (x c d : ℕ) (hx : x < 2 ^ d) (hc : c ≤ 1) :
    (x + c * 2 ^ d).testBit d = decide (c = 1) := by
  have hpos : 0 < 2 ^ d := by omega
  have hdiv0 : x / 2 ^ d = 0 := (Nat.div_eq_zero_iff hpos).mpr hx
  have hdiv : (x + c * 2 ^ d) / 2 ^ d = c := by
    rw [Nat.add_mul_div_right _ _ hpos, hdiv0]; omega
  simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, hdiv]
  interval_cases c <;> simp_all

private theorem sum_powers_2 (n : ℕ) : ∑ i in Finset.range n, 2 ^ i = 2 ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.range_succ, Finset.sum_insert (by simp), ih]
    have : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by omega)
    omega

private theorem add_mul_mod_right' (x c m : ℕ) : (x + c * m) % m = x % m := by
  rw [Nat.add_mod, show c * m % m = 0 from by rw [Nat.mul_comm c m]; exact Nat.mul_mod_right m c,
      Nat.add_zero, Nat.mod_mod_of_dvd x (Nat.dvd_refl m)]

private theorem encodeLower_lt {m d : ℕ} (hdm : d ≤ m) (a : BinVec m) :
    (∑ i in Finset.range d, aVal a i * 2 ^ i) < 2 ^ d := by
  have h1 : ∀ i ∈ Finset.range d, aVal a i * 2 ^ i ≤ 2 ^ i := by
    intro i hi; rw [Finset.mem_range] at hi
    simp only [aVal, dif_pos (by omega : i < m + 1)]
    have := (a ⟨i, by omega⟩).isLt
    interval_cases (a ⟨i, by omega⟩ : ℕ) <;> simp_all
  have h2 : ∑ i in Finset.range d, aVal a i * 2 ^ i ≤ 2 ^ d - 1 := by
    trans ∑ i in Finset.range d, 2 ^ i
    · exact Finset.sum_le_sum h1
    · rw [sum_powers_2]
  have h3 : 1 ≤ 2 ^ d := Nat.one_le_pow d 2 (by omega)
  omega

-- For i < k: n / 2^i % 2 = (n % 2^k) / 2^i % 2
private theorem mod_pow_eq (k n i : ℕ) (hi : i < k) :
    n / 2 ^ i % 2 = (n % 2 ^ k) / 2 ^ i % 2 := by
  have h2i : 0 < 2 ^ i := Nat.pow_pos (by norm_num : (0 : ℕ) < 2)
  have h2k : 2 ^ k = 2 ^ (k - i) * 2 ^ i := by
    conv_lhs => rw [show k = (k - i) + i from by omega]
    rw [Nat.pow_add]
  have h := Nat.div_add_mod n (2^k)
  have h1 : 2^k * (n / 2^k) = (n / 2^k) * 2 ^ (k - i) * 2 ^ i := by
    rw [mul_comm (2^k) (n/2^k), h2k, mul_assoc]
  have hn : n = (n % 2 ^ k) + (n / 2 ^ k) * 2 ^ (k - i) * 2 ^ i := by
    rw [add_comm] at h; rw [h1] at h; exact h.symm
  rw [show n / 2 ^ i = (n % 2 ^ k + (n / 2 ^ k) * 2 ^ (k - i) * 2 ^ i) / 2 ^ i from congr_arg (· / 2 ^ i) hn]
  rw [Nat.add_mul_div_right (n % 2 ^ k) ((n / 2 ^ k) * 2 ^ (k - i)) h2i]
  have hki : k - i = (k - i - 1) + 1 := by omega
  have h2ki : 2 ^ (k - i) = 2 ^ (k - i - 1) * 2 := by
    rw [congr_arg (2 ^ ·) hki, Nat.pow_succ, mul_comm]
  rw [congr_arg (fun e => (n / 2 ^ k) * e) h2ki]
  rw [← mul_assoc]
  exact Nat.add_mul_mod_self_right ((n % 2 ^ k) / 2 ^ i) ((n / 2 ^ k) * 2 ^ (k - i - 1)) 2

-- Binary decomposition: ∑_{i<k} (n/2^i % 2) * 2^i = n for n < 2^k
private theorem binary_sum (k n : ℕ) (hn : n < 2 ^ k) :
    ∑ i in Finset.range k, (n / 2 ^ i % 2) * 2 ^ i = n := by
  induction k generalizing n with
  | zero => simp; omega
  | succ k ih =>
    rw [Finset.range_succ, Finset.sum_insert (by simp)]
    have hmod : n % 2 ^ k < 2 ^ k := Nat.mod_lt n (Nat.pow_pos (by norm_num : (0 : ℕ) < 2))
    have sum_eq : ∑ i in Finset.range k, (n / 2 ^ i % 2) * 2 ^ i = n % 2 ^ k := by
      rw [← ih (n % 2^k) hmod]
      exact Finset.sum_congr rfl (fun i hi => by
        rw [Finset.mem_range] at hi; rw [mod_pow_eq k n i hi])
    rw [sum_eq]
    have h_bit : n / 2^k % 2 = n / 2^k := by
      have h1 : n / 2^k * 2^k ≤ n := Nat.div_mul_le_self n (2^k)
      have h2 : n / 2^k < 2 := by nlinarith [show 2 ^ (k + 1) = 2 * 2 ^ k from by rw [Nat.pow_succ, mul_comm]]
      exact Nat.mod_eq_of_lt h2
    have hdm : n / 2 ^ k * 2 ^ k + n % 2 ^ k = n := by
      rw [mul_comm (n / 2 ^ k) (2 ^ k)]
      exact Nat.div_add_mod n (2 ^ k)
    rw [h_bit]
    exact hdm

private theorem evalBit_encodeLower (d : ℕ) (a : BinVec d) :
    evalBit d (∑ i in Finset.range d, aVal a i * 2 ^ i) =
    ∑ i in Finset.range d, aVal a i * 3 ^ i := by
  induction d with
  | zero => simp [evalBit]
  | succ d ih =>
    have henc_lt : (∑ i in Finset.range d, aVal a i * 2 ^ i) < 2 ^ d :=
      encodeLower_lt (Nat.le_succ d) a
    have hv : aVal a d ≤ 1 := aVal_le_one a d (by omega : d < d + 1 + 1)
    show evalBit (d + 1) (∑ i in Finset.range (d + 1), aVal a i * 2 ^ i) =
         ∑ i in Finset.range (d + 1), aVal a i * 3 ^ i
    simp only [evalBit]
    rw [Finset.range_succ, Finset.sum_insert (by simp)]
    rw [add_comm (aVal a d * 2 ^ d) (∑ i in Finset.range d, aVal a i * 2 ^ i)]
    rw [testBit_split _ _ d henc_lt hv]
    rw [evalBit_mod d (∑ i in Finset.range d, aVal a i * 2 ^ i + aVal a d * 2 ^ d)]
    rw [add_mul_mod_right']
    rw [Nat.mod_eq_of_lt henc_lt]
    -- ih says: for all a' : BinVec d, evalBit d (∑_{i<d} aVal a' i * 2^i) = ∑_{i<d} aVal a' i * 3^i
    -- But we have a : BinVec (d+1). Use restrict to bridge the type gap.
    have hsum_eq : ∑ i in Finset.range d, aVal a i * 2 ^ i =
        ∑ i in Finset.range d, aVal (restrict (d + 1) a) i * 2 ^ i := by
      apply Finset.sum_congr rfl; intro i hi
      rw [Finset.mem_range] at hi
      rw [restrict_aVal (d + 1) a i (by omega)]
    rw [hsum_eq, ih (restrict (d + 1) a)]
    rw [Finset.sum_insert (by simp)]
    -- LHS: (if decide (aVal a d = 1) then 3^d else 0) + ∑_{i<d} aVal (restrict a) i * 3^i
    -- RHS: aVal a d * 3^d + ∑_{i<d} aVal a i * 3^i
    -- First rewrite LHS sum to use a directly instead of restrict
    have hback : ∑ i in Finset.range d, aVal (restrict (d + 1) a) i * 3 ^ i =
        ∑ i in Finset.range d, aVal a i * 3 ^ i := by
      apply Finset.sum_congr rfl; intro i hi
      rw [Finset.mem_range] at hi
      rw [restrict_aVal (d + 1) a i (by omega)]
    rw [hback]
    congr 1
    · simp only [aVal, dif_pos (by omega : d < d + 1 + 1)]
      have := (a ⟨d, by omega⟩).isLt
      interval_cases (a ⟨d, by omega⟩ : ℕ) <;> simp_all

theorem no_pow2_divides (d : ℕ) (a : BinVec d) (hne : NonZeroBinVec d a) :
    2 ^ (d + 4) ∣ evalP3 a → False := by
  intro hdiv
  induction d using Nat.strongRecOn with
  | _ d ih =>
    by_cases hd4 : d ≤ 4
    · exact no_pow2_small d hd4 a hne hdiv
    · push_neg at hd4
      have hcase : (a ⟨d, by omega⟩ : ℕ) = 0 ∨ (a ⟨d, by omega⟩ : ℕ) = 1 := by
        have := (a ⟨d, by omega⟩).isLt; omega
      rcases hcase with hd0 | hd1
      · -- CASE a_d = 0: restriction + IH
        have hdrop : aVal a d = 0 := by
          simp only [aVal, dif_pos (Nat.lt_succ_self d)]; exact hd0
        have hb_eq := restrict_evalP3 d a hd4 hdrop
        have hb_nz := restrict_nonzero d a hne hd4 hdrop
        have hdiv_a : 2 ^ (d + 4) ∣ evalP3 (restrict d a) := by rw [hb_eq]; exact hdiv
        have hdiv_b : 2 ^ ((d - 1) + 4) ∣ evalP3 (restrict d a) :=
          pow_dvd_trans d hd4 _ hdiv_a
        exact ih (d - 1) (by omega) (restrict d a) hb_nz hdiv_b
      · -- CASE a_d = 1: THE MATHEMATICAL CORE
        have hd5 : 5 ≤ d := by omega
        rcases (show d ≤ 5 ∨ 6 ≤ d by omega) with hd_le5 | hd_ge6
        · -- d ≤ 5: bound argument
          have hle := evalP3_mul2_add1_le d a
          interval_cases d
          all_goals (
            have hpos := evalP3_pos hne
            have ⟨k, hk⟩ := hdiv
            norm_num at hle hpos hk ⊢
            omega)
        · -- d ≥ 6: connect to TwoAdicObstruction
          rcases (show d ≤ 12 ∨ 13 ≤ d by omega) with hd_le12 | hd_ge13
          · -- d = 6..12: use obstruction_le12
            have hsplit : evalP3 a = 3 ^ d + ∑ i in Finset.range d, aVal a i * 3 ^ i := by
              show ∑ i in Finset.range (d + 1), aVal a i * 3 ^ i =
                3 ^ d + ∑ i in Finset.range d, aVal a i * 3 ^ i
              rw [Finset.range_succ, Finset.sum_insert (by simp)]
              simp only [aVal, dif_pos (Nat.lt_succ_self d)]
              rw [hd1, one_mul]
            rw [hsplit] at hdiv
            let enc : ℕ := ∑ i in Finset.range d, aVal a i * 2 ^ i
            have hbridge : ∑ i in Finset.range d, aVal a i * 3 ^ i = evalBit d enc :=
              (evalBit_encodeLower d a).symm
            rw [hbridge] at hdiv
            exact absurd hdiv (TwoAdicObstruction.obstruction_le12 d hd_le12 enc)
          · -- d ≥ 13: use obstruction_le23
            rcases (show d ≤ 23 ∨ 24 ≤ d by omega) with hd_le23 | hd_ge24
            · -- d = 13..23: same obstruction argument
              have hsplit : evalP3 a = 3 ^ d + ∑ i in Finset.range d, aVal a i * 3 ^ i := by
                show ∑ i in Finset.range (d + 1), aVal a i * 3 ^ i =
                  3 ^ d + ∑ i in Finset.range d, aVal a i * 3 ^ i
                rw [Finset.range_succ, Finset.sum_insert (by simp)]
                simp only [aVal, dif_pos (Nat.lt_succ_self d)]
                rw [hd1, one_mul]
              rw [hsplit] at hdiv
              let enc : ℕ := ∑ i in Finset.range d, aVal a i * 2 ^ i
              have hbridge : ∑ i in Finset.range d, aVal a i * 3 ^ i = evalBit d enc :=
                (evalBit_encodeLower d a).symm
              rw [hbridge] at hdiv
              exact absurd hdiv (TwoAdicObstruction.obstruction_le23 d hd_le23 enc)
            · -- d >= 24: split enc by parity, handle even enc via shift
              have hsplit : evalP3 a = 3 ^ d + ∑ i in Finset.range d, aVal a i * 3 ^ i := by
                show ∑ i in Finset.range (d + 1), aVal a i * 3 ^ i =
                  3 ^ d + ∑ i in Finset.range d, aVal a i * 3 ^ i
                rw [Finset.range_succ, Finset.sum_insert (by simp)]
                simp only [aVal, dif_pos (Nat.lt_succ_self d)]
                rw [hd1, one_mul]
              rw [hsplit] at hdiv
              let enc : ℕ := ∑ i in Finset.range d, aVal a i * 2 ^ i
              have hbridge : ∑ i in Finset.range d, aVal a i * 3 ^ i = evalBit d enc :=
                (evalBit_encodeLower d a).symm
              rw [hbridge] at hdiv
              rcases (show enc % 2 = 0 ∨ enc % 2 = 1 by omega) with heven | hodd
              · -- enc even: shift + coprimality
                have ⟨m, hm⟩ : ∃ m, enc = 2 * m := ⟨enc / 2, by omega⟩
                rw [hm] at hdiv
                rw [evalBit_two_mul d m (by omega)] at hdiv
                rw [pow3_eq d (by omega)] at hdiv
                have hfactor : 2 ^ (d + 4) ∣ 3 * (3 ^ (d - 1) + evalBit (d - 1) m) := by
                  rw [show 3 * 3 ^ (d - 1) + 3 * evalBit (d - 1) m =
                    3 * (3 ^ (d - 1) + evalBit (d - 1) m) from by ring] at hdiv; exact hdiv
                have hdiv' : 2 ^ (d + 4) ∣ 3 ^ (d - 1) + evalBit (d - 1) m :=
                  (coprime_dvd_iff (d + 4) (3 ^ (d - 1) + evalBit (d - 1) m)).mp hfactor
                have hsmall : 2 ^ ((d - 1) + 4) ∣ 3 ^ (d - 1) + evalBit (d - 1) m :=
                  dvd_trans (Nat.pow_dvd_pow 2 (by omega : d - 1 + 4 ≤ d + 4)) hdiv'
                rcases (show d ≤ 24 ∨ 25 ≤ d by omega) with hd_le24 | hd_ge25
                · -- d = 24: obstruction_le23 handles d-1=23
                  exact absurd hsmall (TwoAdicObstruction.obstruction_le23 (d - 1) (by omega) m)
                · -- d >= 25: build a' : BinVec (d-1) encoding m with leading 1, apply IH
                  have hm_lt : m < 2 ^ (d - 1) := by
                    have henc : enc < 2 ^ d := encodeLower_lt (le_refl d) a
                    rw [hm] at henc
                    have hd : d = (d - 1) + 1 := by omega
                    rw [hd, Nat.pow_succ] at henc
                    omega
                  let a' : BinVec (d - 1) := fun j =>
                    if h : j.val = d - 1 then ⟨1, by omega⟩
                    else ⟨m / 2 ^ j.val % 2, by omega⟩
                  have hne' : NonZeroBinVec (d - 1) a' :=
                    ⟨⟨d - 1, by omega⟩, by simp [a']⟩
                  have hlower : ∑ i in Finset.range (d - 1), aVal a' i * 3 ^ i = evalBit (d - 1) m := by
                    trans evalBit (d - 1) (∑ i in Finset.range (d - 1), aVal a' i * 2 ^ i)
                    · exact (evalBit_encodeLower (d - 1) a').symm
                    · congr 1
                      trans ∑ i in Finset.range (d - 1), (m / 2 ^ i % 2) * 2 ^ i
                      · apply Finset.sum_congr rfl; intro i hi
                        rw [Finset.mem_range] at hi
                        simp only [aVal, a']
                        split
                        · split
                          · omega
                          · rfl
                        · omega
                      · exact binary_sum (d - 1) m hm_lt
                  have heval' : evalP3 a' = 3 ^ (d - 1) + evalBit (d - 1) m := by
                    show ∑ i in Finset.range ((d - 1) + 1), aVal a' i * 3 ^ i =
                      3 ^ (d - 1) + evalBit (d - 1) m
                    rw [Finset.range_succ, Finset.sum_insert (by simp)]
                    simp only [aVal, a', Finset.mem_range, ite_true, ite_false,
                      dite_true, dite_false]
                    norm_num
                    exact hlower
                  exact ih (d - 1) (by omega) a' hne' (heval' ▸ hsmall)
              · -- enc odd: THE MATHEMATICAL CORE
                -- For odd enc = 2m+1: evalBit d enc = 1 + 3·evalBit(d-1,m)
                have ⟨m, hm⟩ : ∃ m, enc = 2 * m + 1 := ⟨enc / 2, by omega⟩
                rw [hm] at hdiv
                rw [evalBit_one_add_mul d m (by omega)] at hdiv
                rw [pow3_eq d (by omega)] at hdiv
                -- hdiv currently: 2^(d+4) | 3 * 3^(d-1) + 1 + 3 * evalBit(d-1, m)
                have hdiv' : 2 ^ (d + 4) ∣ 3 * (3 ^ (d - 1) + evalBit (d - 1) m) + 1 := by
                  -- hdiv : 2^(d+4) | 3 * 3^(d-1) + (1 + 3 * evalBit (d-1, m))
                  -- goal: 2^(d+4) | 3 * (3^(d-1) + evalBit (d-1, m)) + 1
                  have h := hdiv
                  rw [show 3 * 3 ^ (d - 1) + (1 + 3 * evalBit (d - 1) m) =
                    3 * (3 ^ (d - 1) + evalBit (d - 1) m) + 1 from by ring] at h
                  exact h
                -- Split: d=24 needs separate handling, d=25..70 uses bridge, d>=71 uses digit-2
                rcases (show d ≤ 24 ∨ 25 ≤ d by omega) with hd24 | hd25
                · -- d=24: obstruction_le23 gives 2^27 ∤ 3^23 + evalBit(23,m)
                  -- Need: 2^28 ∤ 3*(3^23 + evalBit(23,m)) + 1
                  sorry -- d=24 odd enc: needs separate argument
                · rcases (show d ≤ 70 ∨ 71 ≤ d by omega) with hd70 | hd71
                  · -- d=25..70: use bridge theorem (carry machine soundness)
                    exact OddCaseDigit2.odd_enc_bridge d hd25 hd70 m hdiv'
                  · -- d>=71: use digit-2 property of oddTarget
                    sorry -- d>=71: needs oddTarget_hasDigit2_all

end VdBound
