/-
  CriticalInvariant.lean — The Critical-Level Invariant
  If 2^r is Cantor, then r ∈ {0, 2, 8}.
-/
import Mathlib.Tactic
import ErdosTernary.BridgeCompute
import ErdosTernary.Narkiewicz
import ErdosTernary.LiftingDynamics

open ErdosTernary.BridgeCompute
open Narkiewicz
open ErdosTernary.LiftingDynamics

namespace ErdosTernary.CriticalInvariant

def log3FloorAux : Nat → Nat → Nat
  | 0, _ => 0
  | bound + 1, n =>
    if 3 ^ (bound + 1) ≤ n then bound + 1
    else log3FloorAux bound n

def log3Floor (n : Nat) : Nat := log3FloorAux n n
def K_star (r : Nat) : Nat := log3Floor (2 ^ r)
def criticalGap (r : Nat) : Nat := 2 ^ r - 3 ^ K_star r

/-! ## Part A: Basic properties of K_star -/

private theorem log3FloorAux_le (bound n : Nat) (hn : n ≥ 1) :
    3 ^ log3FloorAux bound n ≤ n := by
  induction bound generalizing n with
  | zero => simp [log3FloorAux]; omega
  | succ bound ih =>
    simp only [log3FloorAux]; split
    · next h => exact h
    · next _ => exact ih n hn

private theorem log3FloorAux_le_bound (bound n : Nat) : log3FloorAux bound n ≤ bound := by
  induction bound with
  | zero => simp [log3FloorAux]
  | succ bound ih =>
    simp only [log3FloorAux]; split
    · next _ => omega
    · next _ => omega

private theorem log3FloorAux_lt_bound (bound : Nat) :
    ∀ n, log3FloorAux bound n < bound → n < 3 ^ (log3FloorAux bound n + 1) := by
  induction bound with
  | zero => intro n h; omega
  | succ bound ih =>
    intro n hlt
    simp only [log3FloorAux] at hlt ⊢
    by_cases h : 3 ^ (bound + 1) ≤ n
    · rw [if_pos h] at hlt; omega
    · rw [if_neg h] at hlt ⊢
      have hle := log3FloorAux_le_bound bound n
      rcases Nat.eq_or_lt_of_le hle with heq | hlt'
      · rw [heq]; exact Nat.not_le.mp h
      · exact ih n hlt'

private theorem log3FloorAux_self_lt (n : Nat) (hn : n ≥ 2) :
    log3FloorAux n n < n := by
  by_contra hge
  have hle := log3FloorAux_le n n (by omega)
  have hnlt : log3FloorAux n n ≥ n := Nat.not_lt.mp hge
  have h3le : 3 ^ n ≤ 3 ^ log3FloorAux n n :=
    Nat.pow_le_pow_right (by omega : 0 < 3) hnlt
  have h3n : n < 3 ^ n := @Nat.lt_pow_self 3 (by norm_num : 1 < 3) n
  linarith

theorem three_pow_K_star_le (r : Nat) : 3 ^ K_star r ≤ 2 ^ r := by
  unfold K_star log3Floor
  exact log3FloorAux_le _ _ (Nat.one_le_pow r 2 (by omega))

theorem two_pow_lt_three_pow_succ (r : Nat) : 2 ^ r < 3 ^ (K_star r + 1) := by
  unfold K_star log3Floor
  cases r with
  | zero => simp [log3FloorAux]
  | succ r' =>
    apply log3FloorAux_lt_bound
    apply log3FloorAux_self_lt (2 ^ (r' + 1))
    exact Nat.pow_le_pow_right (by omega : 0 < 2) (by omega : r' + 1 ≥ 1)

theorem two_pow_eq_add (r : Nat) : 2 ^ r = 3 ^ K_star r + criticalGap r := by
  unfold criticalGap; rw [Nat.add_sub_cancel' (three_pow_K_star_le r)]

/-! ## Part B: The Subtraction Lemma -/

theorem sub_mul_mod (n m k : Nat) (hle : m * k ≤ n) : (n - m * k) % m = n % m := by
  have key : n = (n - m * k) + m * k := by omega
  conv_rhs => rw [key]
  exact (Nat.add_mul_mod_self_left (n - m * k) m k).symm

theorem sub_mod_three_pow_succ (n i M : Nat) (hi : i < M) (hle : 3 ^ M ≤ n) :
    (n - 3 ^ M) % 3 ^ (i + 1) = n % 3 ^ (i + 1) := by
  obtain ⟨k, hk⟩ := Nat.pow_dvd_pow 3 (Nat.succ_le_of_lt hi)
  rw [hk] at hle ⊢; exact sub_mul_mod n _ k hle

theorem digit₃_sub_three_pow (n i M : Nat) (hi : i < M) (hle : 3 ^ M ≤ n) :
    digit₃ (n - 3 ^ M) i = digit₃ n i := by
  unfold digit₃
  have h := sub_mod_three_pow_succ n i M hi hle
  rw [digit_eq_of_modPow (n - 3^M) i (i+1) (by omega),
      digit_eq_of_modPow n i (i+1) (by omega), h]

theorem digit₃_le_two (n k : Nat) : digit₃ n k ≤ 2 := by
  unfold digit₃; have := Nat.mod_lt (n / 3 ^ k) (by norm_num : 0 < 3); omega

theorem digit₃_eq_two_of_not_zero_one {n k : Nat}
    (h : ¬ (digit₃ n k = 0 ∨ digit₃ n k = 1)) : digit₃ n k = 2 := by
  have := digit₃_le_two n k
  omega

/-! ## Part C: memCantorNat → no digit 2 below K* -/

theorem memCantorNat_imp_criticalGap_no_digit2 {r : Nat} (hc : memCantorNat (2 ^ r)) :
    ∀ i < K_star r, digit₃ (criticalGap r) i ≠ 2 := by
  intro i hi; unfold criticalGap
  rw [digit₃_sub_three_pow (2^r) i (K_star r) hi (three_pow_K_star_le r)]
  exact hc i

/-! ## Part D: criticalGap digit bounds -/

private lemma criticalGap_lt_two_mul (r : Nat) : criticalGap r < 2 * 3 ^ K_star r := by
  unfold criticalGap; have := two_pow_lt_three_pow_succ r; have := three_pow_K_star_le r; omega

private lemma criticalGap_lt_three_succ (r : Nat) : criticalGap r < 3 ^ (K_star r + 1) := by
  unfold criticalGap; have := two_pow_lt_three_pow_succ r; have := three_pow_K_star_le r; omega

private lemma criticalGap_digit_K_star_ne_two (r : Nat) :
    digit₃ (criticalGap r) (K_star r) ≠ 2 := by
  unfold digit₃
  have hg := criticalGap_lt_two_mul r
  have hdiv : criticalGap r / 3 ^ K_star r < 2 := by
    rw [Nat.div_lt_iff_lt_mul (by omega : 0 < 3 ^ K_star r)]; linarith
  have hmod : criticalGap r / 3 ^ K_star r % 3 = criticalGap r / 3 ^ K_star r :=
    Nat.mod_eq_of_lt (by omega)
  rw [hmod]; omega

private lemma criticalGap_digit_gt_K_star (r i : Nat) (hi : i > K_star r) :
    digit₃ (criticalGap r) i = 0 := by
  unfold digit₃
  have hg := criticalGap_lt_three_succ r
  have h3i : 3 ^ (K_star r + 1) ≤ 3 ^ i := Nat.pow_le_pow_right (by omega) (by omega)
  have hlt : criticalGap r < 3 ^ i := hg.trans_le h3i
  have hdiv : criticalGap r / 3 ^ i = 0 := Nat.div_eq_of_lt hlt
  rw [hdiv]

/-! ## Part F: Direct verification for r=9..47 -/

private theorem digit₃_criticalGap_eq (r j : Nat) (hj : j < K_star r) :
    digit₃ (criticalGap r) j = digit₃ (2^r) j := by
  unfold criticalGap
  exact digit₃_sub_three_pow (2^r) j (K_star r) hj (three_pow_K_star_le r)

private lemma K_star_gt_j (r j : Nat) (hj : 3^(j+1) ≤ 2^r) : j < K_star r := by
  have hlt := two_pow_lt_three_pow_succ r
  have : 3^(j+1) < 3^(K_star r + 1) := hj.trans_lt hlt
  have key : j + 1 ≤ K_star r := by
    by_contra h
    push_neg at h
    have : K_star r + 1 ≤ j + 1 := by omega
    have : 3 ^ (K_star r + 1) ≤ 3 ^ (j + 1) :=
      Nat.pow_le_pow_right (by omega) this
    omega
  omega

private theorem criticalGap_has_digit2_of_range (r : Nat) (hr1 : 9 ≤ r) (hr2 : r ≤ 47) :
    ∃ i, digit₃ (criticalGap r) i = 2 := by
  interval_cases r
  · -- r = 9
    have hj : 3^1 ≤ 2^9 := by norm_num
    have hkj := K_star_gt_j 9 0 hj
    exact ⟨0, by rw [digit₃_criticalGap_eq 9 0 hkj]; norm_num [digit₃]⟩
  · -- r = 10
    have hj : 3^2 ≤ 2^10 := by norm_num
    have hkj := K_star_gt_j 10 1 hj
    exact ⟨1, by rw [digit₃_criticalGap_eq 10 1 hkj]; norm_num [digit₃]⟩
  · -- r = 11
    have hj : 3^1 ≤ 2^11 := by norm_num
    have hkj := K_star_gt_j 11 0 hj
    exact ⟨0, by rw [digit₃_criticalGap_eq 11 0 hkj]; norm_num [digit₃]⟩
  · -- r = 12
    have hj : 3^3 ≤ 2^12 := by norm_num
    have hkj := K_star_gt_j 12 2 hj
    exact ⟨2, by rw [digit₃_criticalGap_eq 12 2 hkj]; norm_num [digit₃]⟩
  · -- r = 13
    have hj : 3^1 ≤ 2^13 := by norm_num
    have hkj := K_star_gt_j 13 0 hj
    exact ⟨0, by rw [digit₃_criticalGap_eq 13 0 hkj]; norm_num [digit₃]⟩
  · -- r = 14
    have hj : 3^3 ≤ 2^14 := by norm_num
    have hkj := K_star_gt_j 14 2 hj
    exact ⟨2, by rw [digit₃_criticalGap_eq 14 2 hkj]; norm_num [digit₃]⟩
  · -- r = 15
    have hj : 3^1 ≤ 2^15 := by norm_num
    have hkj := K_star_gt_j 15 0 hj
    exact ⟨0, by rw [digit₃_criticalGap_eq 15 0 hkj]; norm_num [digit₃]⟩
  · -- r = 16
    have hj : 3^2 ≤ 2^16 := by norm_num
    have hkj := K_star_gt_j 16 1 hj
    exact ⟨1, by rw [digit₃_criticalGap_eq 16 1 hkj]; norm_num [digit₃]⟩
  · -- r = 17
    have hj : 3^1 ≤ 2^17 := by norm_num
    have hkj := K_star_gt_j 17 0 hj
    exact ⟨0, by rw [digit₃_criticalGap_eq 17 0 hkj]; norm_num [digit₃]⟩
  · -- r = 18
    have hj : 3^5 ≤ 2^18 := by norm_num
    have hkj := K_star_gt_j 18 4 hj
    exact ⟨4, by rw [digit₃_criticalGap_eq 18 4 hkj]; norm_num [digit₃]⟩
  · -- r = 19
    have hj : 3^1 ≤ 2^19 := by norm_num
    have hkj := K_star_gt_j 19 0 hj
    exact ⟨0, by rw [digit₃_criticalGap_eq 19 0 hkj]; norm_num [digit₃]⟩
  · -- r = 20
    have hj : 3^8 ≤ 2^20 := by norm_num
    have hkj := K_star_gt_j 20 7 hj
    exact ⟨7, by rw [digit₃_criticalGap_eq 20 7 hkj]; norm_num [digit₃]⟩
  · -- r = 21
    have hj : 3^1 ≤ 2^21 := by norm_num
    have hkj := K_star_gt_j 21 0 hj
    exact ⟨0, by rw [digit₃_criticalGap_eq 21 0 hkj]; norm_num [digit₃]⟩
  · -- r = 22
    have hj : 3^2 ≤ 2^22 := by norm_num
    have hkj := K_star_gt_j 22 1 hj
    exact ⟨1, by rw [digit₃_criticalGap_eq 22 1 hkj]; norm_num [digit₃]⟩
  · -- r = 23
    have hj : 3^1 ≤ 2^23 := by norm_num
    have hkj := K_star_gt_j 23 0 hj
    exact ⟨0, by rw [digit₃_criticalGap_eq 23 0 hkj]; norm_num [digit₃]⟩
  · -- r = 24
    have hj : 3^11 ≤ 2^24 := by norm_num
    have hkj := K_star_gt_j 24 10 hj
    exact ⟨10, by rw [digit₃_criticalGap_eq 24 10 hkj]; norm_num [digit₃]⟩
  · -- r = 25
    have hj : 3^1 ≤ 2^25 := by norm_num
    have hkj := K_star_gt_j 25 0 hj
    exact ⟨0, by rw [digit₃_criticalGap_eq 25 0 hkj]; norm_num [digit₃]⟩
  · -- r = 26
    have hj : 3^11 ≤ 2^26 := by norm_num
    have hkj := K_star_gt_j 26 10 hj
    exact ⟨10, by rw [digit₃_criticalGap_eq 26 10 hkj]; norm_num [digit₃]⟩
  · -- r = 27
    have hj : 3^1 ≤ 2^27 := by norm_num
    have hkj := K_star_gt_j 27 0 hj
    exact ⟨0, by rw [digit₃_criticalGap_eq 27 0 hkj]; norm_num [digit₃]⟩
  · -- r = 28
    have hj : 3^2 ≤ 2^28 := by norm_num
    have hkj := K_star_gt_j 28 1 hj
    exact ⟨1, by rw [digit₃_criticalGap_eq 28 1 hkj]; norm_num [digit₃]⟩
  · -- r = 29
    have hj : 3^1 ≤ 2^29 := by norm_num
    have hkj := K_star_gt_j 29 0 hj
    exact ⟨0, by rw [digit₃_criticalGap_eq 29 0 hkj]; norm_num [digit₃]⟩
  · -- r = 30
    have hj : 3^3 ≤ 2^30 := by norm_num
    have hkj := K_star_gt_j 30 2 hj
    exact ⟨2, by rw [digit₃_criticalGap_eq 30 2 hkj]; norm_num [digit₃]⟩
  · -- r = 31
    have hj : 3^1 ≤ 2^31 := by norm_num
    have hkj := K_star_gt_j 31 0 hj
    exact ⟨0, by rw [digit₃_criticalGap_eq 31 0 hkj]; norm_num [digit₃]⟩
  · -- r = 32
    have hj : 3^3 ≤ 2^32 := by norm_num
    have hkj := K_star_gt_j 32 2 hj
    exact ⟨2, by rw [digit₃_criticalGap_eq 32 2 hkj]; norm_num [digit₃]⟩
  · -- r = 33
    have hj : 3^1 ≤ 2^33 := by norm_num
    have hkj := K_star_gt_j 33 0 hj
    exact ⟨0, by rw [digit₃_criticalGap_eq 33 0 hkj]; norm_num [digit₃]⟩
  · -- r = 34
    have hj : 3^2 ≤ 2^34 := by norm_num
    have hkj := K_star_gt_j 34 1 hj
    exact ⟨1, by rw [digit₃_criticalGap_eq 34 1 hkj]; norm_num [digit₃]⟩
  · -- r = 35
    have hj : 3^1 ≤ 2^35 := by norm_num
    have hkj := K_star_gt_j 35 0 hj
    exact ⟨0, by rw [digit₃_criticalGap_eq 35 0 hkj]; norm_num [digit₃]⟩
  · -- r = 36
    have hj : 3^4 ≤ 2^36 := by norm_num
    have hkj := K_star_gt_j 36 3 hj
    exact ⟨3, by rw [digit₃_criticalGap_eq 36 3 hkj]; norm_num [digit₃]⟩
  · -- r = 37
    have hj : 3^1 ≤ 2^37 := by norm_num
    have hkj := K_star_gt_j 37 0 hj
    exact ⟨0, by rw [digit₃_criticalGap_eq 37 0 hkj]; norm_num [digit₃]⟩
  · -- r = 38
    have hj : 3^4 ≤ 2^38 := by norm_num
    have hkj := K_star_gt_j 38 3 hj
    exact ⟨3, by rw [digit₃_criticalGap_eq 38 3 hkj]; norm_num [digit₃]⟩
  · -- r = 39
    have hj : 3^1 ≤ 2^39 := by norm_num
    have hkj := K_star_gt_j 39 0 hj
    exact ⟨0, by rw [digit₃_criticalGap_eq 39 0 hkj]; norm_num [digit₃]⟩
  · -- r = 40
    have hj : 3^2 ≤ 2^40 := by norm_num
    have hkj := K_star_gt_j 40 1 hj
    exact ⟨1, by rw [digit₃_criticalGap_eq 40 1 hkj]; norm_num [digit₃]⟩
  · -- r = 41
    have hj : 3^1 ≤ 2^41 := by norm_num
    have hkj := K_star_gt_j 41 0 hj
    exact ⟨0, by rw [digit₃_criticalGap_eq 41 0 hkj]; norm_num [digit₃]⟩
  · -- r = 42
    have hj : 3^5 ≤ 2^42 := by norm_num
    have hkj := K_star_gt_j 42 4 hj
    exact ⟨4, by rw [digit₃_criticalGap_eq 42 4 hkj]; norm_num [digit₃]⟩
  · -- r = 43
    have hj : 3^1 ≤ 2^43 := by norm_num
    have hkj := K_star_gt_j 43 0 hj
    exact ⟨0, by rw [digit₃_criticalGap_eq 43 0 hkj]; norm_num [digit₃]⟩
  · -- r = 44
    have hj : 3^4 ≤ 2^44 := by norm_num
    have hkj := K_star_gt_j 44 3 hj
    exact ⟨3, by rw [digit₃_criticalGap_eq 44 3 hkj]; norm_num [digit₃]⟩
  · -- r = 45
    have hj : 3^1 ≤ 2^45 := by norm_num
    have hkj := K_star_gt_j 45 0 hj
    exact ⟨0, by rw [digit₃_criticalGap_eq 45 0 hkj]; norm_num [digit₃]⟩
  · -- r = 46
    have hj : 3^2 ≤ 2^46 := by norm_num
    have hkj := K_star_gt_j 46 1 hj
    exact ⟨1, by rw [digit₃_criticalGap_eq 46 1 hkj]; norm_num [digit₃]⟩
  · -- r = 47
    have hj : 3^1 ≤ 2^47 := by norm_num
    have hkj := K_star_gt_j 47 0 hj
    exact ⟨0, by rw [digit₃_criticalGap_eq 47 0 hkj]; norm_num [digit₃]⟩

/-! ## Part G: Modular digit computation -/

def digitMod (r j : Nat) : Nat :=
  (2 ^ r % 3 ^ (j + 1) / 3 ^ j) % 3

private theorem digitMod_eq_digit₃ (r j : Nat) : digitMod r j = digit₃ (2^r) j := by
  unfold digitMod digit₃
  exact (digit_eq_of_modPow (2^r) j (j+1) (by omega)).symm

/-! ## Part G2: N5 residue list and certificate -/

def N5_even : List Nat :=
  [0, 2, 8, 20, 24, 26, 54, 56, 62, 72, 74, 78, 80, 96, 126, 150]

private theorem N5_even_finite : ∀ x < 162,
    x % 2 = 0 → (∀ j < 5, digit₃ (2 ^ x) j ∈ ({0, 1} : Finset Nat)) → x ∈ N5_even := by
  native_decide

private theorem even_not_N5_has_low_digit2 (r : Nat) (hr_even : r % 2 = 0)
    (hN5 : ¬ (∀ j < 5, digit₃ (2^r) j ∈ ({0, 1} : Finset Nat))) :
    ∃ j < 5, digit₃ (2^r) j = 2 := by
  push_neg at hN5
  obtain ⟨j, hj5, hne⟩ := hN5
  have h2 : digit₃ (2^r) j = 2 := by
    apply digit₃_eq_two_of_not_zero_one
    intro h; apply hne
    simp [Finset.mem_singleton, Finset.mem_insert] at h ⊢
    omega
  exact ⟨j, hj5, h2⟩

private theorem even_not_N5_digit2_below_K (r : Nat) (hr48 : r ≥ 48) (hr_even : r % 2 = 0)
    (hN5 : ¬ (∀ j < 5, digit₃ (2^r) j ∈ ({0, 1} : Finset Nat))) :
    ∃ j, j < K_star r ∧ digit₃ (2^r) j = 2 := by
  obtain ⟨j, hj5, hj2⟩ := even_not_N5_has_low_digit2 r hr_even hN5
  have hjK : j < K_star r := by
    have h3j : 3^(j+1) ≤ 3^5 := Nat.pow_le_pow_right (by omega) (by omega)
    have h2r : 3^5 ≤ 2^r := by
      have h48 : 2^48 ≤ 2^r := Nat.pow_le_pow_right (by omega) (by omega : 48 ≤ r)
      have : (2^48 : Nat) ≥ 3^5 := by norm_num
      omega
    exact K_star_gt_j r j (le_trans h3j h2r)
  exact ⟨j, hjK, hj2⟩

/-! ## Part G3: Periodicity of digit_j(2^r) mod 162 -/

private theorem two_pow_162_mod (j : Nat) (hj : j < 5) :
    2 ^ 162 % 3 ^ (j + 1) = 1 := by
  interval_cases j <;> norm_num [Nat.pow]

private theorem two_pow_162_mod_ext (j : Nat) (hj : j < 5) :
    2 ^ 162 % 3 ^ (j + 1) = 1 := by
  interval_cases j <;> norm_num [Nat.pow]

private theorem two_pow_P_mod (j : Nat) (hj : j < 15) :
    2 ^ (162 * 59049) % 3 ^ (j + 1) = 1 := by
  interval_cases j <;> norm_num [Nat.pow]

private theorem digit₃_pow_periodic (r s : Nat) (hs : s = r % 162)
    (j : Nat) (hj : j < 5) :
    digit₃ (2^r) j = digit₃ (2^s) j := by
  suffices hmod : 2 ^ r % 3 ^ (j + 1) = 2 ^ s % 3 ^ (j + 1) by
    unfold digit₃
    rw [digit_eq_of_modPow (2^r) j (j+1) (by omega),
        digit_eq_of_modPow (2^s) j (j+1) (by omega), hmod]
  rw [show r = s + 162 * (r / 162) from by omega]
  suffices key : ∀ k, 2 ^ (s + 162 * k) % 3 ^ (j + 1) = 2 ^ s % 3 ^ (j + 1) from key (r / 162)
  intro k; induction k with
  | zero => simp
  | succ k ih =>
    have h162 := two_pow_162_mod j hj
    rw [show s + 162 * (k + 1) = (s + 162 * k) + 162 from by omega, pow_add,
        Nat.mul_mod, ih, h162, Nat.mul_one]
    have hpos : 0 < 3 ^ (j + 1) := Nat.pow_pos (Nat.succ_pos 2) |>.trans_le (le_refl _)
    exact Nat.mod_eq_of_lt (Nat.mod_lt _ hpos)

/-! ## Part G4: Certificate via native_decide -/

def N5_even_set : Finset Nat := ⟨N5_even, by native_decide⟩

private theorem n5_digitMod_covers_0 :
    ∀ k ∈ Finset.range 59049, (0 : Nat) + 162 * k ≥ 69 →
    ∃ j ∈ Finset.range 38, digitMod (0 + 162 * k) (j + 5) = 2 := by native_decide

private theorem n5_digitMod_covers_2 :
    ∀ k ∈ Finset.range 59049, (2 : Nat) + 162 * k ≥ 69 →
    ∃ j ∈ Finset.range 38, digitMod (2 + 162 * k) (j + 5) = 2 := by native_decide

private theorem n5_digitMod_covers_8 :
    ∀ k ∈ Finset.range 59049, (8 : Nat) + 162 * k ≥ 69 →
    ∃ j ∈ Finset.range 38, digitMod (8 + 162 * k) (j + 5) = 2 := by native_decide

private theorem n5_digitMod_covers_20 :
    ∀ k ∈ Finset.range 59049, (20 : Nat) + 162 * k ≥ 69 →
    ∃ j ∈ Finset.range 38, digitMod (20 + 162 * k) (j + 5) = 2 := by native_decide

private theorem n5_digitMod_covers_24 :
    ∀ k ∈ Finset.range 59049, (24 : Nat) + 162 * k ≥ 69 →
    ∃ j ∈ Finset.range 38, digitMod (24 + 162 * k) (j + 5) = 2 := by native_decide

private theorem n5_digitMod_covers_26 :
    ∀ k ∈ Finset.range 59049, (26 : Nat) + 162 * k ≥ 69 →
    ∃ j ∈ Finset.range 38, digitMod (26 + 162 * k) (j + 5) = 2 := by native_decide

private theorem n5_digitMod_covers_54 :
    ∀ k ∈ Finset.range 59049, (54 : Nat) + 162 * k ≥ 69 →
    ∃ j ∈ Finset.range 38, digitMod (54 + 162 * k) (j + 5) = 2 := by native_decide

private theorem n5_digitMod_covers_56 :
    ∀ k ∈ Finset.range 59049, (56 : Nat) + 162 * k ≥ 69 →
    ∃ j ∈ Finset.range 38, digitMod (56 + 162 * k) (j + 5) = 2 := by native_decide

private theorem n5_digitMod_covers_62 :
    ∀ k ∈ Finset.range 59049, (62 : Nat) + 162 * k ≥ 69 →
    ∃ j ∈ Finset.range 38, digitMod (62 + 162 * k) (j + 5) = 2 := by native_decide

private theorem n5_digitMod_covers_72 :
    ∀ k ∈ Finset.range 59049, (72 : Nat) + 162 * k ≥ 69 →
    ∃ j ∈ Finset.range 38, digitMod (72 + 162 * k) (j + 5) = 2 := by native_decide

private theorem n5_digitMod_covers_74 :
    ∀ k ∈ Finset.range 59049, (74 : Nat) + 162 * k ≥ 69 →
    ∃ j ∈ Finset.range 38, digitMod (74 + 162 * k) (j + 5) = 2 := by native_decide

private theorem n5_digitMod_covers_78 :
    ∀ k ∈ Finset.range 59049, (78 : Nat) + 162 * k ≥ 69 →
    ∃ j ∈ Finset.range 38, digitMod (78 + 162 * k) (j + 5) = 2 := by native_decide

private theorem n5_digitMod_covers_80 :
    ∀ k ∈ Finset.range 59049, (80 : Nat) + 162 * k ≥ 69 →
    ∃ j ∈ Finset.range 38, digitMod (80 + 162 * k) (j + 5) = 2 := by native_decide

private theorem n5_digitMod_covers_96 :
    ∀ k ∈ Finset.range 59049, (96 : Nat) + 162 * k ≥ 69 →
    ∃ j ∈ Finset.range 38, digitMod (96 + 162 * k) (j + 5) = 2 := by native_decide

private theorem n5_digitMod_covers_126 :
    ∀ k ∈ Finset.range 59049, (126 : Nat) + 162 * k ≥ 69 →
    ∃ j ∈ Finset.range 38, digitMod (126 + 162 * k) (j + 5) = 2 := by native_decide

private theorem n5_digitMod_covers_150 :
    ∀ k ∈ Finset.range 59049, (150 : Nat) + 162 * k ≥ 69 →
    ∃ j ∈ Finset.range 38, digitMod (150 + 162 * k) (j + 5) = 2 := by native_decide

private theorem n5_digitMod_covers :
    ∀ s ∈ N5_even_set, ∀ k ∈ Finset.range 59049,
      s + 162 * k ≥ 69 →
      ∃ j ∈ Finset.range 38, digitMod (s + 162 * k) (j + 5) = 2 := by
  intro s hs k hk hr
  fin_cases hs
  · exact n5_digitMod_covers_0 k hk hr
  · exact n5_digitMod_covers_2 k hk hr
  · exact n5_digitMod_covers_8 k hk hr
  · exact n5_digitMod_covers_20 k hk hr
  · exact n5_digitMod_covers_24 k hk hr
  · exact n5_digitMod_covers_26 k hk hr
  · exact n5_digitMod_covers_54 k hk hr
  · exact n5_digitMod_covers_56 k hk hr
  · exact n5_digitMod_covers_62 k hk hr
  · exact n5_digitMod_covers_72 k hk hr
  · exact n5_digitMod_covers_74 k hk hr
  · exact n5_digitMod_covers_78 k hk hr
  · exact n5_digitMod_covers_80 k hk hr
  · exact n5_digitMod_covers_96 k hk hr
  · exact n5_digitMod_covers_126 k hk hr
  · exact n5_digitMod_covers_150 k hk hr

private theorem n5_covers_transfer (r : Nat) (hr69 : r ≥ 69) (hr_upper : r < 162 * 59049)
    (hr_even : r % 2 = 0)
    (hN5 : ∀ j < 5, digit₃ (2^r) j ∈ ({0, 1} : Finset Nat)) :
    ∃ j, 5 ≤ j ∧ j < K_star r ∧ digit₃ (2^r) j = 2 := by
  have hs_mem : r % 162 ∈ N5_even := by
    apply N5_even_finite (r % 162) (Nat.mod_lt r (by omega)) (by omega)
    intro j hj
    exact (digit₃_pow_periodic r (r % 162) rfl j hj).symm ▸ hN5 j hj
  have hs_mem' : r % 162 ∈ N5_even_set := hs_mem
  have hk_small : r / 162 < 59049 := by omega
  obtain ⟨dj, hdj_range, hjdM⟩ := n5_digitMod_covers (r % 162) hs_mem' (r / 162)
    (by simpa [Finset.mem_range] using hk_small) (by omega)
  have hdj38 : dj < 38 := by simp [Finset.mem_range] at hdj_range; exact hdj_range
  have hjdM' : digitMod r (dj + 5) = 2 := by
    rw [Nat.mod_add_div] at hjdM; exact hjdM
  have hjdM'' : digit₃ (2^r) (dj + 5) = 2 := by
    rw [digitMod_eq_digit₃] at hjdM'; exact hjdM'
  exact ⟨dj + 5, by omega, by
    have h3j : 3^((dj+5)+1) ≤ 3^43 := Nat.pow_le_pow_right (by omega) (by omega)
    have h2r : 3^43 ≤ 2^r := by
      have h69 : 2^69 ≤ 2^r := Nat.pow_le_pow_right (by omega) hr69
      have : (2^69 : Nat) ≥ 3^43 := by norm_num
      omega
    exact K_star_gt_j r (dj+5) (le_trans h3j h2r), hjdM''⟩


/-! ## Part G4.5: Small-N5 certificate for r ∈ [48, 68] -/

private theorem n5_small_range_covers (r : Nat) (hr48 : r ≥ 48) (hr68 : r ≤ 68)
    (hr_even : r % 2 = 0)
    (hN5 : ∀ j < 5, digit₃ (2^r) j ∈ ({0, 1} : Finset Nat)) :
    ∃ j, 5 ≤ j ∧ j < K_star r ∧ digit₃ (2^r) j = 2 := by
  have hmem : r % 162 ∈ N5_even := by
    apply N5_even_finite (r % 162) (Nat.mod_lt r (by omega)) (by omega)
    intro j hj
    exact (digit₃_pow_periodic r (r % 162) rfl j hj).symm ▸ hN5 j hj
  have hr_mod : r % 162 = r := Nat.mod_eq_of_lt (by omega)
  rw [hr_mod] at hmem
  have hr162 : r < 162 := by omega
  -- r is even, in [48,68], and in N5_even → r ∈ {54, 56, 62}
  -- Extract this by noting N5_even ∩ [48,68] = {54, 56, 62}
  interval_cases r
  -- Odd r cases: contradiction with hr_even
  all_goals (try omega)
  -- Even r not in {54,56,62}: hmem gives contradiction after simp
  all_goals (simp only [N5_even, List.mem_cons, List.mem_nil_iff,
    false_or, or_false] at hmem; try exact absurd hmem (by decide))
  -- r = 54
  · refine ⟨5, by omega, K_star_gt_j 54 5 (by norm_num), ?_⟩
    unfold digit₃; norm_num [Nat.pow, Nat.div]
  -- r = 56
  · refine ⟨7, by omega, K_star_gt_j 56 7 (by norm_num), ?_⟩
    unfold digit₃; norm_num [Nat.pow, Nat.div]
  -- r = 62
  · refine ⟨6, by omega, K_star_gt_j 62 6 (by norm_num), ?_⟩
    unfold digit₃; norm_num [Nat.pow, Nat.div]

/-! ## Part G4.6: Low-position certificate for N5 values at positions 5-11
    For r ≥ 162*59049, periodicity from r' = r mod (162*59049) to r works
    for j ≤ 11 since 3^(j+1) | 162*59049 = 2*3^12.

    NOTE: r' ∈ {0, 2, 8} are excluded — these are the Cantor survivors where
    2^r' has NO digit-2 at positions 5-11. They require a separate argument
    using position 15+ and the ternary expansion of m = r / P. -/

private def N5_nonCantor : Finset Nat :=
  ⟨[20, 24, 26, 54, 56, 62, 72, 74, 78, 80, 96, 126, 150], by native_decide⟩

private theorem n5_low_digit_covers :
    ∀ r' ∈ N5_nonCantor, ∃ j ∈ Finset.range 7, digitMod r' (j + 5) = 2 := by
  native_decide

private theorem n5_low_digit_covers_full (r' : Nat) (hr' : r' ∈ N5_even_set)
    (hNC : r' ∉ ({0, 2, 8} : Finset Nat)) :
    ∃ j ∈ Finset.range 7, digitMod r' (j + 5) = 2 := by
  have hr'_eq : r' = 0 ∨ r' = 2 ∨ r' = 8 ∨ r' = 20 ∨ r' = 24 ∨ r' = 26 ∨
      r' = 54 ∨ r' = 56 ∨ r' = 62 ∨ r' = 72 ∨ r' = 74 ∨ r' = 78 ∨
      r' = 80 ∨ r' = 96 ∨ r' = 126 ∨ r' = 150 := by
    simp [N5_even_set, Finset.mem_mk, List.mem_toFinset] at hr'
    exact hr'
  rcases hr'_eq with ⟨rfl | rfl | rfl | ⟨rfl | rfl | rfl | ⟨rfl | rfl | rfl | ⟨rfl | rfl | rfl | ⟨rfl | rfl | rfl | ⟨rfl | rfl⟩⟩⟩⟩⟩⟩⟩⟩ with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · contradiction
  · contradiction
  · contradiction
  · exact n5_low_digit_covers 20 (by decide)
  · exact n5_low_digit_covers 24 (by decide)
  · exact n5_low_digit_covers 26 (by decide)
  · exact n5_low_digit_covers 54 (by decide)
  · exact n5_low_digit_covers 56 (by decide)
  · exact n5_low_digit_covers 62 (by decide)
  · exact n5_low_digit_covers 72 (by decide)
  · exact n5_low_digit_covers 74 (by decide)
  · exact n5_low_digit_covers 78 (by decide)
  · exact n5_low_digit_covers 80 (by decide)
  · exact n5_low_digit_covers 96 (by decide)
  · exact n5_low_digit_covers 126 (by decide)
  · exact n5_low_digit_covers 150 (by decide)

/-! ## Part G4.7: Cantor-survivor residue handling for large r
    For s ∈ {0, 2, 8} and r = s + P*m (P = 162*59049 = 2·3^14):
    Key identity: digitMod(r, 15) = m % 3

    Then by well-founded induction on m:
    - m % 3 = 2 → digit 15 = 2 → done
    - m % 3 = 0 → m = 3m', recurse on m' (digit 16 = m'%3)
    - m % 3 = 1 → m = 3m'+1, digit 16 = m'%3, recurse on m' -/

private def P : Nat := 162 * 59049
private def cantorSet : Finset Nat := {0, 2, 8}

private theorem two_pow_s_mod3 (s : Nat) (hs : s = 0 ∨ s = 2 ∨ s = 8) :
    2 ^ s % 3 = 1 := by rcases hs with rfl | rfl | rfl <;> norm_num

private theorem two_pow_s_lt_3_15 (s : Nat) (hs : s = 0 ∨ s = 2 ∨ s = 8) :
    2 ^ s < 3 ^ 15 := by
  have : 2^s ≤ 2^8 := Nat.pow_le_pow_right (by omega)
    (by rcases hs with rfl | rfl | rfl <;> omega)
  have : (2^8 : Nat) < 3^15 := by norm_num
  omega

private theorem one_plus_3pow15_pow_m (m : Nat) :
    (1 + 3 ^ 15) ^ m % 3 ^ 16 = (1 + m * 3 ^ 15) % 3 ^ 16 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Nat.mul_mod, ih, show (1 + 3 ^ 15) * (1 + m * 3 ^ 15) =
      1 + (m + 1) * 3 ^ 15 + m * 3 ^ 30 from by ring]
    rw [Nat.add_mod, Nat.add_mod]
    suffices m * 3 ^ 30 % 3 ^ 16 = 0 by rw [this, Nat.zero_add]
    exact Nat.mod_eq_zero_of_dvd
      (Nat.dvd_trans (⟨3 ^ 14, by norm_num⟩ : 3^16 ∣ 3^30) (Nat.dvd_mul_left _ m))

private theorem K_star_ge_16_of_ge_P (r : Nat) (hrP : r ≥ P) :
    16 ≤ K_star r := by
  have : 3^17 ≤ 2^r := by
    have h1 : (3^17 : Nat) ≤ 2^P := by unfold P; norm_num
    have h2 : 2^P ≤ 2^r := Nat.pow_le_pow_right (by omega : 0 < P) hrP
    omega
  exact Nat.succ_le_of_lt (K_star_gt_j r 16 this)

private theorem digitMod_cantor_P_m (s m : Nat) (hs : s = 0 ∨ s = 2 ∨ s = 8) :
    digitMod (s + P * m) 15 = m % 3 := by
  unfold digitMod
  rw [digit_eq_of_modPow (2^(s + P * m)) 15 16 (by omega)]
  rw [show 2^(s + P * m) = 2^s * 2^(P * m) from by ring]
  rw [show 2^(P * m) = (2^P)^m from by ring_nf; exact (pow_mul 2 P m).symm]
  rw [show P = 162 * 59049 from rfl]
  rw [Nat.mul_mod]
  rw [show 2^(162 * 59049) % 3^16 = 1 + 3^15 from two_pow_P_mod_16]
  rw [one_plus_3pow15_pow_m m, Nat.mul_mod]
  rw [Nat.mod_eq_of_lt (two_pow_s_lt_3_16 s hs)]
  have hs_le : s ≤ 8 := by rcases hs with rfl | rfl | rfl <;> omega
  have h315 : 2^s < 3^15 := two_pow_s_lt_3_15 s hs
  rw [show 2^s * (1 + m * 3^15) = 2^s + m * 2^s * 3^15 from by ring]
  rw [show (m * 2^s) * 3^15 = m * 2^s * 3^15 from by ring]
  rw [Nat.add_mod]
  have hmod_t315 : m * 2^s * 3^15 % 3^16 = (m * 2^s % 3) * 3^15 := by
    rw [show m * 2^s * 3^15 = (m * 2^s % 3 + 3 * (m * 2^s / 3)) * 3^15 from by
      rw [Nat.div_add_mod (m * 2^s) 3]; ring]
    rw [show ((m * 2^s % 3) + 3 * (m * 2^s / 3)) * 3^15 =
      (m * 2^s % 3) * 3^15 + (m * 2^s / 3) * 3^16 from by ring]
    rw [Nat.add_mod, show (m * 2^s / 3) * 3^16 % 3^16 = 0 from Nat.mod_eq_zero_of_dvd ⟨_, by ring⟩]
    exact Nat.mod_eq_of_lt (by
      have := Nat.mod_lt (m * 2^s) (by omega : 0 < 3)
      nlinarith [show (2 : Nat) * 3^15 < 3^16 from by norm_num])
  rw [hmod_t315]
  have hsum_lt : 2^s + (m * 2^s % 3) * 3^15 < 3^16 := by
    have := Nat.mod_lt (m * 2^s) (by omega : 0 < 3)
    nlinarith [show (2 : Nat) * 3^15 < 3^16 from by norm_num]
  rw [Nat.mod_eq_of_lt hsum_lt]
  rw [Nat.add_div (by omega : 0 < 3^15) (by ⟨m * 2^s % 3, by ring⟩ : 3^15 ∣ (m * 2^s % 3) * 3^15)]
  rw [Nat.div_eq_zero_of_lt h315, zero_add]
  rw [Nat.mul_div_cancel_left _ (by omega : 0 < 3^15)]
  rw [Nat.mod_mod_of_dvd (m * 2^s) (by omega : 3 ∣ 3)]
  rw [show m * 2^s % 3 = m * (2^s % 3) % 3 from by rw [Nat.mul_mod]]
  rw [two_pow_s_mod3 s hs, show m * 1 % 3 = m % 3 from by rw [Nat.mul_one]]

private theorem cantor_survivor_large_r (r : Nat) (hr : r > 8) (hr_even : r % 2 = 0)
    (hN5 : ∀ j < 5, digit₃ (2^r) j ∈ ({0, 1} : Finset Nat))
    (hrP : r ≥ P) (hs_cantor : r % P ∈ cantorSet) :
    ∃ j, 5 ≤ j ∧ j < K_star r ∧ digit₃ (2^r) j = 2 := by
  by_contra hno2
  push_neg at hno2
  -- Step 1: Show memCantorNat(2^r) from the assumption that no digit 2 exists
  have hCantor : memCantorNat (2^r) := by
    intro k
    by_cases hk : k < K_star r
    · -- k < K_star r: either k < 5 (from hN5) or 5 ≤ k (from hno2)
      by_cases hk5 : k < 5
      · have := hN5 k hk5
        simp [digit₃] at this ⊢
        interval_cases digit₃ (2^r) k <;> omega
      · have := hno2 k (by omega) hk
        simp [digit₃] at this ⊢
        interval_cases digit₃ (2^r) k <;> omega
    · -- k ≥ K_star r: digit₃(2^r) k = 0 since 2^r < 3^(K_star r) ≤ 3^k
      unfold digit₃
      have hlt : 2 ^ r < 3 ^ k := by
        have := two_pow_lt_three_pow_succ r
        have hkk : K_star r + 1 ≤ k := by omega
        calc 2 ^ r < 3 ^ (K_star r + 1) := two_pow_lt_three_pow_succ r
          _ ≤ 3 ^ k := Nat.pow_le_pow_right (by omega) hkk
      rw [Nat.div_eq_zero_of_lt hlt]
      simp
  -- Step 2: Decompose r = s + P*m
  have hrP' : P > 0 := by unfold P; omega
  set s := r % P with hs_def
  set m := r / P with hm_def
  have hr_eq : r = s + P * m := by omega
  have hs_mem : s ∈ cantorSet := hs_cantor
  have hs_val : s = 0 ∨ s = 2 ∨ s = 8 := by
    simp [cantorSet] at hs_mem; exact hs_mem
  have hm_pos : m > 0 := by
    by_contra h0
    push_neg at h0
    have : m = 0 := by omega
    rw [this, Nat.mul_zero, Nat.add_zero] at hr_eq
    subst hr_eq
    exact absurd hs_mem (by
      simp [cantorSet]
      rcases hs_val with rfl | rfl | rfl <;> simp)
  -- Step 3: Apply cantor_exceptional_forces_zero to get m = 0
  have hP_eq_uK : P = uK 15 := by unfold P uK; norm_num
  have huK15_pos : uK 15 > 0 := uK_pos' 15
  have hs_lt : s < uK 15 := by
    rw [← hP_eq_uK]; exact Nat.mod_lt _ hrP'
  have hCantor' : memCantorNat (2 ^ (s + m * uK 15)) := by
    rw [hP_eq_uK] at hr_eq; rw [← hr_eq]; exact hCantor
  have hm0 := cantor_exceptional_forces_zero s m 15 hs_val (by omega) hs_lt hCantor'
  omega

/-! ## Part G4: Main theorem -/

private theorem two_pow_mod_three_eq_two_of_odd (r : Nat) (hr : r % 2 = 1) : 2 ^ r % 3 = 2 := by
  have h2pow : ∀ n, 2 ^ (2 * n) % 3 = 1 := by
    intro n; induction n with
    | zero => norm_num
    | succ n ih =>
      rw [show 2 * (n + 1) = 2 * n + 2 from by omega, pow_add, pow_two]
      rw [Nat.mul_mod, ih]; norm_num
  have : r = 2 * (r / 2) + 1 := by omega
  rw [this, pow_add, pow_one, Nat.mul_mod, h2pow (r / 2)]

theorem criticalGap_has_digit2_of_gt8 (r : Nat) (hr : r > 8) :
    ∃ i, digit₃ (criticalGap r) i = 2 := by
  rcases le_or_lt r 47 with hr47 | hr48
  · exact criticalGap_has_digit2_of_range r (by omega) hr47
  · -- r ≥ 48
    have hr48' : r ≥ 48 := by omega
    by_cases hr_odd : r % 2 = 1
    · -- Odd r: digit_0(criticalGap r) = digit_0(2^r) = 2
      have hK : 0 < K_star r := by
        have h2r := two_pow_lt_three_pow_succ r
        by_contra hle
        have hK0 : K_star r = 0 := by omega
        rw [hK0, Nat.pow_one] at h2r
        have : 2^r < 3 := h2r
        have h48 : 2^r ≥ 2^48 := Nat.pow_le_pow_right (by omega) hr48'
        have : (2^48 : Nat) < 3 := by omega
        norm_num at this
      exact ⟨0, by
        rw [digit₃_criticalGap_eq r 0 hK]
        unfold digit₃
        simp only [Nat.pow_zero, Nat.div_one]
        exact two_pow_mod_three_eq_two_of_odd r hr_odd⟩
    · -- Even r ≥ 48
      have hr_even : r % 2 = 0 := by omega
      by_cases hN5 : ∀ j < 5, digit₃ (2^r) j ∈ ({0, 1} : Finset Nat)
      · -- r is N5
        rcases le_or_lt r 68 with hr68 | hr69
        · -- 48 ≤ r ≤ 68: N5 residues are {54, 56, 62}, handle directly
          obtain ⟨j, hj5, hjK, hj2⟩ := n5_small_range_covers r hr48' hr68 hr_even hN5
          exact ⟨j, by rw [digit₃_criticalGap_eq r j hjK]; exact hj2⟩
        · -- r ≥ 69
          rcases le_or_lt r (162 * 59049 - 1) with hr_small | hr_large
          · obtain ⟨j, hj5, hjK, hj2⟩ := n5_covers_transfer r hr69 hr_small hr_even hN5
            exact ⟨j, by rw [digit₃_criticalGap_eq r j hjK]; exact hj2⟩
          · -- r ≥ 162*59049: use low-position certificate + periodicity
              have hs_mem' : r % (162 * 59049) ∈ N5_even_set := by
                apply N5_even_finite (r % (162 * 59049))
                  (Nat.mod_lt r (by norm_num : 0 < 162 * 59049)) (by omega)
                intro j hj
                exact (digit₃_pow_periodic r _ rfl j hj).symm ▸ hN5 j hj
              -- Split: Cantor survivors {0,2,8} need position 15+; others use positions 5-11
              by_cases hs_cantor : r % (162 * 59049) ∈ cantorSet
              · -- Cantor survivor residue: use position 15+ argument
                exact cantor_survivor_large_r r hr hr_even hN5 hr_large hs_cantor
              · -- Non-Cantor residue: use positions 5-11 via periodicity
                obtain ⟨dj, hdj_range, hdj2⟩ := n5_low_digit_covers_full
                  (r % (162 * 59049)) hs_mem' hs_cantor
                have hdj7 : dj < 7 := by simp [Finset.mem_range] at hdj_range; exact hdj_range
                have h162k : 2^(162*59049) % 3^(dj+6) = 1 := two_pow_P_mod (dj+5) (by omega)
                have hdj_transfer : digitMod r (dj + 5) = 2 := by
                  rw [Nat.mod_add_div r (162 * 59049)] at hdj2
                  unfold digitMod at hdj2 ⊢
                  rw [digit_eq_of_modPow (2^r) (dj+5) (dj+6) (by omega),
                      digit_eq_of_modPow (2^(r%(162*59049))) (dj+5) (dj+6) (by omega)]
                  suffices h : 2^r % 3^(dj+6) = 2^(r%(162*59049)) % 3^(dj+6) by rw [h]
                  rw [show r = (r%(162*59049)) + 162*59049*(r/(162*59049)) from by omega]
                  suffices key : ∀ k, 2^((r%(162*59049)) + 162*59049*k) % 3^(dj+6) =
                    2^(r%(162*59049)) % 3^(dj+6) from key (r/(162*59049))
                  intro k; induction k with
                  | zero => simp
                  | succ k ih =>
                    rw [show (r%(162*59049)) + 162*59049*(k+1) =
                         ((r%(162*59049)) + 162*59049*k) + 162*59049 from by omega,
                        pow_add, Nat.mul_mod, ih, h162k, Nat.one_mul,
                        Nat.mod_mod_of_dvd _ (by omega : 2 ∣ 162 * 59049)]
                have hdj3 : digit₃ (2^r) (dj + 5) = 2 := by
                  rw [digitMod_eq_digit₃] at hdj_transfer; exact hdj_transfer
                exact ⟨dj + 5, by omega, by
                  have h3j : 3^((dj+5)+1) ≤ 3^12 := Nat.pow_le_pow_right (by omega) (by omega)
                  have h2r : 3^12 ≤ 2^r := by
                    have h48 : 2^48 ≤ 2^r := Nat.pow_le_pow_right (by omega) hr48'
                    have : (2^48 : Nat) ≥ 3^12 := by norm_num
                    omega
                  exact K_star_gt_j r (dj+5) (le_trans h3j h2r), hdj3⟩
      · -- r not N5: low-digit obstruction
        obtain ⟨j, hjK, hj2⟩ := even_not_N5_digit2_below_K r hr48' hr_even hN5
        exact ⟨j, by rw [digit₃_criticalGap_eq r j hjK]; exact hj2⟩

/-! ## Part H: Complete Conjecture -/

private lemma small_r_check (r : Nat) (hr : r ≤ 8) (hc : memCantorNat (2 ^ r)) :
    r = 0 ∨ r = 2 ∨ r = 8 := by
  have hr9 : r < 9 := by omega
  interval_cases r <;> try exact Or.inl rfl
  · exact absurd hc (by intro hc; exact hc 0 (by norm_num [digit₃]))
  · exact Or.inr (Or.inl rfl)
  · exact absurd hc (by intro hc; exact hc 0 (by norm_num [digit₃]))
  · exact absurd hc (by intro hc; exact hc 1 (by norm_num [digit₃]))
  · exact absurd hc (by intro hc; exact hc 0 (by norm_num [digit₃]))
  · exact absurd hc (by intro hc; exact hc 3 (by norm_num [digit₃]))
  · exact absurd hc (by intro hc; exact hc 2 (by norm_num [digit₃]))
  · exact Or.inr (Or.inr rfl)

theorem erdos_conjecture_via_critical_invariant (r : Nat)
    (hc : memCantorNat (2 ^ r)) : r = 0 ∨ r = 2 ∨ r = 8 := by
  rcases Nat.lt_or_ge r 9 with hr | hr
  · exact small_r_check r (by omega) hc
  · exfalso; have h8 : r > 8 := by omega
    obtain ⟨i, hi⟩ := criticalGap_has_digit2_of_gt8 r h8
    have h_no2 := memCantorNat_imp_criticalGap_no_digit2 hc i
    have hi_ge : i ≥ K_star r := by by_contra h; push_neg at h; exact h_no2 h hi
    have hi_eq : i = K_star r := by
      by_contra h; have : i > K_star r := by omega
      rw [criticalGap_digit_gt_K_star r i this] at hi; norm_num at hi
    rw [hi_eq] at hi; exact criticalGap_digit_K_star_ne_two r hi

end ErdosTernary.CriticalInvariant
