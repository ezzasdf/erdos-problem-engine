/-
  CriticalInvariant.lean — The Critical-Level Invariant
  If 2^r is Cantor, then r ∈ {0, 2, 8}.
-/
import Mathlib.Tactic
import ErdosTernary.BridgeCompute
import ErdosTernary.Narkiewicz
import ErdosTernary.LiftingDynamics
import ErdosTernary.BlockClassification

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
    simp [N5_even_set, Finset.mem_mk, List.mem_toFinset, N5_even] at hr'
    exact hr'
  rcases hr'_eq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd (by simp : (0 : Nat) ∈ ({0, 2, 8} : Finset Nat)) hNC
  · exact absurd (by simp : (2 : Nat) ∈ ({0, 2, 8} : Finset Nat)) hNC
  · exact absurd (by simp : (8 : Nat) ∈ ({0, 2, 8} : Finset Nat)) hNC
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
    rw [pow_succ, Nat.mul_mod, ih, ← Nat.mul_mod, show (1 + m * 3 ^ 15) * (1 + 3 ^ 15) =
      1 + (m + 1) * 3 ^ 15 + m * 3 ^ 30 from by ring]
    rw [Nat.add_mod]
    have h30 : m * 3 ^ 30 % 3 ^ 16 = 0 :=
      Nat.mod_eq_zero_of_dvd
        (Nat.dvd_trans (⟨3 ^ 14, by norm_num⟩ : 3^16 ∣ 3^30) (Nat.dvd_mul_left _ m))
    rw [h30, Nat.add_zero]
    rw [Nat.mod_mod_of_dvd (1 + (m + 1) * 3 ^ 15) ⟨1, by ring⟩]

private theorem K_star_ge_16_of_ge_P (r : Nat) (hrP : r ≥ P) :
    16 ≤ K_star r := by
  have hP28 : P ≥ 28 := by unfold P; norm_num
  have h317 : (3 : Nat) ^ 17 ≤ 2 ^ 28 := by norm_num
  have h28r : 2 ^ 28 ≤ 2 ^ r :=
    Nat.pow_le_pow_right (by norm_num : (0 : Nat) < 2)
      (le_trans hP28 hrP)
  have h317r : (3 : Nat) ^ 17 ≤ 2 ^ r := le_trans h317 h28r
  exact le_of_lt (K_star_gt_j r 16 h317r)

/-- 2^P mod 3^16 = 1 + 3^15 (via BlockClassification's literal pow2Pmod30). -/
private theorem two_pow_P_mod_16 : (2 : Nat) ^ (162 * 59049) % 3 ^ 16 = 1 + 3 ^ 15 := by
  have h30 : (2 : Nat) ^ (162 * 59049) % 3 ^ 30 =
      ErdosTernary.BlockClassification.pow2Pmod30 := by
    rw [show 162 * 59049 = ErdosTernary.BlockClassification.P from by decide]
    rw [← ErdosTernary.BlockClassification.pow2Pmod30_eq]
  have h16 : (2 : Nat) ^ (162 * 59049) % 3 ^ 16 =
      ErdosTernary.BlockClassification.pow2Pmod30 % 3 ^ 16 := by
    rw [show (2 : Nat) ^ (162 * 59049) % 3 ^ 16 =
      (2 ^ (162 * 59049) % 3 ^ 30) % 3 ^ 16 from
        (Nat.mod_mod_of_dvd (2 ^ (162 * 59049)) ⟨3 ^ 14, by rw [← Nat.pow_add]⟩).symm]
    rw [h30]
  rw [h16]
  norm_num [ErdosTernary.BlockClassification.pow2Pmod30]

private theorem digitMod_cantor_P_m (s m : Nat) (hs : s = 0 ∨ s = 2 ∨ s = 8) :
    digitMod (s + P * m) 15 = m % 3 := by
  unfold digitMod
  rw [show 2^(s + P * m) = 2^s * 2^(P * m) from by ring]
  rw [show 2^(P * m) = (2^P)^m from by ring_nf]
  rw [show P = 162 * 59049 from rfl]
  rw [Nat.mul_mod]
  rw [show 15 + 1 = 16 from rfl]
  rw [show ((2 ^ (162 * 59049)) ^ m % 3 ^ 16) =
      ((2 ^ (162 * 59049) % 3 ^ 16) ^ m % 3 ^ 16) from Nat.pow_mod _ _ _]
  rw [show 2 ^ (162 * 59049) % 3 ^ 16 = 1 + 3 ^ 15 from two_pow_P_mod_16]
  rw [one_plus_3pow15_pow_m m]
  rw [Nat.mod_eq_of_lt (lt_trans (two_pow_s_lt_3_15 s hs)
    (by norm_num : (3 : Nat) ^ 15 < 3 ^ 16))]
  rw [show 2 ^ s * ((1 + m * 3 ^ 15) % 3 ^ 16) % 3 ^ 16 =
      (2 ^ s * (1 + m * 3 ^ 15)) % 3 ^ 16 from by
    rw [Nat.mul_mod, Nat.mod_mod_of_dvd (1 + m * 3 ^ 15) ⟨1, by ring⟩]
    rw [← Nat.mul_mod]]
  have hs_le : s ≤ 8 := by rcases hs with rfl | rfl | rfl <;> omega
  have h315 : 2^s < 3^15 := two_pow_s_lt_3_15 s hs
  rw [show 2^s * (1 + m * 3^15) = 2^s + m * 2^s * 3^15 from by ring]
  rw [show (m * 2^s) * 3^15 = m * 2^s * 3^15 from by ring]
  rw [Nat.add_mod]
  have hmod_t315 : m * 2^s * 3^15 % 3^16 = (m * 2^s % 3) * 3^15 := by
    rw [show m * 2^s * 3^15 = (m * 2^s % 3 + 3 * (m * 2^s / 3)) * 3^15 from by
      rw [show m * 2^s % 3 + 3 * (m * 2^s / 3) = 3 * (m * 2^s / 3) + m * 2^s % 3 from by ring,
        Nat.div_add_mod (m * 2^s) 3]]
    rw [show ((m * 2^s % 3) + 3 * (m * 2^s / 3)) * 3^15 =
      (m * 2^s % 3) * 3^15 + (m * 2^s / 3) * 3^16 from by ring]
    rw [Nat.add_mod, show (m * 2^s / 3) * 3^16 % 3^16 = 0 from Nat.mod_eq_zero_of_dvd ⟨_, by ring⟩,
      Nat.add_zero]
    rw [Nat.mod_mod_of_dvd ((m * 2 ^ s % 3) * 3 ^ 15) ⟨1, by ring⟩]
    exact Nat.mod_eq_of_lt (by
      have hyle2 : m * 2 ^ s % 3 ≤ 2 := by omega
      have hmul : (m * 2 ^ s % 3) * 3 ^ 15 ≤ 2 * 3 ^ 15 := Nat.mul_le_mul_right (3 ^ 15) hyle2
      have h2 : (2 : Nat) * 3 ^ 15 < 3 ^ 16 := by norm_num
      exact lt_of_le_of_lt hmul h2)
  rw [hmod_t315]
  have hsum_lt : 2^s + (m * 2^s % 3) * 3^15 < 3^16 := by
    have hyle2 : m * 2 ^ s % 3 ≤ 2 := by omega
    have hmul : (m * 2 ^ s % 3) * 3 ^ 15 ≤ 2 * 3 ^ 15 := Nat.mul_le_mul_right (3 ^ 15) hyle2
    have hsb : 2 ^ s ≤ 256 :=
      le_trans (Nat.pow_le_pow_right (by norm_num : (0 : Nat) < 2) hs_le) (by norm_num)
    have h256 : (256 : Nat) + 2 * 3 ^ 15 < 3 ^ 16 := by norm_num
    exact lt_of_le_of_lt (Nat.add_le_add hsb hmul) h256
  rw [Nat.mod_eq_of_lt (lt_trans h315 (by norm_num : (3 : Nat) ^ 15 < 3 ^ 16))]
  rw [Nat.mod_eq_of_lt hsum_lt]
  rw [Nat.add_mul_div_right (2 ^ s) (m * 2 ^ s % 3) (by omega : (0 : Nat) < 3 ^ 15)]
  rw [Nat.div_eq_of_lt h315, zero_add]
  rw [Nat.mod_eq_of_lt (by omega : m * 2 ^ s % 3 < 3)]
  rw [show m * 2 ^ s % 3 = m % 3 from by
    rw [Nat.mul_mod, two_pow_s_mod3 s hs, Nat.mul_one,
      Nat.mod_mod_of_dvd m (by omega : 3 ∣ 3)]]

/-! ## Part G6: G_j locality and transition recurrence (validated in gj_validate.py)

    digit_shift_locality: q ≡ q' (mod 3^(j+1)) → digit_{15+j}(2^(ρ+P·q)) agrees.
    Proof: P·3^(j+1) = 2·3^(15+j) = φ(3^(16+j)), so 2^(P·3^(j+1)) ≡ 1 (mod 3^(16+j))
    by Euler (Nat.ModEq.pow_totient); digit extraction via digit_eq_of_modPow.

    digit_shift_recurrence: X_{j+1}(q + d·3^(j+1)) = X_{j+1}(q)·w^d (mod 3^(17+j))
    with w = ((2^P)^(3^(j+1)))^d mod 3^(17+j) — the exact G_j transition
    (state space bijective of size 3^(j+2); recurrence validated j ≤ 10). -/

private theorem gj_P_eq : P = 2 * 3 ^ 14 := by unfold P; norm_num

private theorem gj_totient_3_16_add (j : Nat) :
    Nat.totient (3 ^ (16 + j)) = 2 * 3 ^ (15 + j) := by
  rw [Nat.totient_prime_pow (by decide : Nat.Prime 3) (by omega : 0 < 16 + j)]
  rw [show 16 + j - 1 = 15 + j from by omega]
  ring

private theorem two_pow_periodic_mod_3_pow (j : Nat) :
    (2 ^ (P * 3 ^ (j + 1))) % 3 ^ (16 + j) = 1 := by
  have hc : Nat.Coprime 2 (3 ^ (16 + j)) :=
    Nat.Coprime.pow_right _ (by decide : Nat.Coprime 2 3)
  have hmod := Nat.ModEq.pow_totient hc
  have key : Nat.totient (3 ^ (16 + j)) = P * 3 ^ (j + 1) := by
    rw [gj_totient_3_16_add, gj_P_eq,
      show 2 * 3 ^ 14 * 3 ^ (j + 1) = 2 * (3 ^ 14 * 3 ^ (j + 1)) from by ring,
      ← Nat.pow_add, show 14 + (j + 1) = 15 + j from by omega]
  rw [key] at hmod
  have h1 : 1 % 3 ^ (16 + j) = 1 := Nat.mod_eq_of_lt
    (lt_of_lt_of_le (by norm_num : (1 : Nat) < 3)
      (Nat.pow_le_pow_right (by norm_num : (0 : Nat) < 3) (by omega : 1 ≤ 16 + j)))
  have hm2 : 2 ^ (P * 3 ^ (j + 1)) % 3 ^ (16 + j) = 1 % 3 ^ (16 + j) := hmod
  rw [h1] at hm2
  exact hm2

private theorem digit_shift_step (ρ y j : Nat) :
    2 ^ (ρ + P * (y + 3 ^ (j + 1))) % 3 ^ (16 + j) =
    2 ^ (ρ + P * y) % 3 ^ (16 + j) := by
  have hadd : ρ + P * (y + 3 ^ (j + 1)) = (ρ + P * y) + P * 3 ^ (j + 1) := by ring
  rw [hadd]
  rw [Nat.pow_add 2 (ρ + P * y) (P * 3 ^ (j + 1))]
  rw [Nat.mul_mod]
  rw [two_pow_periodic_mod_3_pow j]
  rw [Nat.mul_one]
  exact Nat.mod_eq_of_lt (Nat.mod_lt _ (Nat.pow_pos (by omega)))

/-- Locality of the G_j digits: q ≡ q' (mod 3^(j+1)) implies that digit 15+j of
    2^(ρ+P·q) equals digit 15+j of 2^(ρ+P·q'). -/
theorem digit_shift_locality (ρ q q' j : Nat)
    (h : q % 3 ^ (j + 1) = q' % 3 ^ (j + 1)) :
    digit₃ (2 ^ (ρ + P * q)) (15 + j) = digit₃ (2 ^ (ρ + P * q')) (15 + j) := by
  have key : ∀ k x, 2 ^ (ρ + P * (x + 3 ^ (j + 1) * k)) % 3 ^ (16 + j) =
      2 ^ (ρ + P * x) % 3 ^ (16 + j) := by
    intro k; induction k with
    | zero => intro x; rw [Nat.mul_zero, Nat.add_zero]
    | succ k ih =>
      intro x
      rw [show 3 ^ (j + 1) * (k + 1) = 3 ^ (j + 1) * k + 3 ^ (j + 1) from by ring,
          ← Nat.add_assoc x (3 ^ (j + 1) * k) (3 ^ (j + 1)),
          digit_shift_step ρ (x + 3 ^ (j + 1) * k) j]
      exact ih x
  have heq_q : q = q % 3 ^ (j + 1) + 3 ^ (j + 1) * (q / 3 ^ (j + 1)) := by
    rw [add_comm (q % 3 ^ (j + 1)) (3 ^ (j + 1) * (q / 3 ^ (j + 1))),
        Nat.div_add_mod]
  have heq_q' : q' = q' % 3 ^ (j + 1) + 3 ^ (j + 1) * (q' / 3 ^ (j + 1)) := by
    rw [add_comm (q' % 3 ^ (j + 1)) (3 ^ (j + 1) * (q' / 3 ^ (j + 1))),
        Nat.div_add_mod]
  suffices hmod : 2 ^ (ρ + P * q) % 3 ^ (16 + j) = 2 ^ (ρ + P * q') % 3 ^ (16 + j) by
    unfold digit₃
    rw [digit_eq_of_modPow (2 ^ (ρ + P * q)) (15 + j) (16 + j) (by omega),
        digit_eq_of_modPow (2 ^ (ρ + P * q')) (15 + j) (16 + j) (by omega),
        hmod]
  rw [heq_q, heq_q', h]
  exact (key (q / 3 ^ (j + 1)) (q' % 3 ^ (j + 1))).trans
    (key (q' / 3 ^ (j + 1)) (q' % 3 ^ (j + 1))).symm

/-- Transition recurrence for the G_j states: with X_{j+1}(q) = 2^(ρ+P·q) mod 3^(17+j),
    X_{j+1}(q + d·3^(j+1)) = X_{j+1}(q)·w^d mod 3^(17+j) where
    w^d = ((2^P)^(3^(j+1)))^d mod 3^(17+j) (equal to (X_{j+1}(q)·w_j^d) mod 3^(17+j)
    for w_j = (2^P)^(3^(j+1)) mod 3^(17+j), by Nat.mul_mod). -/
theorem digit_shift_recurrence (ρ q d j : Nat) :
    2 ^ (ρ + P * (q + d * 3 ^ (j + 1))) % 3 ^ (17 + j) =
    2 ^ (ρ + P * q) % 3 ^ (17 + j) *
      (((2 ^ P) ^ (3 ^ (j + 1))) ^ d % 3 ^ (17 + j)) % 3 ^ (17 + j) := by
  have hadd : ρ + P * (q + d * 3 ^ (j + 1)) = (ρ + P * q) + P * (d * 3 ^ (j + 1)) := by ring
  have hpow : 2 ^ (P * (d * 3 ^ (j + 1))) = ((2 ^ P) ^ (3 ^ (j + 1))) ^ d := by
    rw [show P * (d * 3 ^ (j + 1)) = (P * 3 ^ (j + 1)) * d from by ring, pow_mul, pow_mul]
  rw [hadd]
  rw [Nat.pow_add 2 (ρ + P * q) (P * (d * 3 ^ (j + 1)))]
  rw [hpow]
  exact Nat.mul_mod _ _ _

/-- Digit corollary of the recurrence: digit 16+j of 2^(ρ+P·(q+d·3^(j+1))) equals
    digit 16+j of the residue product X_{j+1}(q)·w^d. -/
theorem digit_shift_recurrence_digit (ρ q d j : Nat) :
    digit₃ (2 ^ (ρ + P * (q + d * 3 ^ (j + 1)))) (16 + j) =
    digit₃ (2 ^ (ρ + P * q) % 3 ^ (17 + j) *
      (((2 ^ P) ^ (3 ^ (j + 1))) ^ d % 3 ^ (17 + j))) (16 + j) := by
  have hi : 16 + j < 17 + j := by omega
  unfold digit₃
  rw [digit_eq_of_modPow (2 ^ (ρ + P * (q + d * 3 ^ (j + 1)))) (16 + j) (17 + j) hi]
  rw [digit_eq_of_modPow (2 ^ (ρ + P * q) % 3 ^ (17 + j) *
      (((2 ^ P) ^ (3 ^ (j + 1))) ^ d % 3 ^ (17 + j))) (16 + j) (17 + j) hi]
  rw [digit_shift_recurrence]

/-- Any digit-2 of 2^r below K_star r is a digit-2 of criticalGap r. -/
private theorem criticalGap_digit2_of_digitMod (r j : Nat) (hj : j < K_star r)
    (hd : digitMod r j = 2) : ∃ i, digit₃ (criticalGap r) i = 2 := by
  refine ⟨j, ?_⟩
  rw [digit₃_criticalGap_eq r j hj]
  rw [← digitMod_eq_digit₃]
  exact hd

/-- For r >= P, positions 5..300 all lie below K_star r (3^301 <= 2^478 <= 2^P <= 2^r). -/
private theorem digit_window_lt_K_star (r : Nat) (hrP : r ≥ 162 * 59049)
    (hj : j ≤ 300) : j < K_star r := by
  have h3 : (3 : Nat) ^ 301 ≤ 2 ^ r := by
    have h1 : (3 : Nat) ^ 301 ≤ 2 ^ 478 := by norm_num
    have h2 : (2 : Nat) ^ 478 ≤ 2 ^ (162 * 59049) :=
      Nat.pow_le_pow_right (by norm_num : (0 : Nat) < 2) (by norm_num)
    have h3' : (2 : Nat) ^ (162 * 59049) ≤ 2 ^ r :=
      Nat.pow_le_pow_right (by norm_num : (0 : Nat) < 2) (by omega)
    exact le_trans h1 (le_trans h2 h3')
  exact lt_of_le_of_lt hj (K_star_gt_j r 300 h3)

private theorem cantor_survivor_large_r (r : Nat) (hc : memCantorNat (2 ^ r))
    (hr : r > 8) (hr_even : r % 2 = 0)
    (hN5 : ∀ j < 5, digit₃ (2^r) j ∈ ({0, 1} : Finset Nat))
    (hrP : r ≥ P) (hs_cantor : r % P ∈ cantorSet) :
    ∃ j, 5 ≤ j ∧ j < K_star r ∧ digit₃ (2^r) j = 2 := by
  -- Step 1: memCantorNat is threaded from the caller (erdos_conjecture_via_critical_invariant).
  -- The previous in-proof reconstruction was removed: it was unprovable at k = K_star r
  -- (leading digit can be 2 under the by-contra assumptions).
  have hCantor : memCantorNat (2^r) := hc
  -- Step 2: Decompose r = s + P*m
  have hrP' : P > 0 := by unfold P; omega
  set s := r % P with hs_def
  set m := r / P with hm_def
  have hr_eq : r = s + P * m := by
    rw [hs_def, hm_def]
    rw [Nat.add_comm (r % P) (P * (r / P))]
    exact (Nat.div_add_mod r P).symm
  have hs_mem : s ∈ cantorSet := hs_cantor
  have hs_val : s = 0 ∨ s = 2 ∨ s = 8 := by
    simp [cantorSet] at hs_mem; exact hs_mem
  have hm_pos : m > 0 := by
    rw [hm_def]
    exact Nat.div_pos hrP (by omega : (0 : Nat) < P)
  -- Step 3: Apply cantor_exceptional_forces_zero to get m = 0
  have hP_eq_uK : P = uK 15 := by unfold P uK; norm_num
  have huK15_pos : uK 15 > 0 := by unfold uK; omega
  have hs_lt : s < uK 15 := by
    rw [← hP_eq_uK]; exact Nat.mod_lt _ hrP'
  have hCantor' : memCantorNat (2 ^ (s + m * uK 15)) := by
    rw [show s + m * uK 15 = s + P * m from by rw [hP_eq_uK]; ring]
    rw [← hr_eq]; exact hCantor
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

theorem criticalGap_has_digit2_of_gt8 (r : Nat) (hc : memCantorNat (2 ^ r))
    (hr : r > 8) :
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
          · obtain ⟨j, hj5, hjK, hj2⟩ := n5_covers_transfer r hr69
              (by omega : r < 162 * 59049) hr_even hN5
            exact ⟨j, by rw [digit₃_criticalGap_eq r j hjK]; exact hj2⟩
          · -- r ≥ 162*59049: low-position certificate + periodicity
              by_cases hs_cantor : r % (162 * 59049) ∈ cantorSet
              · -- Cantor survivor residue: position 15+ argument (hc threaded from caller)
                obtain ⟨j, hj5, hjK, hj2⟩ := cantor_survivor_large_r r hc hr hr_even hN5
                  hr_large hs_cantor
                exact ⟨j, by rw [digit₃_criticalGap_eq r j hjK]; exact hj2⟩
              · -- Non-Cantor residue ρ = r % (162 * 59049), ρ ∉ {0, 2, 8}
                rcases lt_or_ge (r % (162 * 59049)) 162 with hρ162 | hρ162
                · -- ρ < 162: N5 certificate applies to ρ itself; the P-period
                  -- (2^P ≡ 1 mod 3^15) transfers positions ≤ 14 from ρ to r.
                  have hρeq : r % 162 = r % (162 * 59049) := by
                    have h1 : r % (162 * 59049) % 162 = r % 162 :=
                      Nat.mod_mod_of_dvd r ⟨59049, by ring⟩
                    rw [Nat.mod_eq_of_lt hρ162] at h1
                    exact h1.symm
                  have hs_mem' : r % (162 * 59049) ∈ N5_even_set := by
                    apply N5_even_finite (r % (162 * 59049)) hρ162 (by omega)
                    intro j hj
                    have hp := digit₃_pow_periodic r (r % 162) rfl j hj
                    rw [hρeq] at hp
                    rw [← hp]; exact hN5 j hj
                  obtain ⟨dj, hdj_range, hdj2⟩ := n5_low_digit_covers_full
                    (r % (162 * 59049)) hs_mem' (by simpa [cantorSet] using hs_cantor)
                  have hdj7 : dj < 7 := by simp [Finset.mem_range] at hdj_range; exact hdj_range
                  have h162k : 2^(162*59049) % 3^(dj+6) = 1 := two_pow_P_mod (dj+5) (by omega)
                  have hdj_transfer : digitMod r (dj + 5) = 2 := by
                    unfold digitMod at hdj2 ⊢
                    suffices h : 2 ^ r % 3 ^ (dj + 6) =
                        2 ^ (r % (162 * 59049)) % 3 ^ (dj + 6) by
                      rw [h]; exact hdj2
                    conv_lhs => rw [show r = (r % (162 * 59049)) + 162 * 59049 * (r / (162 * 59049))
                      from by omega]
                    have key : ∀ k, 2 ^ ((r % (162 * 59049)) + 162 * 59049 * k)
                          % 3 ^ (dj + 6) = 2 ^ (r % (162 * 59049)) % 3 ^ (dj + 6) := by
                      intro k; induction k with
                      | zero => simp
                      | succ k ih =>
                        rw [show (r % (162 * 59049)) + 162 * 59049 * (k + 1) =
                             ((r % (162 * 59049)) + 162 * 59049 * k) + 162 * 59049
                             from by omega,
                            pow_add, Nat.mul_mod, ih, h162k, Nat.mul_one]
                        rw [Nat.mod_mod_of_dvd (2 ^ (r % (162 * 59049))) ⟨1, by ring⟩]
                    exact key (r / (162 * 59049))
                  have hdj3 : digit₃ (2^r) (dj + 5) = 2 := by
                    rw [digitMod_eq_digit₃] at hdj_transfer; exact hdj_transfer
                  exact ⟨dj + 5, by
                    have h3j : 3 ^ ((dj + 5) + 1) ≤ 3 ^ 12 :=
                      Nat.pow_le_pow_right (by omega : (1 : Nat) ≤ 3) (by omega)
                    have h2r : 3 ^ 12 ≤ 2 ^ r := by
                      have h48 : 2 ^ 48 ≤ 2 ^ r :=
                        Nat.pow_le_pow_right (by omega : (1 : Nat) ≤ 2) hr48'
                      have : (2 ^ 48 : Nat) ≥ 3 ^ 12 := by norm_num
                      omega
                    have hjK : dj + 5 < K_star r := K_star_gt_j r (dj + 5) (le_trans h3j h2r)
                    rw [digit₃_criticalGap_eq r (dj + 5) hjK]
                    exact hdj3⟩
                · -- ρ ≥ 162: P4 hit-split + fixed digit window [15, 61)
                  -- (P4) Exceptional state at level 6: uK 6 = 486 | P, so
                  -- r mod 486 = ρ mod 486; if that state is in {0,2,8},
                  -- cantor_exceptional_forces_zero at K=6 gives r/6 = 0,
                  -- hence r = r mod 486 < 486 < P ≤ r — contradiction.
                  by_cases h486 : r % 486 ∈ ({0, 2, 8} : Finset Nat)
                  · have huK6 : uK 6 = 486 := by norm_num [uK]
                    have hs_val : r % uK 6 = 0 ∨ r % uK 6 = 2 ∨ r % uK 6 = 8 := by
                      rw [huK6]
                      simp only [Finset.mem_insert, Finset.mem_singleton] at h486
                      exact h486
                    have hre : r = r % uK 6 + (r / uK 6) * uK 6 := by
                      have h := Nat.div_add_mod r (uK 6)
                      rw [mul_comm, add_comm] at h
                      exact h.symm
                    have hq0 : r / uK 6 = 0 :=
                      cantor_exceptional_forces_zero (r % uK 6) (r / uK 6) 6
                        hs_val (by omega)
                        (Nat.mod_lt r (by norm_num [uK] : (0 : Nat) < uK 6))
                        (by rw [← hre]; exact hc)
                    exfalso
                    have hlt : r < 486 := by
                      rw [hre, hq0, Nat.zero_mul, Nat.add_zero, huK6]
                      exact Nat.mod_lt r (by norm_num : (0 : Nat) < 486)
                    omega
                  · rcases em (∃ j, 5 ≤ j ∧ j < 301 ∧ digitMod r j = 2)
                      with ⟨j, hj5, hj61, hd⟩ | hclean
                    · exact criticalGap_digit2_of_digitMod r j
                        (digit_window_lt_K_star r (by omega) (by omega)) hd
                    · -- RESIDUAL SORRY (scoped): rho >= 162, rho notin {0,2,8},
                      -- rho mod 486 notin {0,2,8}, and every digit 5..300 of 2^r
                      -- differs from 2 (no digit-2 in the window [5, 301)).
                      -- Positions 5..14 subsume the rho<162 low-digit certificate
                      -- (hN5 covers 0..4); G_j locality/recurrence (Part G6) are the
                      -- route to eliminating the residual, not bounding it.
                      -- Empirically p(rho,q) <= 15 + floor(log3 q) + 13 (max excess 13
                      -- over ~10^5 q), so only adversarial long-clean-prefix q reach
                      -- this case; a full proof needs tail bound INV-2 (research:
                      -- phase3-bridge.md Front 2, section D).
                      sorry
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
    obtain ⟨i, hi⟩ := criticalGap_has_digit2_of_gt8 r hc h8
    have h_no2 := memCantorNat_imp_criticalGap_no_digit2 hc i
    have hi_ge : i ≥ K_star r := by by_contra h; push_neg at h; exact h_no2 h hi
    have hi_eq : i = K_star r := by
      by_contra h; have : i > K_star r := by omega
      rw [criticalGap_digit_gt_K_star r i this] at hi; norm_num at hi
    rw [hi_eq] at hi; exact criticalGap_digit_K_star_ne_two r hi

end ErdosTernary.CriticalInvariant
