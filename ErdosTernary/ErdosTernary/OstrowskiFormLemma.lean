/-
  Lemma A: Form characterization of mass-one integers in Ostrowski numeration.

  For convergent denominators `q` of partial quotients `A >= 1` with anchor
  `q5 = 19`:

    * every integer of the form `q_j + l` (`5 <= j`, `l <= 18`) carries greedy
      coefficient exactly 1 at position `j` and zero coefficients at every
      other position `k >= 5`;
    * conversely, if position `j >= 5` carries coefficient 1 and no other
      position `>= 5` is nonzero, then `n = q_j + l` with `l <= 18`;
    * the form is unique.

  Abstract in `A`: only `A(k) >= 1` for `k >= 2`, `q5 = 19` and
  `q5 + 18 < q6` are used.  For alpha = log_3(2): q5 = 19, q6 = 65.
-/

import Mathlib.Tactic
import ErdosTernary.Ostrowski

namespace ErdosTernary.OstrowskiFormLemma

/-! ### Convergent denominators -/

/-- Convergent denominators for partial quotients `A`:
    `q0 = q1 = 1`, `q_{k+2} = A(k+2) * q_{k+1} + q_k`. -/
def Q (A : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | k + 2 => A (k + 2) * Q A (k + 1) + Q A k

theorem Q_zero {A : ℕ → ℕ} : Q A 0 = 1 := rfl

theorem Q_one {A : ℕ → ℕ} : Q A 1 = 1 := rfl

theorem Q_succ_succ {A : ℕ → ℕ} (k : ℕ) :
    Q A (k + 2) = A (k + 2) * Q A (k + 1) + Q A k := rfl

theorem Q_pair_pos {A : ℕ → ℕ} : ∀ k, 0 < Q A k ∧ 0 < Q A (k + 1) := by
  intro k
  induction k with
  | zero => exact ⟨Nat.zero_lt_one, Nat.zero_lt_one⟩
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    rw [Q_succ_succ]
    omega

theorem Q_pos {A : ℕ → ℕ} (k : ℕ) : 0 < Q A k := (Q_pair_pos k).1

theorem Q_step_add {A : ℕ → ℕ} (hA : ∀ k, 2 ≤ k → 1 ≤ A k) (k : ℕ) :
    Q A k + Q A (k + 1) ≤ Q A (k + 2) := by
  have ha := hA (k + 2) (by omega)
  have _h1 := Q_pos (A := A) (k + 1)
  rw [Q_succ_succ]
  linarith [Nat.mul_le_mul_left (Q A (k + 1)) ha]

theorem Q_succ_gt {A : ℕ → ℕ} (hA : ∀ k, 2 ≤ k → 1 ≤ A k) :
    ∀ k, 1 ≤ k → Q A k < Q A (k + 1) := by
  intro k hk
  match k, hk with
  | 0, _ => omega
  | 1, _ =>
    have ha := hA 2 (by omega)
    have h2 : Q A 2 = A 2 + 1 := by
      unfold Q
      simp [Q_one, Q_zero]
    have h1 : Q A 1 = 1 := Q_one
    rw [h1, h2]
    omega
  | m + 2, h =>
    have hs := Q_step_add hA (m + 1)
    have hp : 0 < Q A (m + 1) := Q_pos (m + 1)
    linarith

theorem Q_mono {A : ℕ → ℕ} (hA : ∀ k, 2 ≤ k → 1 ≤ A k) {a b : ℕ}
    (ha : 1 ≤ a) (hab : a ≤ b) : Q A a ≤ Q A b := by
  induction b with
  | zero => omega
  | succ b ih =>
    rcases Nat.eq_or_lt_of_le hab with hle | hlt
    · subst hle; omega
    · have h2 : a ≤ b := by omega
      have hgt := Q_succ_gt hA b (by omega : 1 ≤ b)
      have hle := ih h2
      omega

theorem Q_ge_index {A : ℕ → ℕ} (hA : ∀ k, 2 ≤ k → 1 ≤ A k) :
    ∀ k, 1 ≤ k → k ≤ Q A k := by
  intro k hk
  induction k with
  | zero => omega
  | succ n ih =>
    rcases n with _ | m
    · change 1 ≤ Q A 1
      rw [Q_one]
    · have hs := Q_step_add hA m
      have hp := Q_pos (A := A) m
      have hi := ih (by omega)
      have heq : (m + 1) + 1 = m + 2 := rfl
      rw [heq]
      omega

/-- Consecutive denominators beyond position 5 are more than 18 apart. -/
theorem key_gap {A : ℕ → ℕ} (hA : ∀ k, 2 ≤ k → 1 ≤ A k) (hQ5 : 18 < Q A 5)
    (hQ6 : Q A 5 + 18 < Q A 6) :
    ∀ j, 5 ≤ j → Q A j + 18 < Q A (j + 1) := by
  intro j hj
  rcases Nat.eq_or_lt_of_le hj with h | h
  · subst h
    exact hQ6
  · have h5le : 5 ≤ j - 1 := by omega
    have hmono := Q_mono hA (by omega : 1 ≤ 5) h5le
    have hgap : 18 < Q A (j - 1) := by linarith
    have hstep : Q A (j - 1) + Q A j ≤ Q A (j + 1) := by
      have h21 : j - 1 + 1 = j := by omega
      have h22 : j - 1 + 2 = j + 1 := by omega
      have aux := Q_step_add hA (j - 1)
      simp only [h21, h22] at aux
      exact aux
    have h₁ : Q A j + 18 < Q A (j - 1) + Q A j := by linarith
    linarith

/-! ### Top greedy index -/

theorem exists_above {A : ℕ → ℕ} (hA : ∀ k, 2 ≤ k → 1 ≤ A k) (n : ℕ) :
    ∃ t, n < Q A (t + 1) :=
  ⟨n, by
    have h := Q_ge_index hA (n + 1) (by omega)
    omega⟩

/-- Largest index `t` with `q_t ≤ n` (least `t` with `n < q_{t+1}`). -/
def topIdx (A : ℕ → ℕ) (hA : ∀ k, 2 ≤ k → 1 ≤ A k) (n : ℕ) : ℕ :=
  Nat.find (exists_above hA n)

theorem topIdx_hi {A : ℕ → ℕ} (hA : ∀ k, 2 ≤ k → 1 ≤ A k) (n : ℕ) :
    n < Q A (topIdx A hA n + 1) :=
  Nat.find_spec (exists_above hA n)

theorem topIdx_le_of_lt {A : ℕ → ℕ} (hA : ∀ k, 2 ≤ k → 1 ≤ A k) {r s : ℕ}
    (h : r < Q A (s + 1)) : topIdx A hA r ≤ s :=
  Nat.find_min' (exists_above hA r) h

theorem topIdx_lo {A : ℕ → ℕ} (hA : ∀ k, 2 ≤ k → 1 ≤ A k) {n : ℕ}
    (hn : 0 < n) : Q A (topIdx A hA n) ≤ n := by
  by_contra hcon
  push_neg at hcon
  have ht1 : 1 ≤ topIdx A hA n := by
    by_contra hc
    push_neg at hc
    have hz : topIdx A hA n = 0 := by omega
    have hs := topIdx_hi hA n
    rw [hz, Nat.zero_add, Q_one] at hs
    omega
  have heq : topIdx A hA n - 1 + 1 = topIdx A hA n := by omega
  have hlt : n < Q A (topIdx A hA n - 1 + 1) := by rw [heq]; exact hcon
  have hle := topIdx_le_of_lt hA hlt
  omega

/-! ### Greedy coefficients -/

/-- Greedy Ostrowski coefficient at position `k` of `n`. -/
def gd (A : ℕ → ℕ) (hA : ∀ k, 2 ≤ k → 1 ≤ A k) (k n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | m + 1 =>
      if k = topIdx A hA (m + 1) then (m + 1) / Q A (topIdx A hA (m + 1))
      else gd A hA k ((m + 1) % Q A (topIdx A hA (m + 1)))
termination_by n
decreasing_by
  rename_i m
  exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (Q_pos (A := A) _)) (topIdx_lo hA (by omega))

theorem gd_zero {A : ℕ → ℕ} (hA : ∀ k, 2 ≤ k → 1 ≤ A k) (k : ℕ) :
    gd A hA k 0 = 0 := by simp [gd]

/-- Shape-generic top branch. -/
theorem gd_eq_top_of {A : ℕ → ℕ} (hA : ∀ k, 2 ≤ k → 1 ≤ A k) {n k : ℕ}
    (hn : 0 < n) (hkt : k = topIdx A hA n) :
    gd A hA k n = n / Q A k := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  subst hkt
  unfold gd
  rw [if_pos rfl]

/-- Shape-generic shifted branch. -/
theorem gd_eq_shift_of {A : ℕ → ℕ} (hA : ∀ k, 2 ≤ k → 1 ≤ A k) {n k : ℕ}
    (hn : 0 < n) (hkt : k ≠ topIdx A hA n) :
    gd A hA k n = gd A hA k (n % Q A (topIdx A hA n)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [gd]
  rw [if_neg hkt]

/-- P1: a nonzero coefficient forces `q_k ≤ n`. -/
theorem gd_nonzero_imp_le {A : ℕ → ℕ} (hA : ∀ k, 2 ≤ k → 1 ≤ A k) :
    ∀ n k, 0 < gd A hA k n → Q A k ≤ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro k hpos
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp [gd_zero] at hpos
    · by_cases hkt : k = topIdx A hA n
      · rw [hkt]
        exact topIdx_lo hA hn
      · rw [gd_eq_shift_of hA hn hkt] at hpos
        have hrem := Nat.mod_lt n (Q_pos (A := A) (topIdx A hA n))
        have hrem_lt_n : n % Q A (topIdx A hA n) < n :=
          lt_of_lt_of_le hrem (topIdx_lo hA hn)
        exact le_trans (ih _ hrem_lt_n k hpos) (Nat.mod_le n (Q A (topIdx A hA n)))

/-- P-top: a nonzero coefficient forces `k ≤ topIdx n`. -/
theorem gd_nonzero_imp_le_top {A : ℕ → ℕ} (hA : ∀ k, 2 ≤ k → 1 ≤ A k) :
    ∀ n k, 0 < gd A hA k n → k ≤ topIdx A hA n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro k hpos
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp [gd_zero] at hpos
    · by_cases hkt : k = topIdx A hA n
      · rw [hkt]
      · rw [gd_eq_shift_of hA hn hkt] at hpos
        have hrem := Nat.mod_lt n (Q_pos (A := A) (topIdx A hA n))
        have hrem_lt_n : n % Q A (topIdx A hA n) < n :=
          lt_of_lt_of_le hrem (topIdx_lo hA hn)
        have htop1 : 1 ≤ topIdx A hA n := by
          have h := topIdx_hi hA n
          by_contra h0
          have h0' : topIdx A hA n = 0 := Nat.eq_zero_of_not_pos h0
          rw [h0'] at h
          simp [Q] at h
          omega
        have heq : topIdx A hA n - 1 + 1 = topIdx A hA n := Nat.sub_add_cancel htop1
        rcases Nat.eq_zero_or_pos (n % Q A (topIdx A hA n)) with hz | hpz
        · rw [hz] at hpos
          simp [gd_zero] at hpos
        · have hle := ih _ hrem_lt_n k hpos
          have hsmall := topIdx_le_of_lt hA
            (by rw [heq]; exact hrem)
          omega

/-- Zero below: if `q_k > n` the coefficient vanishes. -/
theorem gd_zero_of_lt {A : ℕ → ℕ} (hA : ∀ k, 2 ≤ k → 1 ≤ A k) {n k : ℕ}
    (h : n < Q A k) : gd A hA k n = 0 := by
  by_contra hcon
  push_neg at hcon
  have := gd_nonzero_imp_le hA n k (by omega)
  omega

/-! ### Lemma A -/

theorem topIdx_eq_of_form {A : ℕ → ℕ} (hA : ∀ k, 2 ≤ k → 1 ≤ A k)
    (hQ5 : Q A 5 = 19) (hQ6 : Q A 5 + 18 < Q A 6) (j ℓ : ℕ) (hj : 5 ≤ j) (hℓ : ℓ ≤ 18) :
    topIdx A hA (Q A j + ℓ) = j := by
  have hn0 : 0 < Q A j + ℓ := by have h := Q_pos (A := A) j; omega
  have hlow : j ≤ topIdx A hA (Q A j + ℓ) := by
    by_contra hcon
    push_neg at hcon
    have hs := topIdx_hi hA (Q A j + ℓ)
    have hmono := Q_mono hA (by omega) (by omega : topIdx A hA (Q A j + ℓ) + 1 ≤ j)
    have hQj : Q A j ≤ Q A j + ℓ := Nat.le_add_right _ _
    omega
  have hupp : topIdx A hA (Q A j + ℓ) ≤ j := by
    by_contra hcon
    push_neg at hcon
    have hQt := topIdx_lo hA hn0
    have h18 : 18 < Q A 5 := by omega
    have hgap := key_gap hA h18 hQ6 j hj
    have hmono := Q_mono hA (by omega) (by omega : j + 1 ≤ topIdx A hA (Q A j + ℓ))
    omega
  omega

/-- **Lemma A, direction (to)**: integers of the form `q_j + ℓ` (`5 ≤ j`,
`ℓ ≤ 18`) carry exactly one nonzero coefficient above position 5, namely
`b_j = 1`. -/
theorem coef_unique_of_form {A : ℕ → ℕ} (hA : ∀ k, 2 ≤ k → 1 ≤ A k)
    (hQ5 : Q A 5 = 19) (hQ6 : Q A 5 + 18 < Q A 6) (j ℓ : ℕ) (hj : 5 ≤ j) (hℓ : ℓ ≤ 18) :
    gd A hA j (Q A j + ℓ) = 1 ∧ ∀ k, 5 ≤ k → k ≠ j → gd A hA k (Q A j + ℓ) = 0 := by
  have ht := topIdx_eq_of_form hA hQ5 hQ6 j ℓ hj hℓ
  have hn0 : 0 < Q A j + ℓ := by have h := Q_pos (A := A) j; omega
  have h19j : 19 ≤ Q A j := by
    rw [← hQ5]
    exact Q_mono hA (by omega) hj
  have hQjl : ℓ < Q A j := lt_of_le_of_lt hℓ (by omega)
  have hdiv : (Q A j + ℓ) / Q A j = 1 := by
    have hpos : 0 < Q A j := by omega
    apply le_antisymm
    · rw [Nat.div_le_iff_le_mul_add_pred hpos]
      omega
    · rw [Nat.one_le_div_iff hpos]
      omega
  constructor
  · rw [gd_eq_top_of hA hn0 ht.symm, hdiv]
  · intro k hk5 hknj
    have hmv : (Q A j + ℓ) % Q A j = ℓ := by
      have h1 : Q A j + ℓ = ℓ + Q A j * 1 := by ring
      rw [h1, Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt hQjl
    have hneq : k ≠ topIdx A hA (Q A j + ℓ) := by rw [ht]; exact hknj
    have hlk : ℓ < Q A k := by
      have hq5le := Q_mono hA (by omega : 1 ≤ 5) hk5
      omega
    have h1 : gd A hA k (Q A j + ℓ) = gd A hA k ((Q A j + ℓ) % Q A (topIdx A hA (Q A j + ℓ))) :=
      gd_eq_shift_of hA hn0 hneq
    have h2 : (Q A j + ℓ) % Q A (topIdx A hA (Q A j + ℓ)) = ℓ := by rw [ht, hmv]
    have h3 : gd A hA k ℓ = 0 := gd_zero_of_lt hA hlk
    rw [h2] at h1
    rw [h1, h3]

/-- **Lemma A, direction (from)**: an integer whose only nonzero coefficients
at positions ≥ 5 consist of a single `b_j = 1` equals `q_j + ℓ`, `ℓ ≤ 18`. -/
theorem form_of_coef_single {A : ℕ → ℕ} (hA : ∀ k, 2 ≤ k → 1 ≤ A k)
    (hQ5 : Q A 5 = 19) (n j : ℕ) (hj : 5 ≤ j)
    (h1 : gd A hA j n = 1) (ho : ∀ k, 5 ≤ k → k ≠ j → gd A hA k n = 0) :
    ∃ ℓ, ℓ ≤ 18 ∧ n = Q A j + ℓ := by
  have hn1 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      simp only [gd_zero] at h1
      exact absurd h1 (by norm_num)
    · exact hpos
  have hjle : j ≤ topIdx A hA n :=
    gd_nonzero_imp_le_top hA n j (by rw [h1]; exact Nat.zero_lt_one)
  have heq : topIdx A hA n = j := by
    rcases Nat.eq_or_lt_of_le hjle with h | h
    · exact h.symm
    · exfalso
      have hne : topIdx A hA n ≠ j := by omega
      have hzero := ho (topIdx A hA n) (by omega) hne
      have hpos : 0 < gd A hA (topIdx A hA n) n := by
        rw [gd_eq_top_of hA hn1 rfl]
        have := (Nat.one_le_div_iff (Q_pos (A := A) (topIdx A hA n))).mpr (topIdx_lo hA hn1)
        omega
      omega
  have hcoef : n / Q A j = 1 := by
    have h2 := gd_eq_top_of hA hn1 heq.symm
    rw [← h2]
    exact h1
  have hsplit : n = Q A j * (n / Q A j) + n % Q A j :=
    (Nat.div_add_mod n (Q A j)).symm
  have hmlt : n % Q A (topIdx A hA n) < Q A (topIdx A hA n) :=
    Nat.mod_lt _ (Q_pos (A := A) _)
  have hall : ∀ k, 5 ≤ k → gd A hA k (n % Q A (topIdx A hA n)) = 0 := by
    intro k hk5
    by_cases hke : k = j
    · subst hke
      rw [heq] at hmlt
      rw [heq]
      exact gd_zero_of_lt hA hmlt
    · rw [← gd_eq_shift_of hA hn1 (show k ≠ topIdx A hA n from by rw [heq]; exact hke)]
      exact ho k hk5 hke
  have hmod18 : n % Q A (topIdx A hA n) ≤ 18 := by
    by_contra hbig
    push_neg at hbig
    have hm5 : Q A 5 ≤ n % Q A (topIdx A hA n) := by omega
    have htop5 : 5 ≤ topIdx A hA (n % Q A (topIdx A hA n)) := by
      by_contra hc
      push_neg at hc
      have hs := topIdx_hi hA (n % Q A (topIdx A hA n))
      have hmono := Q_mono hA (by omega) (by omega : topIdx A hA (n % Q A (topIdx A hA n)) + 1 ≤ 5)
      omega
    have hnz : 0 < gd A hA (topIdx A hA (n % Q A (topIdx A hA n)))
        (n % Q A (topIdx A hA n)) := by
      rw [gd_eq_top_of hA (by omega) rfl]
      have := (Nat.one_le_div_iff (Q_pos (A := A) (topIdx A hA (n % Q A (topIdx A hA n))))).mpr
        (topIdx_lo hA (by omega))
      omega
    exact absurd hnz (by rw [hall (topIdx A hA (n % Q A (topIdx A hA n))) htop5]; omega)
  refine ⟨n % Q A (topIdx A hA n), hmod18, ?_⟩
  have hfin := hsplit
  rw [hcoef, Nat.mul_one] at hfin
  rw [heq]
  exact hfin

/-- Uniqueness of the mass-one form. -/
theorem form_unique {A : ℕ → ℕ} (hA : ∀ k, 2 ≤ k → 1 ≤ A k)
    (hQ5 : Q A 5 = 19) (hQ6 : Q A 5 + 18 < Q A 6)
    {j j' ℓ ℓ' : ℕ} (hj : 5 ≤ j) (hj' : 5 ≤ j') (hℓ : ℓ ≤ 18) (hℓ' : ℓ' ≤ 18)
    (h : Q A j + ℓ = Q A j' + ℓ') : j = j' ∧ ℓ = ℓ' := by
  have h18 : 18 < Q A 5 := by omega
  rcases Nat.lt_trichotomy j j' with hlt | heq | hgt
  · exfalso
    have hgap := key_gap hA h18 hQ6 j hj
    have hmono := Q_mono hA (by omega) (by omega : j + 1 ≤ j')
    have hlt2 : Q A j + ℓ < Q A j' + ℓ' := calc
      Q A j + ℓ ≤ Q A j + 18 := by omega
      _ < Q A (j + 1) := hgap
      _ ≤ Q A j' := hmono
      _ ≤ Q A j' + ℓ' := Nat.le_add_right _ _
    omega
  · subst heq
    have hEq : ℓ = ℓ' := by omega
    exact ⟨rfl, hEq⟩
  · exfalso
    have hgap := key_gap hA h18 hQ6 j' hj'
    have hmono := Q_mono hA (by omega) (by omega : j' + 1 ≤ j)
    have hlt2 : Q A j' + ℓ' < Q A j + ℓ := calc
      Q A j' + ℓ' ≤ Q A j' + 18 := by omega
      _ < Q A (j' + 1) := hgap
      _ ≤ Q A j := hmono
      _ ≤ Q A j + ℓ := Nat.le_add_right _ _
    omega

/-- Combined restatement: mass-one exactly characterizes the `q_j + ℓ` forms. -/
theorem mass_one_iff {A : ℕ → ℕ} (hA : ∀ k, 2 ≤ k → 1 ≤ A k)
    (hQ5 : Q A 5 = 19) (hQ6 : Q A 5 + 18 < Q A 6) (n : ℕ) :
      (∃ j, 5 ≤ j ∧ gd A hA j n = 1 ∧ ∀ k, 5 ≤ k → k ≠ j → gd A hA k n = 0) ↔
    ∃ j ℓ, 5 ≤ j ∧ ℓ ≤ 18 ∧ n = Q A j + ℓ := by
  constructor
  · rintro ⟨j, hj, h1, ho⟩
    obtain ⟨ℓ, hℓ, rfl⟩ := form_of_coef_single hA hQ5 n j hj h1 ho
    exact ⟨j, ℓ, hj, hℓ, rfl⟩
  · rintro ⟨j, ℓ, hj, hℓ, rfl⟩
    have h := coef_unique_of_form hA hQ5 hQ6 j ℓ hj hℓ
    exact ⟨j, hj, h.1, h.2⟩

section Log32

open ErdosTernary.Ostrowski

/-- Concrete partial quotients of log₃(2), floored at 1 outside the stored
CF window.  The floor is irrelevant: Lemma A only needs coefficients ≥ 1,
and every stored entry at index ≥ 2 already satisfies it. -/
def Al32 : ℕ → ℕ := fun k => max 1 (log32_cf.getD k 0)

theorem Al32_hyp : ∀ k, 2 ≤ k → 1 ≤ Al32 k := fun k _ => Nat.le_max_left _ _

theorem Ql32_5 : Q Al32 5 = 19 := by native_decide

theorem Ql32_6 : Q Al32 6 = 65 := by native_decide

theorem Ql32_hyp6 : Q Al32 5 + 18 < Q Al32 6 := by native_decide

end Log32

end ErdosTernary.OstrowskiFormLemma
