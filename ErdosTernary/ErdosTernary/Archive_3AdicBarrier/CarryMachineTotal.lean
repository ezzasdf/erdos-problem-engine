import Mathlib.Tactic
import ErdosTernary.TwoAdicObstruction
import ErdosTernary.OddEncObstruction

set_option linter.unusedVariables false

namespace CarryMachineTotal
open OddEncObstruction

-- ================================================================
-- Definitions
-- ================================================================

def outerF (S M M1 targetParity p_j vBits : ℕ) : ℕ → ℕ → ℕ :=
  fun acc ci =>
    if S.testBit ci then
      (List.range M1).foldl (fun acc2 vi =>
        if (vBits.testBit vi && (p_j + vi + ci) % 2 == targetParity : Bool) then
          acc2 ||| (1 <<< ((p_j + vi + ci) / 2 % M))
        else acc2) acc
    else acc

def carryStepTotal (M M1 targetParity : ℕ) (S : ℕ) (p_j vBits : ℕ) : ℕ :=
  (List.range M).foldl (outerF S M M1 targetParity p_j vBits) 0

def carryRunTotal (d M M1 : ℕ) (j : ℕ) : ℕ :=
  let tbl := tableData d
  (List.range j).foldl (fun acc pos =>
    let entry := tbl.getD pos (0, 0)
    let targetParity := if pos % 2 == 0 then 1 else 0
    carryStepTotal M M1 targetParity acc entry.1 entry.2) 1

-- ================================================================
-- COMPUTATIONAL VERIFICATION (46 native_decide)
-- ================================================================

theorem carryRunTotal_dead_d25 : carryRunTotal 25 64 128 29 = 0 := by native_decide
theorem carryRunTotal_dead_d26 : carryRunTotal 26 64 128 30 = 0 := by native_decide
theorem carryRunTotal_dead_d27 : carryRunTotal 27 64 128 31 = 0 := by native_decide
theorem carryRunTotal_dead_d28 : carryRunTotal 28 64 128 32 = 0 := by native_decide
theorem carryRunTotal_dead_d29 : carryRunTotal 29 64 128 33 = 0 := by native_decide
theorem carryRunTotal_dead_d30 : carryRunTotal 30 64 128 34 = 0 := by native_decide
theorem carryRunTotal_dead_d31 : carryRunTotal 31 64 128 35 = 0 := by native_decide
theorem carryRunTotal_dead_d32 : carryRunTotal 32 64 128 36 = 0 := by native_decide
theorem carryRunTotal_dead_d33 : carryRunTotal 33 64 128 37 = 0 := by native_decide
theorem carryRunTotal_dead_d34 : carryRunTotal 34 64 128 38 = 0 := by native_decide
theorem carryRunTotal_dead_d35 : carryRunTotal 35 64 128 39 = 0 := by native_decide
theorem carryRunTotal_dead_d36 : carryRunTotal 36 64 128 40 = 0 := by native_decide
theorem carryRunTotal_dead_d37 : carryRunTotal 37 64 128 41 = 0 := by native_decide
theorem carryRunTotal_dead_d38 : carryRunTotal 38 64 128 42 = 0 := by native_decide
theorem carryRunTotal_dead_d39 : carryRunTotal 39 64 128 43 = 0 := by native_decide
theorem carryRunTotal_dead_d40 : carryRunTotal 40 64 128 44 = 0 := by native_decide
theorem carryRunTotal_dead_d41 : carryRunTotal 41 64 128 45 = 0 := by native_decide
theorem carryRunTotal_dead_d42 : carryRunTotal 42 64 128 46 = 0 := by native_decide
theorem carryRunTotal_dead_d43 : carryRunTotal 43 64 128 47 = 0 := by native_decide
theorem carryRunTotal_dead_d44 : carryRunTotal 44 64 128 48 = 0 := by native_decide
theorem carryRunTotal_dead_d45 : carryRunTotal 45 64 128 49 = 0 := by native_decide
theorem carryRunTotal_dead_d46 : carryRunTotal 46 64 128 50 = 0 := by native_decide
theorem carryRunTotal_dead_d47 : carryRunTotal 47 64 128 51 = 0 := by native_decide
theorem carryRunTotal_dead_d48 : carryRunTotal 48 64 128 52 = 0 := by native_decide
theorem carryRunTotal_dead_d49 : carryRunTotal 49 64 128 53 = 0 := by native_decide
theorem carryRunTotal_dead_d50 : carryRunTotal 50 64 128 54 = 0 := by native_decide
theorem carryRunTotal_dead_d51 : carryRunTotal 51 64 128 55 = 0 := by native_decide
theorem carryRunTotal_dead_d52 : carryRunTotal 52 64 128 56 = 0 := by native_decide
theorem carryRunTotal_dead_d53 : carryRunTotal 53 64 128 57 = 0 := by native_decide
theorem carryRunTotal_dead_d54 : carryRunTotal 54 64 128 58 = 0 := by native_decide
theorem carryRunTotal_dead_d55 : carryRunTotal 55 64 128 59 = 0 := by native_decide
theorem carryRunTotal_dead_d56 : carryRunTotal 56 64 128 60 = 0 := by native_decide
theorem carryRunTotal_dead_d57 : carryRunTotal 57 64 128 61 = 0 := by native_decide
theorem carryRunTotal_dead_d58 : carryRunTotal 58 64 128 62 = 0 := by native_decide
theorem carryRunTotal_dead_d59 : carryRunTotal 59 64 128 63 = 0 := by native_decide
theorem carryRunTotal_dead_d60 : carryRunTotal 60 128 256 64 = 0 := by native_decide
theorem carryRunTotal_dead_d61 : carryRunTotal 61 64 128 65 = 0 := by native_decide
theorem carryRunTotal_dead_d62 : carryRunTotal 62 64 128 66 = 0 := by native_decide
theorem carryRunTotal_dead_d63 : carryRunTotal 63 64 128 67 = 0 := by native_decide
theorem carryRunTotal_dead_d64 : carryRunTotal 64 64 128 68 = 0 := by native_decide
theorem carryRunTotal_dead_d65 : carryRunTotal 65 64 128 69 = 0 := by native_decide
theorem carryRunTotal_dead_d66 : carryRunTotal 66 64 128 70 = 0 := by native_decide
theorem carryRunTotal_dead_d67 : carryRunTotal 67 64 128 71 = 0 := by native_decide
theorem carryRunTotal_dead_d68 : carryRunTotal 68 64 128 72 = 0 := by native_decide
theorem carryRunTotal_dead_d69 : carryRunTotal 69 64 128 73 = 0 := by native_decide
theorem carryRunTotal_dead_d70 : carryRunTotal 70 64 128 74 = 0 := by native_decide

theorem carryRunTotal_dead_all (d : ℕ) (hd : 25 ≤ d) (hle : d ≤ 70) :
    carryRunTotal d (if d = 60 then 128 else 64) (if d = 60 then 256 else 128) (d + 4) = 0 := by
  interval_cases d <;> native_decide

-- ================================================================
-- PRIMITIVE LEMMAS
-- ================================================================

private theorem testBit_shiftLeft_one (k i : ℕ) :
    (1 <<< k : ℕ).testBit i = true ↔ k = i := by
  constructor
  · intro h
    rw [Nat.shiftLeft_eq, show (1 : ℕ) * 2 ^ k = 2 ^ k from one_mul _] at h
    rw [Nat.testBit_two_pow] at h; exact decide_eq_true_eq.mp h
  · intro h; subst h
    rw [Nat.shiftLeft_eq, show (1 : ℕ) * 2 ^ k = 2 ^ k from one_mul _]
    rw [Nat.testBit_two_pow]; exact decide_eq_true_eq.mpr rfl

private theorem nat_beq_eq_true {a b : ℕ} (h : (a == b : Bool) = true) : a = b := by
  induction a generalizing b with
  | zero => cases b <;> simp_all [BEq.beq, Nat.beq]
  | succ a ih => cases b <;> simp_all [BEq.beq, Nat.beq]

private theorem eq_nat_beq_true {a b : ℕ} (h : a = b) : (a == b : Bool) = true := by
  subst h; simp [BEq.beq, Nat.beq]

private theorem mod2_beq_iff {x targetParity : ℕ} :
    ((x % 2 == targetParity : Bool) = true) ↔ (x % 2 = targetParity) := by
  constructor
  · intro h; exact nat_beq_eq_true h
  · intro h; exact eq_nat_beq_true h

private theorem lor_shiftLeft_testBit (a k i : ℕ) :
    (a ||| (1 <<< k)).testBit i = true ↔ a.testBit i = true ∨ k = i := by
  have hlor := Nat.testBit_lor a (1 <<< k) i
  constructor
  · intro h; rw [hlor, Bool.or_eq_true] at h
    rcases h with h | h
    · left; exact h
    · right; exact (testBit_shiftLeft_one k i).mp h
  · intro h; rw [hlor, Bool.or_eq_true]
    rcases h with h | h
    · left; exact h
    · right; exact (testBit_shiftLeft_one k i).mpr h

private theorem foldl_range_succ (f : ℕ → ℕ → ℕ) (acc n : ℕ) :
    (List.range (n + 1)).foldl f acc = f ((List.range n).foldl f acc) n := by
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

-- ================================================================
-- LAYER A: INNER FOLD INVARIANT
-- ================================================================

private theorem inner_fold_bit_iff (M1 M targetParity ci p_j vBits c' : ℕ) :
    ∀ acc,
    ((List.range M1).foldl (fun acc2 vi =>
      if (vBits.testBit vi && (p_j + vi + ci) % 2 == targetParity : Bool) then
        acc2 ||| (1 <<< ((p_j + vi + ci) / 2 % M))
      else acc2) acc).testBit c' = true ↔
    acc.testBit c' = true ∨
    (∃ vi, vi < M1 ∧ vBits.testBit vi = true ∧
      (p_j + vi + ci) % 2 = targetParity ∧ c' = (p_j + vi + ci) / 2 % M) := by
  intro acc
  induction M1 generalizing acc with
  | zero => simp [List.range, List.foldl]
  | succ M1 ih =>
    rw [foldl_range_succ]
    by_cases hcond :
      (vBits.testBit M1 && (p_j + M1 + ci) % 2 == targetParity : Bool) = true
    · rw [if_pos hcond]
      rw [Bool.and_eq_true, mod2_beq_iff] at hcond
      rcases hcond with ⟨hv, hp⟩
      constructor
      · intro h
        rw [lor_shiftLeft_testBit] at h
        rcases h with h | h
        · rcases (ih acc).mp h with h | ⟨vi, hvi, hvb, hpc, hcc⟩
          · left; exact h
          · right; exact ⟨vi, by omega, hvb, hpc, hcc⟩
        · right; exact ⟨M1, by omega, hv, hp, Eq.symm h⟩
      · intro h
        rcases h with h | ⟨vi, hvi, hvb, hpc, hcc⟩
        · rw [lor_shiftLeft_testBit]; left; exact (ih acc).mpr (Or.inl h)
        · by_cases hvi_eq : vi = M1
          · subst hvi_eq; rw [lor_shiftLeft_testBit]; right; exact Eq.symm hcc
          · rw [lor_shiftLeft_testBit]; left
            have hvi_lt : vi < M1 := by omega
            exact (ih acc).mpr (Or.inr ⟨vi, hvi_lt, hvb, hpc, hcc⟩)
    · rw [if_neg hcond]
      constructor
      · intro h
        rcases (ih acc).mp h with h | ⟨vi, hvi, hvb, hpc, hcc⟩
        · left; exact h
        · right; exact ⟨vi, by omega, hvb, hpc, hcc⟩
      · intro h
        rcases h with h | ⟨vi, hvi, hvb, hpc, hcc⟩
        · exact (ih acc).mpr (Or.inl h)
        · by_cases hvi_eq : vi = M1
          · rw [hvi_eq] at hvb hpc
            have htrue :
              (vBits.testBit M1 && (p_j + M1 + ci) % 2 == targetParity : Bool) = true := by
              rw [Bool.and_eq_true, mod2_beq_iff]; exact ⟨hvb, hpc⟩
            exact absurd htrue hcond
          · exact (ih acc).mpr (Or.inr ⟨vi, by omega, hvb, hpc, hcc⟩)

-- ================================================================
-- LAYER A: OUTER FOLD INVARIANT
-- ================================================================

private theorem outer_fold_bit_iff (S M M1 targetParity p_j vBits c' : ℕ) (n : ℕ) :
    ∀ acc,
    ((List.range n).foldl (outerF S M M1 targetParity p_j vBits) acc).testBit c' = true ↔
    acc.testBit c' = true ∨
    (∃ ci, ci < n ∧ S.testBit ci = true ∧
      ∃ vi, vi < M1 ∧ vBits.testBit vi = true ∧
        (p_j + vi + ci) % 2 = targetParity ∧
        c' = (p_j + vi + ci) / 2 % M) := by
  intro acc
  induction n generalizing acc with
  | zero => simp [List.range, List.foldl]
  | succ n ih =>
    rw [foldl_range_succ]
    unfold outerF
    by_cases hs : S.testBit n = true
    · rw [if_pos hs]
      constructor
      · intro h
        have hinner := @inner_fold_bit_iff M1 M targetParity n p_j vBits c'
          ((List.range n).foldl (outerF S M M1 targetParity p_j vBits) acc)
        rcases hinner.mp h with h | ⟨vi, hvi, hvb, hpc, hcc⟩
        · rcases (ih acc).mp h with h | ⟨ci, hci, hsci, vi', hvi', hvb', hpc', hcc'⟩
          · left; exact h
          · right; exact ⟨ci, by omega, hsci, vi', by omega, hvb', hpc', hcc'⟩
        · right; exact ⟨n, by omega, hs, vi, hvi, hvb, hpc, hcc⟩
      · intro h
        rcases h with h | ⟨ci, hci, hsci, vi, hvi, hvb, hpc, hcc⟩
        · have hinner := @inner_fold_bit_iff M1 M targetParity n p_j vBits c'
            ((List.range n).foldl (outerF S M M1 targetParity p_j vBits) acc)
          exact hinner.mpr (Or.inl ((ih acc).mpr (Or.inl h)))
        · by_cases hci_eq : ci = n
          · have hvpc : (p_j + vi + n) % 2 = targetParity := by rw [← hci_eq]; exact hpc
            have hvcc : c' = (p_j + vi + n) / 2 % M := by rw [← hci_eq]; exact hcc
            have hinner := @inner_fold_bit_iff M1 M targetParity n p_j vBits c'
              ((List.range n).foldl (outerF S M M1 targetParity p_j vBits) acc)
            exact hinner.mpr (Or.inr ⟨vi, by omega, hvb, hvpc, hvcc⟩)
          · have hci_lt : ci < n := by omega
            have hinner := @inner_fold_bit_iff M1 M targetParity n p_j vBits c'
              ((List.range n).foldl (outerF S M M1 targetParity p_j vBits) acc)
            exact hinner.mpr (Or.inl ((ih acc).mpr (Or.inr ⟨ci, hci_lt, hsci, vi, hvi, hvb, hpc, hcc⟩)))
    · rw [if_neg hs]
      constructor
      · intro h
        rcases (ih acc).mp h with h | ⟨ci, hci, hsci, vi, hvi, hvb, hpc, hcc⟩
        · left; exact h
        · right; exact ⟨ci, by omega, hsci, vi, hvi, hvb, hpc, hcc⟩
      · intro h
        rcases h with h | ⟨ci, hci, hsci, vi, hvi, hvb, hpc, hcc⟩
        · exact (ih acc).mpr (Or.inl h)
        · by_cases hci_eq : ci = n
          · rw [hci_eq] at hsci; exact absurd hsci hs
          · have hci_lt : ci < n := by omega
            exact (ih acc).mpr (Or.inr ⟨ci, hci_lt, hsci, vi, hvi, hvb, hpc, hcc⟩)

-- ================================================================
-- LAYER A: carryStepTotal_bit_iff (no sorry!)
-- ================================================================

theorem carryStepTotal_bit_iff (M M1 targetParity : ℕ) (S : ℕ) (p_j vBits c' : ℕ) :
    (carryStepTotal M M1 targetParity S p_j vBits).testBit c' = true ↔
    ∃ ci, ci < M ∧ S.testBit ci = true ∧
      ∃ vi, vi < M1 ∧ vBits.testBit vi = true ∧
        (p_j + vi + ci) % 2 = targetParity ∧
        c' = (p_j + vi + ci) / 2 % M := by
  unfold carryStepTotal
  have h := @outer_fold_bit_iff S M M1 targetParity p_j vBits c' M 0
  have h0 : (0 : ℕ).testBit c' = false := by
    induction c' with
    | zero => simp [Nat.testBit]
    | succ c' ih => simp [Nat.testBit, ih]
  simp only [h0] at h
  constructor
  · intro hc; rcases h.mp hc with h | h
    · contradiction
    · exact h
  · intro hc; exact h.mpr (Or.inr hc)

-- ================================================================
-- LAYER B: Soundness (sorry)
-- ================================================================

theorem carryRunTotal_sound (d M M1 : ℕ) (hd25 : 25 ≤ d) (hd70 : d ≤ 70)
    (hM : if d = 60 then M = 128 else M = 64)
    (hM1 : M1 = 2 * M) :
    carryRunTotal d M M1 (d + 4) = 0 →
    ∀ m, 2 ^ (d + 4) ∣ 3 * (3 ^ (d - 1) + TwoAdicObstruction.evalBit (d - 1) m) + 1 → False := by
  sorry

-- ================================================================
-- Bridge theorem
-- ================================================================

theorem odd_enc_bridge_total (d : ℕ) (hd : 25 ≤ d) (hle : d ≤ 70) (m : ℕ) :
    2 ^ (d + 4) ∣ 3 * (3 ^ (d - 1) + TwoAdicObstruction.evalBit (d - 1) m) + 1 → False := by
  intro hdiv
  by_cases hd60 : d = 60
  · subst hd60
    exact carryRunTotal_sound 60 128 256 (by omega) (by omega)
      (by simp) (by simp) (carryRunTotal_dead_d60) m hdiv
  · have hne : d ≠ 60 := hd60
    exact carryRunTotal_sound d 64 128 hd hle
      (by simp [hne]) (by simp [hne])
      (by have := carryRunTotal_dead_all d hd hle; simp [hne] at this; exact this) m hdiv

end CarryMachineTotal
