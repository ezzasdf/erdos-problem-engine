import Mathlib.Tactic
import ErdosTernary.TernaryExp

namespace ErdosTernary.MiddleDigits

open ErdosTernary

def doubleDigit (d : Nat) (c : Nat) : Nat × Nat :=
  ((2 * d + c) % 3, (2 * d + c) / 3)

def doubleCarry (c : Nat) : List Nat → List Nat × Nat
  | [] => ([], c)
  | d :: ds =>
      let (o, c') := doubleDigit d c
      let (out, cf) := doubleCarry c' ds
      (o :: out, cf)

lemma doubleCarry_eval (c : Nat) (ds : List Nat) :
    2 * evalTernary ds + c
      = evalTernary (doubleCarry c ds).1 + (doubleCarry c ds).2 * 3 ^ ds.length := by
  revert c
  induction ds with
  | nil => intro c; simp [doubleCarry, evalTernary]
  | cons d ds ih =>
      intro c
      let p := doubleCarry ((2 * d + c) / 3) ds
      have hp0 : p = doubleCarry ((2 * d + c) / 3) ds := rfl
      rcases p with ⟨out, cf⟩
      have hp : doubleCarry ((2 * d + c) / 3) ds = (out, cf) := hp0.symm
      have hih : 2 * evalTernary ds + (2 * d + c) / 3
          = evalTernary out + cf * 3 ^ ds.length := by
        simpa [hp] using (ih ((2 * d + c) / 3))
      have hdiv : 2 * d + c = (2 * d + c) % 3 + 3 * ((2 * d + c) / 3) := by
        omega
      simp only [doubleCarry, doubleDigit, evalTernary, List.length_cons, hp]
      rw [pow_succ]
      nlinarith [hdiv, hih]

lemma evalTernary_append_singleton (ds : List Nat) (c : Nat) :
    evalTernary (ds ++ [c]) = evalTernary ds + c * 3 ^ ds.length := by
  induction ds with
  | nil => simp [evalTernary]
  | cons d ds ih =>
      simp only [evalTernary, List.append_cons, List.length_cons]
      change d + 3 * evalTernary (ds ++ [c]) = d + 3 * evalTernary ds + c * 3 ^ (ds.length + 1)
      rw [ih, pow_succ]
      ring

def doubleTernary (ds : List Nat) : List Nat :=
  let out := (doubleCarry 0 ds).1
  let cf := (doubleCarry 0 ds).2
  if cf = 0 then out else out ++ [cf]

lemma doubleCarry_length (c : Nat) (ds : List Nat) :
    (doubleCarry c ds).1.length = ds.length := by
  revert c
  induction ds with
  | nil => simp [doubleCarry]
  | cons d ds ih =>
      intro c
      simp [doubleCarry, ih]

theorem doubleTernary_correct (ds : List Nat) :
    2 * evalTernary ds = evalTernary (doubleTernary ds) := by
  have h : 2 * evalTernary ds + 0
      = evalTernary (doubleCarry 0 ds).1 + (doubleCarry 0 ds).2 * 3 ^ ds.length :=
    doubleCarry_eval 0 ds
  dsimp [doubleTernary]
  by_cases hz : (doubleCarry 0 ds).2 = 0
  · rw [if_pos hz]
    simpa [hz] using h
  · rw [if_neg hz]
    rw [evalTernary_append_singleton, doubleCarry_length]
    nlinarith

def iterNat {α : Type} (f : α → α) : Nat → α → α
  | 0, a => a
  | n + 1, a => iterNat f n (f a)

def Pow2TernaryDigits (n : Nat) : List Nat := iterNat doubleTernary n [1]

lemma iterNat_double_eval (n : Nat) (ds : List Nat) :
    evalTernary (iterNat doubleTernary n ds) = 2 ^ n * evalTernary ds := by
  revert ds
  induction n with
  | zero => simp [iterNat]
  | succ n ih =>
      intro ds
      simp [iterNat]
      rw [ih, ← doubleTernary_correct]
      rw [pow_succ]
      ring

theorem Pow2TernaryDigits_correct (n : Nat) :
    evalTernary (Pow2TernaryDigits n) = 2 ^ n := by
  rw [Pow2TernaryDigits, iterNat_double_eval]
  simp [evalTernary]

theorem carry_le_one {d c : Nat} (hd : d < 3) (hc : c ≤ 1) :
    (2 * d + c) / 3 ≤ 1 := by
  omega

theorem out_lt_three (d c : Nat) : (2 * d + c) % 3 < 3 := by
  omega

lemma doubleCarry_digits_valid (c : Nat) (hc : c ≤ 1) (ds : List Nat)
    (hds : ∀ d ∈ ds, d < 3) :
    (∀ o ∈ (doubleCarry c ds).1, o < 3) ∧ (doubleCarry c ds).2 ≤ 1 := by
  revert c hc hds
  induction ds with
  | nil => intro c hc _hds; simp [doubleCarry, hc]
  | cons d ds ih =>
      intro c hc hds
      have hd : d < 3 := hds d (by simp)
      have hc' : (2 * d + c) / 3 ≤ 1 := carry_le_one hd hc
      have hrest : (∀ o ∈ (doubleCarry ((2 * d + c) / 3) ds).1, o < 3)
                     ∧ (doubleCarry ((2 * d + c) / 3) ds).2 ≤ 1 :=
        ih ((2 * d + c) / 3) hc' (by intro d' hd'; exact hds d' (by simp [hd']))
      simp only [doubleCarry, doubleDigit]
      constructor
      · intro o ho
        cases ho with
        | head => exact out_lt_three d c
        | tail _ ho' => exact hrest.1 o ho'
      · exact hrest.2

theorem doubleTernary_digits_valid (ds : List Nat) (hds : ∀ d ∈ ds, d < 3) :
    ∀ o ∈ doubleTernary ds, o < 3 := by
  have h : (∀ o ∈ (doubleCarry 0 ds).1, o < 3) ∧ (doubleCarry 0 ds).2 ≤ 1 :=
    doubleCarry_digits_valid 0 (by omega) ds hds
  rw [doubleTernary]
  by_cases hz : (doubleCarry 0 ds).2 = 0
  · rw [if_pos hz]
    intro o ho
    exact h.1 o ho
  · rw [if_neg hz]
    intro o ho
    rcases (List.mem_append.mp ho) with ho1 | ho2
    · exact h.1 o ho1
    · rw [List.mem_singleton] at ho2
      subst o
      omega

lemma iterNat_digits_valid (n : Nat) (ds : List Nat)
    (hds : ∀ d ∈ ds, d < 3) :
    ∀ d ∈ iterNat doubleTernary n ds, d < 3 := by
  revert ds hds
  induction n with
  | zero => intro ds hds; simp [iterNat]; exact hds
  | succ n ih =>
      intro ds hds
      intro d hd
      rw [iterNat] at hd
      exact ih (doubleTernary ds) (doubleTernary_digits_valid ds hds) d hd

theorem Pow2TernaryDigits_digits_valid (n : Nat) :
    ∀ d ∈ Pow2TernaryDigits n, d < 3 := by
  rw [Pow2TernaryDigits]
  exact iterNat_digits_valid n [1] (by simp)

def NoDigitTwo (n : Nat) : Prop :=
  ∀ d ∈ Pow2TernaryDigits n, d ≠ 2

def ErdosTernaryConjecture : Prop :=
  ∀ n : Nat, NoDigitTwo n ↔ n = 0 ∨ n = 2 ∨ n = 8

theorem no_digit_two_zero : NoDigitTwo 0 := by
  simp [NoDigitTwo, Pow2TernaryDigits, iterNat]
theorem no_digit_two_two : NoDigitTwo 2 := by
  simp [NoDigitTwo, Pow2TernaryDigits, iterNat, doubleTernary, doubleCarry, doubleDigit]
theorem no_digit_two_eight : NoDigitTwo 8 := by
  simp [NoDigitTwo, Pow2TernaryDigits, iterNat, doubleTernary, doubleCarry, doubleDigit]
theorem not_no_digit_two_one : ¬ NoDigitTwo 1 := by
  simp [NoDigitTwo, Pow2TernaryDigits, iterNat, doubleTernary, doubleCarry, doubleDigit]

theorem pow2_ten_digits : Pow2TernaryDigits 10 = [1, 2, 2, 1, 0, 1, 1] := by
  native_decide

end ErdosTernary.MiddleDigits
