# Phase 7 M3: Lean Formalization of the Base-3 Doubling Transducer

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Formalize in Lean 4 (mathlib) the base-3 doubling transducer used by `verify_middle` — prove `Pow2TernaryDigits n` computes the LSB-first base-3 digits of `2^n`, that all digits are `< 3`, and state the Erdős–Ternary conjecture (`NoDigitTwo n ↔ n = 0 ∨ n = 2 ∨ n = 8`), discharging the four finite base cases and one `native_decide` digit-string case.

**Architecture:** A pure-`Nat` functional transducer (`doubleCarry c ds` folds a per-digit doubling with carry over the digit list; `doubleTernary ds` appends the final carry digit; `iterNat` iterates it starting from `[1]`). Correctness is by induction: `doubleCarry_eval` ties the transducer to `evalTernary` (LSB-first `Nat` value), `doubleTernary_correct` proves doubling exactly, and `Pow2TernaryDigits_correct` proves `E(digits 2^n) = 2^n`. Digit validity follows from carry bounds via `omega`. The conjecture is stated with its finite cases proved by `simp` on the fully-unfolded definitions.

**Tech Stack:** Lean 4.12.0 (`leanprover/lean4:v4.12.0`), mathlib `v4.12.0`, the existing `erdosTernary` Lake package (`ErdosTernary/`). Verification uses `lake env lean <file>` (fast, no rebuild of mathlib needed).

## Global Constraints

- Lean toolchain is pinned by `ErdosTernary/lean-toolchain` to `leanprover/lean4:v4.12.0`; `ErdosTernary/lakefile.lean` pins mathlib `@ "v4.12.0"`. Do not upgrade or add dependencies.
- **Zero `sorry`/`admit`** in committed code. Every committed declaration must compile with `lake env lean ErdosTernary/MiddleDigits.lean` with EXIT 0 and no warnings.
- Work happens in an isolated git worktree on a new branch `phase7-m3` created from `main` (create it before Task 1 with the `using-git-worktrees` skill; if already created, reuse it). Commit once per task.
- Commit message style in this repo is conventional: `feat(lean): ...` / `docs(lean): ...`.
- All arithmetic is `Nat`; digits are LSB-first (`evalTernary (d :: ds) = d + 3 * evalTernary ds`, defined in `ErdosTernary/TernaryExp.lean`).
- **Known Lean 4.12 gotchas (verified — do not fight them):**
  - `Nat.iterate` / `Function.iterate` do **not** exist in this mathlib. Define the local `iterNat` below.
  - `rcases` on a compound term (e.g. `rcases doubleCarry c ds with ⟨a, b⟩`) does **not** reliably substitute projections in other hypotheses. Use: `let p := e; have hp0 : p = e := rfl; rcases p with ⟨a, b⟩; have hp : e = (a, b) := hp0.symm`.
  - `native_decide` fails to synthesize `Decidable` for a `Prop` hidden behind a `def` (e.g. `NoDigitTwo 0`). Prove those finite cases with `simp [NoDigitTwo, Pow2TernaryDigits, iterNat, doubleTernary, doubleCarry, doubleDigit]`. For a direct list equality (`pow2_ten_digits`) `native_decide` works.
  - `omega` is linear-only; when `3 ^ ds.length` products appear use `nlinarith` instead.
  - `rw [h]` for `h : a = b` rewrites `a → b` (LHS to RHS). Use `rw [← h]` for the reverse.
  - An `evalTernary`/`nat` goal of the form `2 ^ n * evalTernary (doubleTernary ds) = 2 ^ (n + 1) * evalTernary ds` needs `rw [pow_succ]` + `ring`.

## File Structure

- `ErdosTernary/ErdosTernary/MiddleDigits.lean` — **create**: the whole formalization (transducer + correctness + digit-validity + conjecture). Single file, ~180 lines, namespace `ErdosTernary.MiddleDigits`.
- `ErdosTernary/ErdosTernary.lean` — **modify**: append `import ErdosTernary.MiddleDigits` so the root file (and `lake build ErdosTernary`) picks it up.

Tasks build the file incrementally. After every task the file compiles clean; only at Task 5 is the import added and the whole lib built.

## Task 1: Transducer core (`doubleDigit`, `doubleCarry`) + `doubleCarry_eval` + `evalTernary_append_singleton`

**Files:**
- Create: `ErdosTernary/ErdosTernary/MiddleDigits.lean`

**Interfaces:**
- Consumes: `evalTernary` from `ErdosTernary.TernaryExp` (LSB-first: `evalTernary (d :: ds) = d + 3 * evalTernary ds`, `evalTernary [] = 0`).
- Produces: `doubleDigit : Nat → Nat → Nat × Nat`; `doubleCarry : Nat → List Nat → List Nat × Nat`; `doubleCarry_eval : (c : Nat) (ds : List Nat) → 2 * evalTernary ds + c = evalTernary (doubleCarry c ds).1 + (doubleCarry c ds).2 * 3 ^ ds.length`; `evalTernary_append_singleton : (ds : List Nat) (c : Nat) → evalTernary (ds ++ [c]) = evalTernary ds + c * 3 ^ ds.length`.

- [ ] **Step 1: Create the file with the verified core**

Create `ErdosTernary/ErdosTernary/MiddleDigits.lean` with exactly:

```lean
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
```

- [ ] **Step 2: Verify it compiles clean**

Run: `cd ErdosTernary && timeout 400 lake env lean ErdosTernary/MiddleDigits.lean`
Expected: no output, exit status 0, no warnings. (`lake env lean` requires the imported modules to already be built; if it fails with "no build" errors run `lake build ErdosTernary` once first.)

- [ ] **Step 3: Commit**

```bash
git add ErdosTernary/ErdosTernary/MiddleDigits.lean
git commit -m "feat(lean): base-3 doubling transducer core (doubleCarry + eval lemma)"
```

## Task 2: `doubleTernary` + `doubleCarry_length` + `doubleTernary_correct`

**Files:**
- Modify: `ErdosTernary/ErdosTernary/MiddleDigits.lean` (append after `evalTernary_append_singleton`)

**Interfaces:**
- Consumes: `doubleCarry`, `doubleCarry_eval` (Task 1), `evalTernary_append_singleton` (Task 1).
- Produces: `doubleTernary : List Nat → List Nat`; `doubleCarry_length : (c : Nat) (ds : List Nat) → (doubleCarry c ds).1.length = ds.length`; `doubleTernary_correct : (ds : List Nat) → 2 * evalTernary ds = evalTernary (doubleTernary ds)`.

- [ ] **Step 1: Append the verified doubling + correctness**

```lean
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
```

- [ ] **Step 2: Verify it compiles clean**

Run: `cd ErdosTernary && timeout 400 lake env lean ErdosTernary/MiddleDigits.lean`
Expected: no output, exit 0, no warnings.

- [ ] **Step 3: Commit**

```bash
git add ErdosTernary/ErdosTernary/MiddleDigits.lean
git commit -m "feat(lean): doubleTernary appends final carry; doubling correctness"
```

## Task 3: `iterNat` + `Pow2TernaryDigits` + iteration correctness + digit cross-check

**Files:**
- Modify: `ErdosTernary/ErdosTernary/MiddleDigits.lean` (append after `doubleTernary_correct`)

**Interfaces:**
- Consumes: `doubleTernary`, `doubleTernary_correct` (Task 2).
- Produces: `iterNat : {α : Type} → (α → α) → Nat → α → α` (repeat `f` `n` times); `Pow2TernaryDigits : Nat → List Nat` (LSB-first base-3 digits of `2^n`); `iterNat_double_eval : (n : Nat) (ds : List Nat) → evalTernary (iterNat doubleTernary n ds) = 2 ^ n * evalTernary ds`; `Pow2TernaryDigits_correct : (n : Nat) → evalTernary (Pow2TernaryDigits n) = 2 ^ n`.

- [ ] **Step 1: Append the verified iteration + correctness**

```lean
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
```

- [ ] **Step 2: Verify compile + in-Lean `#eval` spot checks**

Append these two lines at the end of the file (before the closing `end`), run the check, then delete them:

```lean
#eval Pow2TernaryDigits 8
#eval Pow2TernaryDigits 10
```

Run: `cd ErdosTernary && timeout 400 lake env lean ErdosTernary/MiddleDigits.lean`
Expected output contains `[1, 1, 1, 0, 0, 1]` (2⁸ = 256 = 100111₃) and `[1, 2, 2, 1, 0, 1, 1]` (2¹⁰ = 1024 = 1101221₃). Then delete the two `#eval` lines.

- [ ] **Step 3: Cross-check against an independent Python implementation**

Run:
```bash
python3 - <<'EOF'
def digits(n):
    ds = []
    while n:
        ds.append(n % 3); n //= 3
    return ds or [0]
for n in (1, 2, 3, 5, 8, 10, 15, 20):
    print(n, digits(2**n))
EOF
```
Expected: `1 [2]`, `2 [1,1]`, `3 [2,2]`, `5 [2,1,2,1]`, `8 [1,1,1,0,0,1]`, `10 [1,2,2,1,0,1,1]` — matches the LSB-first base-3 digits of `2^n` (same as the `verify_middle` carry-chain stream). Spot-check each against the Lean output from Step 2 (re-run the `#eval` lines if desired); the `n = 8, 10` rows above already match.

- [ ] **Step 4: Verify clean + commit**

Run: `cd ErdosTernary && timeout 400 lake env lean ErdosTernary/MiddleDigits.lean`
Expected: exit 0, no warnings (the `#eval` lines removed).

```bash
git add ErdosTernary/ErdosTernary/MiddleDigits.lean
git commit -m "feat(lean): Pow2TernaryDigits = LSB-first base-3 digits of 2^n"
```

## Task 4: Digit-validity (`< 3`) for the transducer and powers

**Files:**
- Modify: `ErdosTernary/ErdosTernary/MiddleDigits.lean` (append after `Pow2TernaryDigits_correct`)

**Interfaces:**
- Consumes: `doubleCarry`, `doubleDigit`, `doubleTernary`, `iterNat`, `Pow2TernaryDigits` (Tasks 1–3).
- Produces: `carry_le_one : {d c : Nat} → d < 3 → c ≤ 1 → (2 * d + c) / 3 ≤ 1`; `out_lt_three : (d c : Nat) → (2 * d + c) % 3 < 3`; `doubleCarry_digits_valid : (c : Nat) → c ≤ 1 → (ds : List Nat) → (∀ d ∈ ds, d < 3) → (∀ o ∈ (doubleCarry c ds).1, o < 3) ∧ (doubleCarry c ds).2 ≤ 1`; `doubleTernary_digits_valid : (ds : List Nat) → (∀ d ∈ ds, d < 3) → ∀ o ∈ doubleTernary ds, o < 3`; `iterNat_digits_valid : (n : Nat) (ds : List Nat) → (∀ d ∈ ds, d < 3) → ∀ d ∈ iterNat doubleTernary n ds, d < 3`; `Pow2TernaryDigits_digits_valid : (n : Nat) → ∀ d ∈ Pow2TernaryDigits n, d < 3`.

- [ ] **Step 1: Append the verified digit-validity lemmas**

```lean
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
```

- [ ] **Step 2: Verify it compiles clean**

Run: `cd ErdosTernary && timeout 400 lake env lean ErdosTernary/MiddleDigits.lean`
Expected: no output, exit 0, no warnings (watch for `unusedVariables`/`unnecessarySimpa` lints — the code above is already lint-clean).

- [ ] **Step 3: Commit**

```bash
git add ErdosTernary/ErdosTernary/MiddleDigits.lean
git commit -m "feat(lean): all transducer/power digits are < 3"
```

## Task 5: Conjecture statement + finite base cases + `pow2_ten_digits` + register import + full build

**Files:**
- Modify: `ErdosTernary/ErdosTernary/MiddleDigits.lean` (append before the closing `end`)
- Modify: `ErdosTernary/ErdosTernary.lean` (append `import ErdosTernary.MiddleDigits` at the end)

**Interfaces:**
- Consumes: `Pow2TernaryDigits`, `Pow2TernaryDigits_digits_valid` (Tasks 3–4).
- Produces: `NoDigitTwo : Nat → Prop`; `ErdosTernaryConjecture : Prop`; `no_digit_two_zero / no_digit_two_two / no_digit_two_eight : NoDigitTwo 0 / 2 / 8`; `not_no_digit_two_one : ¬ NoDigitTwo 1`; `pow2_ten_digits : Pow2TernaryDigits 10 = [1, 2, 2, 1, 0, 1, 1]`; the import is registered so `lake build ErdosTernary` succeeds.

- [ ] **Step 1: Append the verified conjecture + finite cases**

```lean
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
```

- [ ] **Step 2: Register the import in the root file**

Append to the end of `ErdosTernary/ErdosTernary.lean`:

```lean
import ErdosTernary.MiddleDigits
```

- [ ] **Step 3: Verify file compiles + full lib builds**

Run: `cd ErdosTernary && timeout 400 lake env lean ErdosTernary/MiddleDigits.lean && timeout 900 lake build ErdosTernary`
Expected: `lake env lean` silent exit 0; `lake build ErdosTernary` succeeds (builds the root file, which now imports MiddleDigits).

- [ ] **Step 4: Update ROADMAP and commit**

In `ROADMAP.md`, flip the M3 checkbox on line 221 to `[x]` and append a one-line summary of what was proved (doubling correctness, digit validity, conjecture statement + base cases + `pow2_ten_digits`).

```bash
git add ErdosTernary/ErdosTernary/MiddleDigits.lean ErdosTernary/ErdosTernary.lean ROADMAP.md
git commit -m "feat(lean): ErdosTernaryConjecture statement, finite base cases, register MiddleDigits"
```
