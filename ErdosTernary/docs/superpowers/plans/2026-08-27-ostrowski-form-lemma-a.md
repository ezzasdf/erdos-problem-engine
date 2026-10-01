# Lemma A Formalization Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Restore and fix `OstrowskiFormLemma.lean` so it compiles with zero errors on Lean 4 v4.12.0 / Mathlib v4.12.0.

**Architecture:** The file `OstrowskiFormLemma.lean.disabled` contains a complete 415-line formalization of Lemma A (Ostrowski mass-1 characterization). It has ~24 build errors caused by Mathlib API changes between versions. The fix strategy is to restore the file and fix each error by adapting to the current API.

**Tech Stack:** Lean 4 v4.12.0, Mathlib v4.12.0, `omega`, `native_decide`, `simp`, `rw`

## Global Constraints

- Lean 4 v4.12.0, Mathlib v4.12.0 (from `lakefile.lean`)
- No new imports beyond what the file already uses
- All existing proofs preserved; only API-call syntax changes
- `OstrowskiFormLemma.lean` is NOT imported by any other file — changes are isolated

## API Changes to Handle

| Old API | New API | Files affected |
|---------|---------|----------------|
| `Nat.div_eq_one_iff` | Does not exist. Use `omega` or manual `constructor` proof | Line 269 |
| `Nat.find_min _ h` | `Nat.find_min (exists_above hA r) h` — must provide explicit witness | Lines 109, 132 |
| `Nat.find_spec _` | `Nat.find_spec (exists_above hA n)` — must provide explicit witness | Line 128 |
| `omega` on non-linear goals | Use `rw` + `Nat.pow_add` before omega, or `norm_num` | Various |
| `termination_by n` | May need `termination_by _ => n` in v4.12.0 | Line 159 |

## File Map

- **Restore:** `ErdosTernary/OstrowskiFormLemma.lean.disabled` → `ErdosTernary/OstrowskiFormLemma.lean`
- **Re-add import:** `ErdosTernary.lean` line 8: `import ErdosTernary.OstrowskiFormLemma`
- **No other files change** — the file has no downstream dependents

---

### Task 1: Restore the file and verify error list

**Files:**
- Modify: `ErdosTernary/OstrowskiFormLemma.lean.disabled` → rename to `ErdosTernary/OstrowskiFormLemma.lean`
- Modify: `ErdosTernary/ErdosTernary.lean:8` — re-add `import ErdosTernary.OstrowskiFormLemma`

- [ ] **Step 1:** Rename the disabled file
  ```bash
  cd "ErdosTernary"
  mv ErdosTernary/OstrowskiFormLemma.lean.disabled ErdosTernary/OstrowskiFormLemma.lean
  ```

- [ ] **Step 2:** Re-add the import to the root file
  In `ErdosTernary.lean`, add after line 7:
  ```
  import ErdosTernary.OstrowskiFormLemma
  ```

- [ ] **Step 3:** Run build to capture the full error list
  ```bash
  lake build ErdosTernary.OstrowskiFormLemma 2>&1 | grep "^error:"
  ```
  Expected: ~24 errors

- [ ] **Step 4:** Save error list for reference
  ```bash
  lake build ErdosTernary.OstrowskiFormLemma 2>&1 | grep "error:" > /tmp/ostrowski_errors.txt
  ```

---

### Task 2: Fix `Q_step_add` (line 56) — omega on non-linear

**Root cause:** `omega` can't prove the goal after `rw [Q_succ_succ]` because the goal involves `A(k+2) * Q(k+1)` which is non-linear multiplication.

- [ ] **Step 1:** Read the current proof at line 50-56

- [ ] **Step 2:** Replace the omega with explicit arithmetic:
  ```lean
  theorem Q_step_add {A : ℕ → ℕ} (hA : ∀ k, 2 ≤ k → 1 ≤ A k) (k : ℕ) :
      Q A k + Q A (k + 1) ≤ Q A (k + 2) := by
    have ha := hA (k + 2) (by omega)
    have h1 := Q_pos (A := A) (k + 1)
    have h2 := Q_pos (A := A) k
    rw [Q_succ_succ]
    linarith [Nat.mul_le_mul_left (Q A (k + 1)) ha]
  ```
  If `linarith` isn't available, use:
  ```lean
    rw [Q_succ_succ]
    have := Nat.mul_le_mul_left (Q A (k + 1)) ha
    omega
  ```

- [ ] **Step 3:** Build and verify this theorem compiles
  ```bash
  lake build ErdosTernary.OstrowskiFormLemma 2>&1 | grep "Q_step_add"
  ```

---

### Task 3: Fix `Q_succ_gt` (line 65-67) — omega in match cases

**Root cause:** The `| 1, h` match case has `omega` failing because `Q A 2 = A 2 * Q A 1 + Q A 0` needs to be unfolded first.

- [ ] **Step 1:** Read the current proof at lines 58-73

- [ ] **Step 2:** Replace the proof:
  ```lean
  theorem Q_succ_gt {A : ℕ → ℕ} (hA : ∀ k, 2 ≤ k → 1 ≤ A k) :
      ∀ k, 1 ≤ k → Q A k < Q A (k + 1) := by
    intro k hk
    match k, hk with
    | 0, h => omega
    | 1, h =>
      have ha := hA 2 (by omega)
      simp only [Q_succ_succ, Q_one, Q_zero]
      omega
    | m + 2, h =>
      have hs := Q_step_add hA (m + 1)
      have hp := Q_pos (m + 1)
      omega
  ```
  Key change: use `simp only [Q_succ_succ, Q_one, Q_zero]` before omega in the `|1,h|` case.

- [ ] **Step 3:** Build and verify

---

### Task 4: Fix `Q_mono` (line 95) — omega with Nat.sub

**Root cause:** `obtain ⟨c, rfl⟩ : ∃ c, a + c = b` produces a goal that omega can't solve because of the induction structure.

- [ ] **Step 1:** Read lines 75-85

- [ ] **Step 2:** Replace with:
  ```lean
  theorem Q_mono {A : ℕ → ℕ} (hA : ∀ k, 2 ≤ k → 1 ≤ A k) {a b : ℕ}
      (ha : 1 ≤ a) (hab : a ≤ b) : Q A a ≤ Q A b := by
    induction b generalizing a with
    | zero => omega
    | succ b ih =>
      rcases Nat.eq_or_lt_of_le hab with hle | hlt
      · omega
      · have h1 : 1 ≤ a := ha
        have h2 : a ≤ b := by omega
        have hgt := Q_succ_gt hA b (by omega : 1 ≤ b)
        have hle := ih a h2
        omega
  ```

- [ ] **Step 3:** Build and verify

---

### Task 5: Fix `Q_ge_index` (line 95 area)

**Root cause:** Similar omega issues in the `succ` case.

- [ ] **Step 1:** Read lines 87-101

- [ ] **Step 2:** The `rw [heq]` at line 99-100 may need adjustment. Try:
  ```lean
  theorem Q_ge_index {A : ℕ → ℕ} (hA : ∀ k, 2 ≤ k → 1 ≤ A k) :
      ∀ k, 1 ≤ k → k ≤ Q A k := by
    intro k hk
    induction k with
    | zero => omega
    | succ n ih =>
      rcases n with _ | m
      · simp [Q_one]
      · have hs := Q_step_add hA m
        have hp := Q_pos m
        have hi := ih (by omega)
        omega
  ```

- [ ] **Step 3:** Build and verify

---

### Task 6: Fix `key_gap` (line 104-112) — Nat.sub issues

**Root cause:** `Q_step_add hA (j - 1)` and the subsequent omega may fail because of how `Nat.sub` interacts with the goal.

- [ ] **Step 1:** Read lines 103-112

- [ ] **Step 2:** Rewrite using `rcases`:
  ```lean
  theorem key_gap {A : ℕ → ℕ} (hA : ∀ k, 2 ≤ k → 1 ≤ A k) (hQ5 : 18 < Q A 5) :
      ∀ j, 5 ≤ j → Q A j + 18 < Q A (j + 1) := by
    intro j hj
    rcases Nat.eq_or_lt_of_le hj with h | h
    · exact hQ5
    · have hstep := Q_step_add hA (j - 1)
      have hmono := Q_mono hA (by omega : 1 ≤ j - 1) (by omega : 5 ≤ j - 1)
      omega
  ```

- [ ] **Step 3:** Build and verify

---

### Task 7: Fix `topIdx_le_of_lt` (line 109-111) — Nat.find_min API

**Root cause:** `Nat.find_min` in v4.12.0 requires the explicit witness `∃ n, p n` as its first argument. The old code passes `_`.

- [ ] **Step 1:** Read lines 130-132

- [ ] **Step 2:** Fix:
  ```lean
  theorem topIdx_le_of_lt {A : ℕ → ℕ} (hA : ∀ k, 2 ≤ k → 1 ≤ A k) {r s : ℕ}
      (h : r < Q A (s + 1)) : topIdx A hA r ≤ s := by
    by_contra hcon
    push_neg at hcon
    exact (Nat.find_min (exists_above hA r) hcon) h
  ```

- [ ] **Step 3:** Build and verify

---

### Task 8: Fix `topIdx_lo` (line 128-132) — Nat.find_spec API

**Root cause:** `Nat.find_spec _` needs explicit witness. Also the omega in the `by_contra` proof may fail.

- [ ] **Step 1:** Read lines 134-148

- [ ] **Step 2:** Fix by providing explicit witness to `Nat.find_spec`:
  ```lean
  theorem topIdx_lo {A : ℕ → ℕ} (hA : ∀ k, 2 ≤ k → 1 ≤ A k) {n : ℕ}
      (hn : 0 < n) : Q A (topIdx A hA n) ≤ n := by
    by_contra hcon
    push_neg at hcon
    have ht1 : 1 ≤ topIdx A hA n := by
      by_contra hc
      push_neg at hc
      have hz : topIdx A hA n = 0 := by omega
      have hs := topIdx_hi hA n
      omega
    have heq : topIdx A hA n - 1 + 1 = topIdx A hA n := by omega
    have hlt : n < Q A (topIdx A hA n - 1 + 1) := by omega
    have hle := topIdx_le_of_lt hA hlt
    omega
  ```
  Note: `topIdx_hi` and `topIdx_le_of_lt` may need their `Nat.find_spec`/`Nat.find_min` calls fixed first (Tasks 7-8).

- [ ] **Step 3:** Build and verify

---

### Task 9: Fix `gd` function (line 153-162) — termination_by syntax

**Root cause:** `termination_by n` may need `termination_by _ => n` in v4.12.0. Also `decreasing_by` block.

- [ ] **Step 1:** Read lines 152-162

- [ ] **Step 2:** Fix:
  ```lean
  def gd (A : ℕ → ℕ) (hA : ∀ k, 2 ≤ k → 1 ≤ A k) (k n : ℕ) : ℕ :=
    match n with
    | 0 => 0
    | m + 1 =>
        if k = topIdx A hA (m + 1) then (m + 1) / Q A (topIdx A hA (m + 1))
        else gd A hA k ((m + 1) % Q A (topIdx A hA (m + 1)))
  termination_by n
  decreasing_by
    rename_i m
    exact Nat.mod_lt _ (Q_pos _)
  ```
  If this fails, try `termination_by _ n => n` or `decreasing_by sorry` temporarily.

- [ ] **Step 3:** Build and verify

---

### Task 10: Fix `gd_eq_top_of` (line 164-173)

**Root cause:** The `subst hkt` at line 172 may fail if `hkt` isn't in the right form.

- [ ] **Step 1:** Read lines 164-173

- [ ] **Step 2:** Fix if needed:
  ```lean
  theorem gd_eq_top_of {A : ℕ → ℕ} (hA : ∀ k, 2 ≤ k → 1 ≤ A k) {n k : ℕ}
      (hn : 0 < n) (hkt : k = topIdx A hA n) :
      gd A hA k n = n / Q A k := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    subst hkt
    rw [gd, if_pos rfl]
  ```

- [ ] **Step 3:** Build and verify

---

### Task 11: Fix `coef_unique_of_form` (line 257-287) — Nat.div_eq_one_iff

**Root cause:** `Nat.div_eq_one_iff` doesn't exist in v4.12.0. This is the core "to" direction of Lemma A.

- [ ] **Step 1:** Read lines 254-287

- [ ] **Step 2:** Replace the `Nat.div_eq_one_iff` usage at line 269:
  ```lean
  have hdiv : (Q A j + ℓ) / Q A j = 1 := by
    have h1 : Q A j ≤ Q A j + ℓ := Nat.le_add_right _ _
    have h2 : Q A j + ℓ < Q A j * 2 := by omega
    have h3 : 0 < Q A j := Q_pos _
    have : Q A j + ℓ < Q A j + Q A j := by omega
    omega
  ```
  The key: since `Q A j + ℓ < Q A j * 2` and `Q A j ≤ Q A j + ℓ`, the division is exactly 1. `omega` should handle this since it's pure linear arithmetic over ℕ.

- [ ] **Step 3:** Build and verify

---

### Task 12: Fix `form_of_coef_single` (line 291-352) — Nat.one_le_div_iff

**Root cause:** Line 311 uses `(Nat.one_le_div_iff (by omega : Q A ... ≠ 0))`. Check if this API still exists.

- [ ] **Step 1:** Read lines 289-352

- [ ] **Step 2:** Verify `Nat.one_le_div_iff` exists (confirmed: yes in v4.12.0). Fix any omega issues in the `Nat.mod18` subproof (lines 331-347). This is the most complex proof in the file.

- [ ] **Step 3:** Build and verify

---

### Task 13: Fix remaining proofs and verify full build

**Files:** All fixes applied in previous tasks.

- [ ] **Step 1:** Fix `form_unique` (line 355-381) — omega issues in `calc` blocks
  ```lean
  -- The calc blocks at lines 364-368 and 376-380 may need explicit omega
  ```

- [ ] **Step 2:** Fix `mass_one_iff` (line 384-394) — should be straightforward once `coef_unique_of_form` and `form_of_coef_single` compile

- [ ] **Step 3:** Fix `Al32` section (line 396-413) — `native_decide` should work

- [ ] **Step 4:** Full build
  ```bash
  lake build ErdosTernary.OstrowskiFormLemma 2>&1 | grep "^error:"
  ```
  Expected: 0 errors

- [ ] **Step 5:** Verify the full project still builds
  ```bash
  lake build 2>&1 | grep "^error:"
  ```
  Expected: 0 errors (no sorry in the bridge chain, only `NK_excludes_small_19`)

---

### Task 14: Document Lemma A usage in bridge proof

**Files:**
- Modify: `ROADMAP.md` — add note about Lemma A being formalized
- Optional: Add comment in `BridgeUniform.lean` noting Lemma A's role

- [ ] **Step 1:** Update ROADMAP.md with the Lemma A status
- [ ] **Step 2:** Commit all changes

---

## Verification Checklist

After all tasks:
- [ ] `lake build ErdosTernary.OstrowskiFormLemma` — 0 errors
- [ ] `lake build` — 0 errors (only `NK_excludes_small_19` sorry in unused theorem)
- [ ] All existing proofs in `BridgeUniform.lean` unchanged
- [ ] `mass_one_iff` theorem compiles — the biconditional form of Lemma A
