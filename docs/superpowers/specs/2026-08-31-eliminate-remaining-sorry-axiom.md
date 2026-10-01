# Design: Eliminate Remaining Sorry and Axiom

**Date:** 2026-08-31
**Goal:** Remove 1 sorry and 1 axiom from the Erdős ternary bridge theorem, reducing total sorry count from 1 to 0 (for the bridge path).

## Current State

| File | Symbol | Type | Lines |
|------|--------|------|-------|
| `Mass1Dynamics.lean` | `mass1_in_NK_empty_K13_25` | sorry (placeholder) | 228 |
| `Mass1Dynamics.lean` | `mass1_j_ge_38_trail2` | axiom | 232 |
| `BridgeUniform.lean` | `NK_excludes_small_19` | sorry | 175 |

**Dependency chain:** `no_births_after_K7` (Mass1Dynamics) → uses `mass1_in_NK_empty_K13_25` (sorry) and `mass1_j_ge_38_trail2` (axiom) → feeds into `conditional_extinction` → feeds into `no_mass1_for_large_K`. The `NK_excludes_small_19` is used by `bridge_small_n` in BridgeUniform.

---

## Task 1: mass1_in_NK_empty_K13_25 → native_decide

### What it does
Proves that for K∈[13,25], no element of `computeNK K` has Ostrowski mass 1. This is a pure computation: enumerate all residues in `computeNK K`, check if any have the mass-1 form, return empty list.

### Approach
Split the single sorry into 13 individual theorems (K=13..25), each proved by `native_decide`. Two tiers:

- **Tier 1 (K=13..16):** `computeNK` sizes are 1.5M..47M elements. Binary pow2ModAux makes these fast (seconds).
- **Tier 2 (K=17..25):** `computeNK` sizes grow to ~4.6 billion. Each native_decide takes minutes to hours. Defer to background `lake build`.

### Implementation

Replace the single theorem:
```lean
theorem mass1_in_NK_empty_K13_25 (K : ℕ) (hK : 13 ≤ K ∧ K ≤ 25) :
    mass1_in_NK K = [] := by sorry
```

With individual theorems:
```lean
theorem mass1_in_NK_empty_K13 : mass1_in_NK 13 = [] := by native_decide
theorem mass1_in_NK_empty_K14 : mass1_in_NK 14 = [] := by native_decide
-- ... through K=16 (Tier 1)
-- K=17..25: proved via background lake build, referenced as:
theorem mass1_in_NK_empty_K17 : mass1_in_NK 17 = [] := by native_decide
-- ... through K=25
```

Then reconstruct the combined theorem:
```lean
theorem mass1_in_NK_empty_K13_25 (K : ℕ) (hK : 13 ≤ K ∧ K ≤ 25) :
    mass1_in_NK K = [] := by
  interval_cases K <;> simp_all [
    mass1_in_NK_empty_K13, mass1_in_NK_empty_K14, mass1_in_NK_empty_K15,
    mass1_in_NK_empty_K16, mass1_in_NK_empty_K17, mass1_in_NK_empty_K18,
    mass1_in_NK_empty_K19, mass1_in_NK_empty_K20, mass1_in_NK_empty_K21,
    mass1_in_NK_empty_K22, mass1_in_NK_empty_K23, mass1_in_NK_empty_K24,
    mass1_in_NK_empty_K25]
```

### Risk
K=17..25 may timeout even in background build. Fallback: keep sorry for K=17..25 only, or reduce to a smaller range.

---

## Task 2: mass1_j_ge_38_trail2 → native_decide

### What it does
Asserts that for j≥38, K≥26, ℓ≤18, if Q(Al32,j)+ℓ < uK(K), then `pow2Mod (Q(j)+ℓ) (3^K)` has digit 2 in its last K ternary digits. This is the key lemma that the j≥38 mass-1 candidates cannot exist in `computeNK K`.

### Approach — Finite enumeration via native_decide

For j≥38, all partial quotients A(j)=1, so Q(j) grows as Fibonacci. The constraint Q(j)+18 < uK(K) bounds j:

- K=26: uK(26) = 16,888,868. Q(j)+18 < 16.9M → j ∈ [38, 51]
- K=27: uK(27) = 50,666,604. Q(j)+18 < 50.7M → j ∈ [38, 54]
- K=28: uK(28) = 151,999,812. Q(j)+18 < 152M → j ∈ [38, 57]
- ...up to K=34 (where Q(38)+18 > uK(34))

For K≥35, Q(38)+18 > uK(35), so the condition `Q(j)+ℓ < uK(K)` is vacuously false for all j≥38. No proof needed.

**Total proof obligation:** ~200 (j,K,ℓ) triples, each a native_decide on a small computation.

### Implementation

Replace the axiom:
```lean
axiom mass1_j_ge_38_trail2 (K : ℕ) (hK : K ≥ 26) (j : ℕ) (hj : j ≥ 38)
    (ℓ : ℕ) (hℓ : ℓ ≤ 18) (hr : Q Al32 j + ℓ < uK K) :
    hasTrailingDigit2 (pow2Mod (Q Al32 j + ℓ) (3 ^ K)) K = true
```

With a theorem proved by case analysis:
```lean
theorem mass1_j_ge_38_trail2 (K : ℕ) (hK : K ≥ 26) (j : ℕ) (hj : j ≥ 38)
    (ℓ : ℕ) (hℓ : ℓ ≤ 18) (hr : Q Al32 j + ℓ < uK K) :
    hasTrailingDigit2 (pow2Mod (Q Al32 j + ℓ) (3 ^ K)) K = true := by
  -- For K ≥ 35: Q(38)+18 > uK(35), so hr is contradictory
  by_cases hK35 : K ≥ 35
  · have h38 : Q Al32 38 + 18 < uK K := by
      have hq := Q_mono Al32_hyp (by omega : 1 ≤ j) (le_trans (by omega : j ≥ 38) (by omega : 38 ≤ j))
      have h38_uk : Q Al32 38 + 18 ≥ uK 35 := by native_decide
      have huk : uK 35 ≤ uK K := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by norm_num) hK35)
      omega
    omega
  · push_neg at hK35
    -- K ∈ [26, 34]: enumerate all (j, ℓ) pairs
    interval_cases K <;> native_decide
```

### Risk
The `interval_cases K` produces 9 cases (K=26..34). Each native_decide must evaluate `pow2Mod (Q(j)+ℓ) (3^K)` for all j in the valid range and ℓ∈[0,18]. This should be fast since 3^K is at most 3^34 ≈ 1.7×10^16, well within 64-bit range for K≤17, but requires big integer for K≥18. The binary pow2ModAux handles this efficiently.

---

## Task 3: NK_excludes_small_19 → proof

### What it does
Proves that for K≥5, any r ∈ computeNK K with r ≠ 0,2,8 satisfies r ≥ 19. This is used by `bridge_small_n` to restrict the Cantor set check to r ≥ 19.

### Approach
Extend the exact pattern of `NK_excludes_small` (which proves r ≥ 9) to cover r = 9..18. All 10 trail2 lemmas (`trail2_r9` through `trail2_r18`) already exist in BridgeUniform.lean.

### Implementation

```lean
theorem NK_excludes_small_19 (K : Nat) (hK : K ≥ 5) (r : Nat)
    (hr : r ∈ computeNK K) (hSpecial : r ≠ 0 ∧ r ≠ 2 ∧ r ≠ 8) :
    r ≥ 19 := by
  by_contra hlt; push_neg at hlt
  have h2r_lt : 2 ^ r < 3 ^ K := by
    have h2r : 2 ^ r ≤ 2 ^ 18 := Nat.pow_le_pow_right (by omega) (by omega)
    have h3k : 3 ^ 5 ≤ 3 ^ K := Nat.pow_le_pow_right (by omega) (by omega : 5 ≤ K)
    omega
  have hmod : 2 ^ r % 3 ^ K = 2 ^ r := Nat.mod_eq_of_lt h2r_lt
  unfold computeNK at hr
  simp only [List.mem_filter, Finset.mem_range] at hr
  obtain ⟨hlt_u, hno2⟩ := hr
  rw [hmod] at hno2
  interval_cases r
  · exact absurd rfl hSpecial.1
  · have := trail2_r1 K hK; simp_all [Bool.not_eq_true]
  · exact absurd rfl hSpecial.2.1
  · have := trail2_r3 K hK; simp_all [Bool.not_eq_true]
  · have := trail2_r4 K hK; simp_all [Bool.not_eq_true]
  · have := trail2_r5 K hK; simp_all [Bool.not_eq_true]
  · have := trail2_r6 K hK; simp_all [Bool.not_eq_true]
  · have := trail2_r7 K hK; simp_all [Bool.not_eq_true]
  · exact absurd rfl hSpecial.2.2
  · have := trail2_r9 K hK; simp_all [Bool.not_eq_true]
  · have := trail2_r10 K hK; simp_all [Bool.not_eq_true]
  · have := trail2_r11 K hK; simp_all [Bool.not_eq_true]
  · have := trail2_r12 K hK; simp_all [Bool.not_eq_true]
  · have := trail2_r13 K hK; simp_all [Bool.not_eq_true]
  · have := trail2_r14 K hK; simp_all [Bool.not_eq_true]
  · have := trail2_r15 K hK; simp_all [Bool.not_eq_true]
  · have := trail2_r16 K hK; simp_all [Bool.not_eq_true]
  · have := trail2_r17 K hK; simp_all [Bool.not_eq_true]
  · have := trail2_r18 K hK; simp_all [Bool.not_eq_true]
```

### Risk
Low — mechanical extension of existing code. The only concern is `interval_cases r` with 19 cases, but this is just a case split, not computation.

---

## Execution Order

1. **Task 3 first** (NK_excludes_small_19) — smallest, no dependencies, immediate payoff
2. **Task 1 second** (K=13..16 native_decide) — fast tier, immediate payoff
3. **Task 2 third** (mass1_j_ge_38_trail2) — eliminates axiom, requires careful case analysis
4. **Task 1 tier 2** (K=17..25 native_decide) — background lake build, slowest

## Success Criteria

- 0 sorry in Mass1Dynamics.lean and BridgeUniform.lean (bridge path)
- 0 axioms in Mass1Dynamics.lean
- All files compile with `lake env lean`
- `lake build` completes for Tier 1 (K=13..16) within 10 minutes

## Files Modified

- `ErdosTernary/ErdosTernary/Mass1Dynamics.lean` — Tasks 1 and 2
- `ErdosTernary/ErdosTernary/BridgeUniform.lean` — Task 3
