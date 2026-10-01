# Lagarias Hausdorff-Dimension Formalization Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Create `ErdosTernary/ErdosTernary/LagariasHausdorff.lean` defining Lagarias's (2009) exceptional sets and stating his Hausdorff-dimension theorems and conjectures, with zero `sorry`/`axiom`/`admit`.

**Architecture:** A single Lean file under `namespace LagariasHausdorff` holding: (a) definitions of the 3-adic Cantor set membership predicate `memSigma₃₂` and the exceptional-set membership predicates `memEk`/`memE`; (b) the real truncated/untruncated predicates `memETrunc`/`memEReal` using `Narkiewicz.memCantorNat` and mathlib's real `cantorSet`; (c) all theorem/conjecture statements as `noncomputable def … : Prop` (never axioms); (d) one genuinely-proved nesting lemma `Ek (k+1) ⊆ Ek k`. The statements never unfold `dimH` on `ℤ_[3]` without the required `borel` measurable-space instance, so a local helper `dimH₃` supplies it via `letI`.

**Tech Stack:** Lean 4.12.0, mathlib 4.12.0 (pinned). Only stdlib/mathlib imports. Uses existing project file `ErdosTernary/Narkiewicz.lean` for `memCantorNat`/`digit₃`.

## Global Constraints

- Lean `v4.12.0` + mathlib `v4.12.0` (pinned, project-wide) — never bump.
- stdlib/mathlib only, no third-party deps.
- Zero `sorry` / `axiom` / `admit` anywhere in the new file (grep-verified).
- All theorem/conjecture statements are `noncomputable def … : Prop`; conjectures carry docstrings explicitly labeled **OPEN**.
- One commit per task, conventional commit style (`feat:`, `fix:`, `docs:`), task-wise review.
- Module path: `ErdosTernary/ErdosTernary/LagariasHausdorff.lean` → `import ErdosTernary.LagariasHausdorff`.
- Build command from `ErdosTernary/`: `lake env lean ErdosTernary/LagariasHausdorff.lean` and `lake build ErdosTernary`.
- ROADMAP correction (line 17 + action item 7) is **already committed** (`61b1571`) — this plan only verifies, never re-edits ROADMAP.
- `λ` is a Lean binder token — never use it as an identifier; use `lam` throughout.

---

## Reference: Complete Target File Content

The three tasks below assemble this file. The full content is reproduced in Task 2 so a worker reading only that task sees the whole file.

```lean
/-
  Lagarias's Hausdorff-Dimension Results on Ternary Expansions of Powers of 2.

  Definitions and theorem/conjecture statements from
  J. C. Lagarias, "Ternary expansions of powers of 2",
  J. London Math. Soc. 79 (2009) 562-588.

  This file defines the 3-adic and real exceptional sets and states the
  Hausdorff-dimension results.  It does NOT prove the dimension theorems;
  the OPEN conjectures are explicitly labeled as such.

  Reference numbering (published version):
    Thm 1.3  : dimH E^T(R^+) = log_3 2          (truncated real exceptional set)
    Thm 1.6  : dimH bounds for E^(k)(Z_3), k = 1, 2, 3
    Conj 1.4 : dimH E(R^+) = 0                  (real untruncated; OPEN)
    Conj 1.7 : dimH E(Z_3) = 0                  (3-adic; OPEN)
-/

import ErdosTernary.Narkiewicz
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Topology.Instances.CantorSet
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

open scoped ENNReal NNReal

namespace LagariasHausdorff

/-! ## 3-adic Cantor set and exceptional sets -/

/-- Membership in the 3-adic Cantor set Σ_{3,2} ⊆ ℤ_[3]: every prefix of the
  3-adic expansion omits the digit 2, i.e. for every n the residue of `lam`
  modulo `3^n` equals some `r < 3^n` whose ternary digits are all 0 or 1
  (`Narkiewicz.memCantorNat r`) and whose 3-adic distance from `lam` is at
  most `3^(-n)`.  (Lagarias §1.4, eq. (1.15).) -/
def memSigma₃₂ (lam : ℤ_[3]) : Prop :=
  ∀ n : ℕ, ∃ r : ℕ, r < 3 ^ n ∧ Narkiewicz.memCantorNat r ∧
    ‖lam - (r : ℤ_[3])‖ ≤ (3 : ℝ) ^ (- (n : ℤ))

/-- E^(k)(ℤ₃): at least `k` distinct `m` with `lam·2^m ∈ Σ_{3,2}`.  (Lagarias
  eq. (1.11).) -/
def memEk (k : ℕ) (lam : ℤ_[3]) : Prop :=
  ∃ s : Finset ℕ, s.card = k ∧ ∀ m ∈ s, memSigma₃₂ (lam * (2 : ℤ_[3]) ^ m)

/-- E(ℤ₃) = E*(ℤ₃): infinitely many `m` with `lam·2^m ∈ Σ_{3,2}`.  (Lagarias
  eq. (1.10); the design spec's `E*` coincides with `E`, since "the set of m is
  infinite" is identical to "infinitely many m".) -/
def memE (lam : ℤ_[3]) : Prop :=
  Set.Infinite { m : ℕ | memSigma₃₂ (lam * (2 : ℤ_[3]) ^ m) }

/-- Hausdorff dimension on `ℤ_[3]`.  mathlib's `dimH` requires `[MeasurableSpace
  X] [BorelSpace X]`, which `ℤ_[3]` lacks; the `borel` measurable space is
  provided locally. -/
noncomputable def dimH₃ (s : Set (ℤ_[3])) : ℝ≥0∞ := by
  letI : MeasurableSpace (ℤ_[3]) := borel (ℤ_[3])
  exact dimH s

/-- log₃2 = log 2 / log 3, as an extended nonnegative real. -/
noncomputable def log3two : ℝ≥0∞ := ENNReal.ofReal (Real.log 2 / Real.log 3)

/-- E^(k)(ℤ₃) as a set, as a family over k. -/
noncomputable def Ek (k : ℕ) : Set (ℤ_[3]) := { lam : ℤ_[3] | memEk k lam }

/-- E(ℤ₃) as a set. -/
noncomputable def EZ3 : Set (ℤ_[3]) := { lam : ℤ_[3] | memE lam }

/-! ## Real truncated and untruncated exceptional sets -/

/-- A real `x` omits the digit 2 in its (full) ternary expansion iff its
  integer part has ternary digits all in {0,1} (`Narkiewicz.memCantorNat`) and
  its fractional part has ternary digits all in {0,1}, which holds iff twice
  the fractional part lies in the middle-thirds Cantor set `cantorSet` (whose
  ternary digits are {0,2}; doubling maps digit-{0,1} numbers to digit-{0,2}
  numbers with no carries). -/
def RealOmitsTwo (x : ℝ) : Prop :=
  Narkiewicz.memCantorNat (Nat.floor x) ∧ 2 * (x - (Nat.floor x : ℝ)) ∈ cantorSet

/-- E^T(R⁺): infinitely many `⌊lam·2^n⌋` omit the digit 2.  (Lagarias
  eq. (1.7).) -/
def memETrunc (lam : ℝ) : Prop :=
  Set.Infinite { n : ℕ | Narkiewicz.memCantorNat (Nat.floor (lam * 2 ^ n)) }

/-- E^T(R⁺) as a set. -/
noncomputable def ETrunc : Set ℝ := { lam : ℝ | 0 < lam ∧ memETrunc lam }

/-- E(R⁺): infinitely many full ternary expansions `(lam·2^n)` omit the digit
  2.  (Lagarias eq. (1.8).) -/
def memEReal (lam : ℝ) : Prop :=
  Set.Infinite { n : ℕ | RealOmitsTwo (lam * 2 ^ n) }

/-- E(R⁺) as a set. -/
noncomputable def EReal : Set ℝ := { lam : ℝ | 0 < lam ∧ memEReal lam }

/-! ## Theorem and conjecture statements (never axioms) -/

/-- Theorem 1.3 (proved in Lagarias): the truncated real exceptional set has
  Hausdorff dimension log₃2. -/
noncomputable def thm_1_3 : Prop := dimH ETrunc = log3two

/-- Theorem 1.6(i) (proved in Lagarias): dimH E^(1)(ℤ₃) = log₃2. -/
noncomputable def thm_1_6_i : Prop := dimH₃ (Ek 1) = log3two

/-- Theorem 1.6(ii) (proved in Lagarias): ½·log₃2 ≤ dimH E^(2)(ℤ₃) ≤ ½. -/
noncomputable def thm_1_6_ii : Prop :=
  ENNReal.ofReal ((1 : ℝ) / 2 * Real.log 2 / Real.log 3) ≤ dimH₃ (Ek 2) ∧
    dimH₃ (Ek 2) ≤ ENNReal.ofReal ((1 : ℝ) / 2)

/-- Theorem 1.6(iii) (proved in Lagarias): ⅙·log₃2 ≤ dimH E^(3)(ℤ₃) ≤
  dimH E^(2)(ℤ₃). -/
noncomputable def thm_1_6_iii : Prop :=
  ENNReal.ofReal ((1 : ℝ) / 6 * Real.log 2 / Real.log 3) ≤ dimH₃ (Ek 3) ∧
    dimH₃ (Ek 3) ≤ dimH₃ (Ek 2)

/-- Conjecture 1.4 (Lagarias Conjecture A): the real untruncated exceptional
  set has Hausdorff dimension zero.  **OPEN** — not proved. -/
noncomputable def conj_1_4 : Prop := dimH EReal = 0

/-- Conjecture 1.7 (Lagarias Conjecture B): the 3-adic exceptional set has
  Hausdorff dimension zero.  **OPEN** — not proved. -/
noncomputable def conj_1_7 : Prop := dimH₃ EZ3 = 0

/-! ## Trivial proved lemmas -/

/-- E^(k+1) ⊆ E^(k): dropping any one of the k+1 witnessing powers of 2 leaves
  k witnesses. -/
theorem memEk_mono {k lam} (h : memEk (k + 1) lam) : memEk k lam := by
  rcases h with ⟨s, hcard, hmem⟩
  have hne : s.Nonempty := by
    exact Finset.card_pos.mp (by omega)
  let e := s.min' hne
  refine ⟨s.erase e, ?_, ?_⟩
  · simp [hcard, Finset.card_erase_of_mem (Finset.min'_mem s hne)]
  · intro m hm
    exact hmem m (Finset.mem_of_mem_erase hm)

/-- E^(k+1)(ℤ₃) ⊆ E^(k)(ℤ₃) as set inclusion. -/
theorem E_mono {k : ℕ} : Ek (k + 1) ⊆ Ek k := by
  intro lam hlam
  exact memEk_mono hlam

end LagariasHausdorff
```

---

## File Structure

- `ErdosTernary/ErdosTernary/LagariasHausdorff.lean` — new file, whole deliverable.
- `ErdosTernary/ErdosTernary.lean` — append `import ErdosTernary.LagariasHausdorff` (Task 3).
- `ROADMAP.md` — already corrected in commit `61b1571`; verification only.

## Task Decomposition

Three tasks:
1. **Definitions** — write the file with all `def` blocks (3-adic + real) and verify `lake env lean` exits 0.
2. **Statements + nesting lemma** — append the six statements and the proved `memEk_mono`/`E_mono`; verify full-file `lake env lean` exit 0.
3. **Register import + verify** — append import to `ErdosTernary.lean`, run `lake build ErdosTernary`, grep zero `sorry`/`axiom`/`admit`, confirm ROADMAP already corrected; final commit.

---

### Task 1: Definitions

**Files:**
- Create: `ErdosTernary/ErdosTernary/LagariasHausdorff.lean`

**Interfaces:**
- Consumes: `Narkiewicz.memCantorNat : ℕ → Prop`, `Narkiewicz.digit₃` (from `import ErdosTernary.Narkiewicz`); `dimH` (root namespace, from `Mathlib.Topology.MetricSpace.HausdorffDimension`); `ℤ_[3]` (= `PadicInt 3`, from `Mathlib.NumberTheory.Padics.PadicIntegers`); real `cantorSet : Set ℝ` (from `Mathlib.Topology.Instances.CantorSet`).
- Produces (used by Task 2): `memSigma₃₂ : ℤ_[3] → Prop`; `memEk : ℕ → ℤ_[3] → Prop`; `memE : ℤ_[3] → Prop`; `dimH₃ : Set (ℤ_[3]) → ℝ≥0∞`; `log3two : ℝ≥0∞`; `Ek : ℕ → Set (ℤ_[3])`; `EZ3 : Set (ℤ_[3])`; `RealOmitsTwo : ℝ → Prop`; `memETrunc : ℝ → Prop`; `ETrunc : Set ℝ`; `memEReal : ℝ → Prop`; `EReal : Set ℝ`.

- [ ] **Step 1: Create the file with all definitions**

Create `ErdosTernary/ErdosTernary/LagariasHausdorff.lean` containing exactly:

```lean
/-
  Lagarias's Hausdorff-Dimension Results on Ternary Expansions of Powers of 2.

  Definitions and theorem/conjecture statements from
  J. C. Lagarias, "Ternary expansions of powers of 2",
  J. London Math. Soc. 79 (2009) 562-588.

  This file defines the 3-adic and real exceptional sets and states the
  Hausdorff-dimension results.  It does NOT prove the dimension theorems;
  the OPEN conjectures are explicitly labeled as such.

  Reference numbering (published version):
    Thm 1.3  : dimH E^T(R^+) = log_3 2          (truncated real exceptional set)
    Thm 1.6  : dimH bounds for E^(k)(Z_3), k = 1, 2, 3
    Conj 1.4 : dimH E(R^+) = 0                  (real untruncated; OPEN)
    Conj 1.7 : dimH E(Z_3) = 0                  (3-adic; OPEN)
-/

import ErdosTernary.Narkiewicz
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Topology.Instances.CantorSet
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

open scoped ENNReal NNReal

namespace LagariasHausdorff

/-! ## 3-adic Cantor set and exceptional sets -/

/-- Membership in the 3-adic Cantor set Σ_{3,2} ⊆ ℤ_[3]: every prefix of the
  3-adic expansion omits the digit 2, i.e. for every n the residue of `lam`
  modulo `3^n` equals some `r < 3^n` whose ternary digits are all 0 or 1
  (`Narkiewicz.memCantorNat r`) and whose 3-adic distance from `lam` is at
  most `3^(-n)`.  (Lagarias §1.4, eq. (1.15).) -/
def memSigma₃₂ (lam : ℤ_[3]) : Prop :=
  ∀ n : ℕ, ∃ r : ℕ, r < 3 ^ n ∧ Narkiewicz.memCantorNat r ∧
    ‖lam - (r : ℤ_[3])‖ ≤ (3 : ℝ) ^ (- (n : ℤ))

/-- E^(k)(ℤ₃): at least `k` distinct `m` with `lam·2^m ∈ Σ_{3,2}`.  (Lagarias
  eq. (1.11).) -/
def memEk (k : ℕ) (lam : ℤ_[3]) : Prop :=
  ∃ s : Finset ℕ, s.card = k ∧ ∀ m ∈ s, memSigma₃₂ (lam * (2 : ℤ_[3]) ^ m)

/-- E(ℤ₃) = E*(ℤ₃): infinitely many `m` with `lam·2^m ∈ Σ_{3,2}`.  (Lagarias
  eq. (1.10); the design spec's `E*` coincides with `E`, since "the set of m is
  infinite" is identical to "infinitely many m".) -/
def memE (lam : ℤ_[3]) : Prop :=
  Set.Infinite { m : ℕ | memSigma₃₂ (lam * (2 : ℤ_[3]) ^ m) }

/-- Hausdorff dimension on `ℤ_[3]`.  mathlib's `dimH` requires `[MeasurableSpace
  X] [BorelSpace X]`, which `ℤ_[3]` lacks; the `borel` measurable space is
  provided locally. -/
noncomputable def dimH₃ (s : Set (ℤ_[3])) : ℝ≥0∞ := by
  letI : MeasurableSpace (ℤ_[3]) := borel (ℤ_[3])
  exact dimH s

/-- log₃2 = log 2 / log 3, as an extended nonnegative real. -/
noncomputable def log3two : ℝ≥0∞ := ENNReal.ofReal (Real.log 2 / Real.log 3)

/-- E^(k)(ℤ₃) as a set, as a family over k. -/
noncomputable def Ek (k : ℕ) : Set (ℤ_[3]) := { lam : ℤ_[3] | memEk k lam }

/-- E(ℤ₃) as a set. -/
noncomputable def EZ3 : Set (ℤ_[3]) := { lam : ℤ_[3] | memE lam }

/-! ## Real truncated and untruncated exceptional sets -/

/-- A real `x` omits the digit 2 in its (full) ternary expansion iff its
  integer part has ternary digits all in {0,1} (`Narkiewicz.memCantorNat`) and
  its fractional part has ternary digits all in {0,1}, which holds iff twice
  the fractional part lies in the middle-thirds Cantor set `cantorSet` (whose
  ternary digits are {0,2}; doubling maps digit-{0,1} numbers to digit-{0,2}
  numbers with no carries). -/
def RealOmitsTwo (x : ℝ) : Prop :=
  Narkiewicz.memCantorNat (Nat.floor x) ∧ 2 * (x - (Nat.floor x : ℝ)) ∈ cantorSet

/-- E^T(R⁺): infinitely many `⌊lam·2^n⌋` omit the digit 2.  (Lagarias
  eq. (1.7).) -/
def memETrunc (lam : ℝ) : Prop :=
  Set.Infinite { n : ℕ | Narkiewicz.memCantorNat (Nat.floor (lam * 2 ^ n)) }

/-- E^T(R⁺) as a set. -/
noncomputable def ETrunc : Set ℝ := { lam : ℝ | 0 < lam ∧ memETrunc lam }

/-- E(R⁺): infinitely many full ternary expansions `(lam·2^n)` omit the digit
  2.  (Lagarias eq. (1.8).) -/
def memEReal (lam : ℝ) : Prop :=
  Set.Infinite { n : ℕ | RealOmitsTwo (lam * 2 ^ n) }

/-- E(R⁺) as a set. -/
noncomputable def EReal : Set ℝ := { lam : ℝ | 0 < lam ∧ memEReal lam }

end LagariasHausdorff
```

- [ ] **Step 2: Verify the file compiles**

Run (from `ErdosTernary/`): `lake env lean ErdosTernary/LagariasHausdorff.lean`
Expected: exit code 0, no errors. (All definitions in this block are verified against mathlib v4.12.0.)

- [ ] **Step 3: Commit**

```bash
git add ErdosTernary/ErdosTernary/LagariasHausdorff.lean
git commit -m "feat(erdos-ternary): Lagarias Hausdorff exceptional-set definitions"
```

---

### Task 2: Statements + nesting lemma

**Files:**
- Modify: `ErdosTernary/ErdosTernary/LagariasHausdorff.lean` (append before the final `end LagariasHausdorff`)

**Interfaces:**
- Consumes (from Task 1): `memEk`, `memE`, `dimH₃`, `log3two`, `Ek`, `EZ3`, `ETrunc`, `EReal`.
- Produces: `thm_1_3`, `thm_1_6_i`, `thm_1_6_ii`, `thm_1_6_iii` (all `noncomputable def … : Prop`); `conj_1_4`, `conj_1_7` (labeled OPEN); theorems `memEk_mono`, `E_mono`. Used by Task 3 only for verification.

- [ ] **Step 1: Replace the trailing `end LagariasHausdorff` with the statements + lemma block + `end`**

In `ErdosTernary/ErdosTernary/LagariasHausdorff.lean`, replace the final two lines

```lean
end LagariasHausdorff
```

with

```lean
/-! ## Theorem and conjecture statements (never axioms) -/

/-- Theorem 1.3 (proved in Lagarias): the truncated real exceptional set has
  Hausdorff dimension log₃2. -/
noncomputable def thm_1_3 : Prop := dimH ETrunc = log3two

/-- Theorem 1.6(i) (proved in Lagarias): dimH E^(1)(ℤ₃) = log₃2. -/
noncomputable def thm_1_6_i : Prop := dimH₃ (Ek 1) = log3two

/-- Theorem 1.6(ii) (proved in Lagarias): ½·log₃2 ≤ dimH E^(2)(ℤ₃) ≤ ½. -/
noncomputable def thm_1_6_ii : Prop :=
  ENNReal.ofReal ((1 : ℝ) / 2 * Real.log 2 / Real.log 3) ≤ dimH₃ (Ek 2) ∧
    dimH₃ (Ek 2) ≤ ENNReal.ofReal ((1 : ℝ) / 2)

/-- Theorem 1.6(iii) (proved in Lagarias): ⅙·log₃2 ≤ dimH E^(3)(ℤ₃) ≤
  dimH E^(2)(ℤ₃). -/
noncomputable def thm_1_6_iii : Prop :=
  ENNReal.ofReal ((1 : ℝ) / 6 * Real.log 2 / Real.log 3) ≤ dimH₃ (Ek 3) ∧
    dimH₃ (Ek 3) ≤ dimH₃ (Ek 2)

/-- Conjecture 1.4 (Lagarias Conjecture A): the real untruncated exceptional
  set has Hausdorff dimension zero.  **OPEN** — not proved. -/
noncomputable def conj_1_4 : Prop := dimH EReal = 0

/-- Conjecture 1.7 (Lagarias Conjecture B): the 3-adic exceptional set has
  Hausdorff dimension zero.  **OPEN** — not proved. -/
noncomputable def conj_1_7 : Prop := dimH₃ EZ3 = 0

/-! ## Trivial proved lemmas -/

/-- E^(k+1) ⊆ E^(k): dropping any one of the k+1 witnessing powers of 2 leaves
  k witnesses. -/
theorem memEk_mono {k lam} (h : memEk (k + 1) lam) : memEk k lam := by
  rcases h with ⟨s, hcard, hmem⟩
  have hne : s.Nonempty := by
    exact Finset.card_pos.mp (by omega)
  let e := s.min' hne
  refine ⟨s.erase e, ?_, ?_⟩
  · simp [hcard, Finset.card_erase_of_mem (Finset.min'_mem s hne)]
  · intro m hm
    exact hmem m (Finset.mem_of_mem_erase hm)

/-- E^(k+1)(ℤ₃) ⊆ E^(k)(ℤ₃) as set inclusion. -/
theorem E_mono {k : ℕ} : Ek (k + 1) ⊆ Ek k := by
  intro lam hlam
  exact memEk_mono hlam

end LagariasHausdorff
```

(Note: the file now matches the "Complete Target File Content" block in the plan header exactly.)

- [ ] **Step 2: Verify the full file compiles**

Run (from `ErdosTernary/`): `lake env lean ErdosTernary/LagariasHausdorff.lean`
Expected: exit code 0, no errors. (The six statements and both lemmas are verified against mathlib v4.12.0.)

- [ ] **Step 3: Verify no sorry/axiom/admit**

Run: `rg -n "sorry|axiom|admit" ErdosTernary/ErdosTernary/LagariasHausdorff.lean`
Expected: no matches (exit code 1 from `rg`).

- [ ] **Step 4: Verify conjectures labeled OPEN**

Run: `rg -n "OPEN" ErdosTernary/ErdosTernary/LagariasHausdorff.lean`
Expected: at least 2 matches (in `conj_1_4` and `conj_1_7` docstrings).

- [ ] **Step 5: Commit**

```bash
git add ErdosTernary/ErdosTernary/LagariasHausdorff.lean
git commit -m "feat(erdos-ternary): Lagarias Hausdorff theorem/conjecture statements and nesting lemma"
```

---

### Task 3: Register import + full verification

**Files:**
- Modify: `ErdosTernary/ErdosTernary.lean` (append import line)

**Interfaces:**
- Consumes: module `ErdosTernary.LagariasHausdorff` (Tasks 1+2).
- Produces: project-level registration so `lake build ErdosTernary` picks up the new module.

- [ ] **Step 1: Append the import**

Read `ErdosTernary/ErdosTernary.lean`. It ends with existing import lines such as:

```lean
import ErdosTernary.TernaryExp
import ErdosTernary.PowTwoDigitTwo
import ErdosTernary.Narkiewicz
import ErdosTernary.NarkiewiczBound
import ErdosTernary.Density
import ErdosTernary.MiddleDigits
```

Append the line `import ErdosTernary.LagariasHausdorff` at the end of the import block (keep alphabetical order; it sorts last).

- [ ] **Step 2: Verify module compiles standalone**

Run (from `ErdosTernary/`): `lake env lean ErdosTernary/LagariasHausdorff.lean`
Expected: exit code 0, no errors.

- [ ] **Step 3: Run full project build**

Run (from `ErdosTernary/`): `lake build ErdosTernary`
Expected: "Build completed successfully", exit code 0. (Existing modules unchanged; only the new module + import line are new.)

- [ ] **Step 4: Final zero-sorry sweep across the project**

Run: `rg -n "sorry|axiom|admit" ErdosTernary/ErdosTernary/LagariasHausdorff.lean`
Expected: no matches.

- [ ] **Step 5: Confirm ROADMAP correction already landed (verification only, no edit)**

Run: `rg -n "log₃2 ≈ 0.6309|dim_H = 0 for the full exceptional sets" ROADMAP.md`
Expected: line 17 shows the corrected Lagarias row (proved positive dimensions + open dim_H=0 conjecture). Do **not** edit ROADMAP in this task — commit `61b1571` already applied the correction.

- [ ] **Step 6: Commit**

```bash
git add ErdosTernary/ErdosTernary.lean
git commit -m "feat(erdos-ternary): register Lagarias Hausdorff module import"
```

---

## Self-Review Checklist

- [x] **Spec coverage:** Deliverable 1 (the Lean file) = Tasks 1+2; Deliverable 2 (ROADMAP correction) = already committed `61b1571`, verified in Task 3 Step 5; Deliverable 3 (import registration) = Task 3 Step 1. Verification section of spec (lean exit 0, lake build green, zero sorry, OPEN labels) = Task 1 Step 2, Task 2 Steps 2-4, Task 3 Steps 2-4. Constraints (pinned Lean/mathlib, stdlib-only, one commit per task) enforced in Global Constraints.
- [x] **Placeholder scan:** No "TBD"/"TODO"; every code step contains full compilable Lean text verified against mathlib v4.12.0.
- [x] **Type consistency:** `memEk : ℕ → ℤ_[3] → Prop` used consistently by `memEk_mono`, `Ek`, `thm_1_6_*`. `dimH₃`/`log3two` defined in Task 1, used only in Task 2 statements. `RealOmitsTwo`/`memETrunc`/`memEReal` defined in Task 1, used in Task 2's `thm_1_3`/`conj_1_4`. No cross-task name drift.
- [x] **Faithfulness to Lagarias (published JLMS numbering verified against the journal version; content verified against arXiv:math/0512006v4):** Conj 1.4 = `dimH E(R⁺) = 0` (Conjecture A); Conj 1.7 = `dimH E(Z₃) = 0` (Conjecture B); Thm 1.3 = `dimH E^T(R⁺) = log₃2`; Thm 1.6(i)/(ii)/(iii) on `E^(k)(Z₃)`. The design spec's `E*(ℤ₃)` coincides with `E(ℤ₃)`; documented in `memE` docstring.

## Execution Handoff

Plan complete and saved to `docs/superpowers/plans/2026-08-20-lagarias-hausdorff.md`. Two execution options:

**1. Subagent-Driven (recommended)** — I dispatch a fresh subagent per task, review between tasks, fast iteration.

**2. Inline Execution** — execute tasks in this session with checkpoints for review.

Which approach?