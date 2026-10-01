# Spec: Action Item 7 — Lagarias Hausdorff-Dimension Formalization (Definitions + Statements)

Date: 2026-08-20
Status: Drafted — design approved, pending user approval to begin implementation
Part of: ROADMAP Action Item 7 ("Formalize Lagarias's Hausdorff dimension result")

## Objective

Formalize in Lean the definitions and theorem/conjecture statements of
J. C. Lagarias, *Ternary expansions of powers of 2*, J. London Math. Soc.
79 (2009) 562–588. The formalization **does not prove** the dimension
theorems; it precisely defines the exceptional sets and states the results,
with every conjecture explicitly labeled as open.

## Critical correction to ROADMAP

The ROADMAP (line 17) currently reads: *"Lagarias 2009 … proved Hausdorff
dim of exceptional set is 0"*. This is **wrong**:

- **Proved (positive dimension):** `dim_H E^T(ℝ⁺) = log₃2 ≈ 0.63092`
  (Thm 1.3); `dim_H E^(1)(ℤ₃) = log₃2` (Thm 1.6(i));
  `½·log₃2 ≤ dim_H E^(2)(ℤ₃) ≤ ½` (Thm 1.6(ii));
  `⅙·log₃2 ≤ dim_H E^(3)(ℤ₃) ≤ dim_H E^(2)(ℤ₃)` (Thm 1.6(iii)).
- **`dim_H = 0` is a conjecture** (Lagarias's Conjectures 1.4, 1.7) — an
  open problem. It cannot be formalized as a theorem.

The implementation must correct the ROADMAP.

## Definitions to formalize (all with docstrings citing Lagarias's numbering)

1. **3-adic Cantor set** `Σ_{3,2} ⊆ ℤ_[3]`: elements whose 3-adic expansion
   uses only digits `{0,1}` (omits 2). mathlib provides `ℤ_[p]` (PadicInt),
   `dimH` (Hausdorff dimension), `padicValNat`, and the real ternary Cantor
   set — but not the 3-adic Cantor set nor any dimension theorem. Model
   digit-avoidance via the mod-`3ⁿ` residue condition (residue is a sum of
   distinct powers of 3) for every n.
2. **3-adic exceptional sets**: `E^(k)(ℤ₃) = {λ ∈ ℤ₃ : at least k distinct
   m with λ·2^m ∈ Σ_{3,2}}`; `E(ℤ₃) = {λ : infinitely many m}`;
   `E*(ℤ₃) = {λ : the set of m with λ·2^m ∈ Σ_{3,2} is infinite}` (complete).
3. **Real truncated exceptional set** `E^T(ℝ⁺) = {λ > 0 : infinitely many
   ⌊λ·2ⁿ⌋ have ternary expansion omitting digit 2}` (truncated real model).

## Statements (declared as `def … : Prop`, never as axioms/theorems)

Zero `sorry` / `axiom` / `admit` constraint preserved (matches project norm).

| Label | Statement | Status |
|---|---|---|
| Thm 1.3 | `dimH E^T(ℝ⁺) = log₃2` | proved in Lagarias |
| Thm 1.6(i) | `dimH E^(1)(ℤ₃) = log₃2` | proved in Lagarias |
| Thm 1.6(ii) | `½·log₃2 ≤ dimH E^(2)(ℤ₃) ≤ ½` | proved in Lagarias |
| Thm 1.6(iii) | `⅙·log₃2 ≤ dimH E^(3)(ℤ₃) ≤ dimH E^(2)(ℤ₃)` | proved in Lagarias |
| Conj 1.4 | `dimH E(ℝ⁺) = 0` | **OPEN** |
| Conj 1.7 | `dimH E*(ℤ₃) = 0` | **OPEN** |

Conjecture statements carry docstrings explicitly marking them open and
unproved. Trivial proved lemmas only where cheap (e.g. nesting
`E^(k+1) ⊆ E^(k)`), each genuinely proved.

## Deliverables

1. `ErdosTernary/ErdosTernary/LagariasHausdorff.lean` — all definitions and
   statements above.
2. ROADMAP correction: line 17 and action-item-7 row fixed to distinguish
   proved positive-dimension theorems from the open dim_H = 0 conjectures.
3. Import registration appended to `ErdosTernary/ErdosTernary.lean`.

## Verification

- `lake env lean ErdosTernary/LagariasHausdorff.lean` — exit 0, no warnings.
- `lake build ErdosTernary` — green.
- Zero `sorry` / `axiom` / `admit` in the new file (grep).
- Conjecture statements labeled open (grep for "OPEN" / "open").

## Constraints

- Lean `v4.12.0` + mathlib `v4.12.0` (pinned, project-wide).
- stdlib/mathlib only, no third-party deps.
- One commit per task, conventional commit style, plan-driven execution
  with per-task review.

## Non-goals (this milestone)

- Proving any dimension theorem (positive or zero). Requires
  self-similar/moran dimension theory not in mathlib — a later milestone.
- The real untruncated exceptional set `E(ℝ⁺)` definition beyond the
  Conj 1.4 statement (kept as a Prop statement only).
- New computation; the K=40 record run continues in the background.

## References

- Lagarias, *Ternary expansions of powers of 2*, JLMS 79 (2009) 562–588,
  Theorems 1.3, 1.6, Conjectures 1.4, 1.7.
- mathlib `Mathlib/NumberTheory/Padics/PadicIntegers.lean` (`ℤ_[p]`),
  `Mathlib/Topology/MetricSpace/HausdorffDimension.lean` (`dimH`),
  `Mathlib/Topology/Instances/CantorSet.lean` (real Cantor set).