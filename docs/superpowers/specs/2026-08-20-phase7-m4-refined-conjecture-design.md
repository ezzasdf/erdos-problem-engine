# Spec: Phase 7 M4 — Refined Conjecture Document

Date: 2026-08-20
Status: Approved (design), pending implementation
Part of: ROADMAP Phase 7 (middle-digit attack), milestone M4

## Objective

Produce a consolidated, precisely-stated **refined conjecture** document for the
Erdős ternary conjecture (no `2ⁿ` whose ternary expansion contains only digits `{0,1}`),
unifying the draft conjectures already scattered across Phase 7/8 findings:

- **M1-C1** (middle-window lower frequency bound, from `verify_middle/FINDINGS.md`)
- **P8-C1** (first-2-position linear bound, from `verify_middle/PHASE8_FINDINGS.md`)
- **M1-C2** (two-sided independence, from `verify_middle/FINDINGS.md`)

The document must be unambiguous about the **epistemic status** of every claim:
proved results, empirical measurements, and conjectural extrapolations are labeled
separately. The conjectured bounds (`n > 1000` / constant `0.246`; `f(n) ≤ 3.5·log₃ n`)
are *conjectural extrapolations from the existing datasets*, **not** proved theorems.

The deliverable is a research document plus a small verification script that re-derives
every stated constant from the existing data (`results_m1.csv`, `first2_records.csv`).
No new heavy computation — K=40 continues running in the background.

## Definitions

- `L(n) = ⌊n·log₃2⌋ + 1` — number of ternary digits of `2ⁿ`.
- `W = ⌊L/3⌋` — window length. Windows (least-significant-first digit positions):
  trailing `[0, W)`, middle `[W, ⌊2L/3⌋)`, leading `[⌊2L/3⌋, L)`.
- `f(n)` — position of the first digit 2 in `2ⁿ` counting from the most significant
  digit (0-indexed), or `L(n)` if `2ⁿ` has no digit 2.
- Datasets (both already exist, verified):
  - `verify_middle/results_m1.csv` — 999,992 rows, n = 9…10⁶, window statistics.
  - `verify_middle/first2_records.csv` — 19 record-holders, n = 0…10⁹,
    columns `n,f,L,ratio,prefix,mantissa_precision,record_number,gap_from_previous_record`.

## Deliverable 1 — `verify_middle/REFINED_CONJECTURES.md`

A self-contained research document with these sections:

### 1. Status table

Every claim in the document categorized as one of:

| Status | Meaning |
|---|---|
| **Proved** | Proven result with a rigorous argument (e.g. the exact `P(f ≥ L)` law and the counting-identity upper bounds from Phase 8 findings). |
| **Empirical** | Measured exactly over the stated dataset range (e.g. `results_m1.csv`, `first2_records.csv`). |
| **Conjectural** | Extrapolated beyond the measured range; not proved; falsifiable by a single counterexample. |

### 2. The conjecture statement

The core conjecture, stated precisely with exact quantifiers:

> **M4-C (middle-window digit-2 lower bound; conjectural).**
> For every `n > 8`, the middle third `[⌊L/3⌋, ⌊2L/3⌋)` of the ternary expansion of
> `2ⁿ` contains a digit 2; more precisely, the digit-2 frequency in that window is
> `≥ 0.246` for `n > 1000`.

Immediately following the statement, a boxed caveat in the exact wording approved in
review:

> The threshold `n > 1000` and the constant `0.246` are **conjectural extrapolations**
> from the existing dataset (`n ≤ 10⁶`, `verify_middle/results_m1.csv`). They are
> **not proved results.** The measured facts are: the only n with a 2-free middle
> window over `9 ≤ n ≤ 10⁶` are `n ∈ {14, 24, 76}`, and the minimum middle-window
> digit-2 frequency over `n > 1000`, `n ≤ 10⁶` is `0.246192893` at `n = 1874`.

### 3. Supporting conjectures

- **M4-C2 (two-sided independence; empirical + conjectural).** The digit-2
  frequencies of the trailing, middle and leading thirds of `2ⁿ` are statistically
  independent across `n` (Spearman |ρ| < 0.005 over `n ≤ 10⁶`), and boundary digits
  pair near-uniformly. State explicitly: measured (empirical) over `n ≤ 10⁶`;
  the extrapolation to all `n` is conjectural.
- **M4-C3 (first-2-position linear bound; conjectural).** For every `n ≥ 1`,
  `f(n) ≤ 3.5·log₃ n`, i.e. `2ⁿ` has a digit 2 among its first `⌈3.5·log₃ n⌉` ternary
  digits. Stated throughout as *a conjecture supported by all tested data
  (`n ≤ 10⁹`), not a theorem*. The sharpest tested point is `n = 121` with
  `f(121)/log₃(121) ≈ 3.437` (2% margin below 3.5); the ratio decays toward ≈ 2.8
  for large `n`. The measured records obey `f ≈ log_{3/2} n` (least-squares
  `f ≈ 1.044·log_{3/2} n + 0.60`).

### 4. Evidence tables

Tables re-derived from the datasets by the verification script (see Deliverable 2),
each captioned with its epistemic status (all "Empirical — measured over `n ≤ 10⁶`"
or "`n ≤ 10⁹`", and clearly marked not-proved):

- Middle-window floor: min digit-2 frequency, `n > 1000`, argmin `n`.
- Set of 2-free middle windows over `n ≤ 10⁶`: `{14, 24, 76}`.
- Longest 2-free run inside the middle window: 61 (at `n = 385178`).
- First-2 record table (all 19 rows from `first2_records.csv`).
- `f/log₃ n` ratio over records; max `3.437` at `n = 121`.
- `log_{3/2}` growth fit over the 19 records.

### 5. Falsification criteria

Operational definition of what would refute each conjectural claim:

- **M4-C:** any `n > 76` whose middle window contains no digit 2; or any `n > 1000`
  with middle-window digit-2 frequency `< 0.246`.
- **M4-C2:** a statistically significant dependence between any pair of window
  frequencies over a tested range.
- **M4-C3:** any `n` with `f(n) > 3.5·log₃ n`.

A single counterexample at any tested or future `n` refutes the conjectural claim.
Proved results (the `P(f ≥ L)` law) are immune.

### 6. Relation to Erdős / Phase 9

- The middle-window bound is the Erdős conjecture restricted to the middle block:
  a proof of M4-C would prove the full conjecture for all `n > 8`.
- The two-sided search (Phase 9) treats the leading and trailing blocks as
  independent inputs; M4-C2 justifies that modelling over the measured range.
- The first-2 bound, if proved, would combine with Saye's trailing-digit pruning
  to certify a two-sided search far beyond `5.9×10²¹`.

## Deliverable 2 — `verify_middle/refine_conjectures.py`

Stdlib-only Python (matching `verify_middle/p_cf_log32.py` style). Reads
`results_m1.csv` and `first2_records.csv`, recomputes every constant below, and prints
a verification report:

1. Middle-window floor and argmin over `n > 1000`, `n ≤ 10⁶` → must equal
   `0.24619289340101522` at `n = 1874`.
2. Set of n with 2-free middle window → must equal `{14, 24, 76}`.
3. Longest 2-free run in the middle window → must equal `61` at `n = 385178`.
4. `max f/log₃ n` over the 19 records → must equal `3.4367…` (at `n = 121`).
5. Least-squares fit `f ≈ a·log_{3/2} n + b` → must reproduce `a ≈ 1.044, b ≈ 0.60`.
6. Cross-checks on the record table (`ratio = f/L`, record monotonicity of `f`,
   `gap = n - prev_n`).

Exit code 0 on success; each check prints PASS/FAIL. The report is embedded into
`REFINED_CONJECTURES.md` §4 (the "Evidence" tables are generated by running the
script, so doc numbers and script numbers cannot drift).

## Deliverable 3 — ROADMAP update

Flip the M4 checkbox in `ROADMAP.md` from `[ ]` to `[x]` and update the summary line
to reference `verify_middle/REFINED_CONJECTURES.md`.

## Verification

- `python3 verify_middle/refine_conjectures.py` — all checks PASS, constants match.
- `REFINED_CONJECTURES.md` renders with correct epistemic labels; no phrase claims
  `f(n) ≤ 3.5·log₃ n` or the `0.246` bound as proved.
- `ROADMAP.md` M4 checkbox flipped.
- No new computation beyond reading the two existing CSVs.

## Non-goals

- No proof attempts of M4-C / M4-C3 (out of scope; Phase 9 / P8-C1 remain open).
- No extension of the datasets (no new heavy runs; K=40 continues in background).
- No Lean formalization of the conjecture.