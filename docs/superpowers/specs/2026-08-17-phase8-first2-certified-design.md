# Phase 8 M1: Certified First-2-Position Records f(n) — Design

**Date:** 2026-08-17
**Status:** Approved design (brainstorming), to be implemented via writing-plans.

## Goal

Produce the first certified dataset of `f(n)` — the number of leading (most-significant) ternary digits of `2ⁿ` that are ≠ 2 before the first digit 2 — for n up to 10⁹, together with record-holder statistics and the ratio `f(n)/L(n)`. Every reported value must be **mathematically certified** (interval enclosures, no "200 digits seems enough" hand-waving).

## Definitions

- α = log₃2 = ln 2 / ln 3 ≈ 0.6309297536
- `L(n) = ⌊n·α⌋ + 1` — number of ternary digits of 2ⁿ
- `yₙ = 2ⁿ / 3^⌊nα⌋ ∈ [1, 3)` — the mantissa of 2ⁿ. The leading digits of 2ⁿ equal the digits of yₙ (integer digit `d₀ ∈ {1,2}` then fractional digits).
- `f(n) = max L such that the first L leading digits of 2ⁿ are all ≠ 2` — equivalently the number of leading digits in `{0,1}` before the first 2. `f(n) = 0` ⟺ the leading digit is 2. Note `f(n) ≥ L ⟺ A_L` from the Phase 7 event test.

## Core Algorithm: Certified Mantissa Stream

The mantissa evolves by the exact recurrence

```
yₙ₊₁ = 2·yₙ / 3^δₙ,   δₙ = 1 ⟺ 2·yₙ ≥ 3  (i.e. yₙ ≥ 3/2)
```

### Interval invariant

Represent the mantissa at precision `p` as `D = d₀.d₁…d_p` (ternary digits, `d₀ ∈ {1,2}`), with the certified enclosure

```
yₙ ∈ [D, D + 3⁻ᵖ]
```

The enclosure width is exactly `3⁻ᵖ` at every step because it is a re-truncation of the true value, never a propagated error bound — errors do not accumulate.

### Certified δ decision (cutoff is 3/2, not 2/3)

After doubling, `2·yₙ ∈ [2D, 2D + 2·3⁻ᵖ]`. Compare against 3:

- `2D ≥ 3` → δₙ = 1 certified; set `yₙ₊₁ = 2yₙ/3`, re-truncate to `p` digits (width back to `3⁻ᵖ`)
- `2D + 2·3⁻ᵖ < 3` → δₙ = 0 certified; `yₙ₊₁ = 2yₙ`, re-truncate
- else → **ambiguity**: `3/2 ∈ [yₙ⁻, yₙ⁺]` → escalate (below)

### Certified f(n)

Report `f(n) = r` only when the enclosures `D` and `D + 3⁻ᵖ` agree on the first `r+1` digits — i.e. the 2-free prefix AND the terminating 2 are both certified, so the reported value cannot be a truncation artifact.

### Escalation path (increase precision)

On any ambiguity (δ or digit), resolve that single n by an **independent exact** computation of the mantissa:

```
yₙ = 3^{frac(n·α)},   frac(n·α) = n·α mod 1
```

computed with certified interval arithmetic:
- `α` computed once to certified bounds (interval [α⁻, α⁺] via ln2/ln3 enclosures)
- `n·α` as interval → if it straddles an integer, widen precision until not
- `3^frac` via interval exponentiation (Taylor series `e^t` with verified remainder bound, then `3^t = e^{t·ln3}`)

This resolves δₙ and f(n) exactly, re-seeds the stream at `n+1` with higher precision `p′`, and continues. Precision schedule: start at `p = 200`; on escalation, set `p′ = 4·p` (and start a fresh certified-α computation at the new width). Expected to trigger ~never at p ≈ 200 (P(ambiguity at step n) ≈ 3⁻ᵖ; expected count over 10⁹ ≈ 10⁹·3⁻²⁰⁰), but required for mathematical safety.

Every record-holder is also re-verified through this same independent route.

## Outputs

### Records CSV (`verify_middle/first2_records.csv`)

Columns: `n, f(n), L(n), f(n)/L(n), prefix, mantissa_precision, record_number, gap_from_previous_record`

- `prefix` = the certified 2-free leading digit string (length f(n))
- `mantissa_precision` = p in effect when the record was found
- `record_number` = sequential index of the record
- `gap_from_previous_record` = n − previous record's n

### Record summary (stdout / `FINDINGS`)

- record table (min, max, growth)
- ratio analysis: is `f(n)/L(n)` decaying cleanly, structured, or bounded? (records suggest f ≈ log_{3/2} n ≈ 51 at n=10⁹ vs L ≈ 6.3×10⁸ → ratio ≈ 10⁻⁷)
- growth-rate fit for the Phase 8 conjecture

## Scale & Performance

- N = 10⁹ (ROADMAP target), single streaming pass
- O(p) per n, p ≈ 200 digits → runs in minutes single-threaded (no log needed in the main loop; α only enters the escalation path)
- Records expected around f ≈ 50 (from P(A_L)·N ≈ 1 at (2/3)^L·10⁹), comfortably within p

## Validation Layers

1. **Mantissa stream vs exact digits:** for n ≤ 10⁵, compare the mantissa-derived f(n) against f(n) computed from the full digit stream (`Stream::digits` from Task 1 of the Phase 7 plan).
2. **Distribution cross-check:** `P(f ≥ L)` from the mantissa stream must match the `P(A_L)` marginals in `events_m1.csv` (Phase 7).
3. **Independent certification:** a sample of n (including all record-holders) re-verified via the escalation-path computation (certified `3^{frac(n·α)}`).

## Tech Stack

- Extend the existing `verify_middle` Rust crate (mirrors Phase 7 conventions)
- Rust, edition 2021, `num-bigint` only (already a dependency); no new deps
- TDD: unit tests for the mantissa stream and f(n) vs known values, then CLI `--first2` mode

## Out of Scope (later)

- Phase 8 gap-structure deep-dive / conjectured theorem `f(n) ≤ C·log₃ n`
- Phase 9 two-sided search (uses these records)
- M3 Lean formalization of the transducer