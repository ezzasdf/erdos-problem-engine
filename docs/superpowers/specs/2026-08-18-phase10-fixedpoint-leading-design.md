# Phase 10 Design — u256 Fixed-Point Leading Check

Date: 2026-08-18
Status: Approved (design v2)
Predecessor: `docs/superpowers/specs/2026-08-17-two-sided-search-design.md` (Phase 9)
Phase 9 engine: `verify_erdos_rs/src/leading.rs`, `src/two_sided.rs`, `src/saye.rs`

## 1. Goal

Speed up the certified leading-digit check `leading_digits_have_two(n, k_prime)` so that the two-sided engine can reach K=40 and K=42 as routine background records on this 4-core machine. Today the per-candidate cost is ~0.43 ms, dominated by the BigInt `certified_pow3_interval` at ~3^138 scale (~220-bit intermediates). Target: ~10–30× faster via a u256 fixed-point fast path.

Milestones:
- **K=40 record** (n ≤ 2·3^39 = 8.1×10¹⁸), ~3–5 h background.
- **K=42 record** (n ≤ 2·3^41 = 7.3×10¹⁹), ~2–4 days background.
- Non-goal: K=46 (beat Saye 5.9×10²¹). The Saye traversal (≈256 ns/node × 2^K) is the wall there and is out of scope for this phase.

## 2. Correctness invariant: optimization, not replacement

`leading_digits_have_two` keeps its exact public contract and semantics:

- `Some(true)`: a 2 is **certified** in the first `k_prime` ternary digits of `3^{frac(n·α)}`.
- `Some(false)`: all first `k_prime` digits are **certified** ≠ 2.
- `None`: undecidable at the highest tried precision (caller treats as deep).

Dispatch:
```
u256 fast path
  ├── certified → return Some(result)
  └── ambiguous → existing BigInt certified path (identical logic to today)
```

The u256 path never emits an answer it could not certify. An ambiguous/undecidable u256 case always escalates to the proof-grade BigInt path. **The returned `Option<bool>` for every n is bit-identical to the current engine's**, enforced by an exhaustive differential test (Section 6).

## 3. Architecture

New module `verify_erdos_rs/src/fixedpoint.rs`:

- **`U256`** — `[u128; 2]`, with the ops used by the fast path:
  - `add`, `sub`, `shl`, `shr` (exact)
  - `mul` (full 512-bit product as `(hi, lo)`, truncated with explicit round-down / round-up variants)
  - `mul_u64` (u256 × u64, truncated, round-down / round-up variants)
  - `div` by `U256` and by `u64` (round-down / round-up variants)
  - `from_bigint(BigInt, round_down|round_up)` for converting the cached certified constants
  - `to_ternary_digits(len) -> Vec<u8>` (repeated div-by-3; ≤ 3^P has ~P·log₂3 ≈ 190 bits → ≤ 190 digits)
- **Cached n-independent constants at two scales** (Section 4), converted once from the existing certified BigInt `certified_alpha` / `certified_ln(3, …)`, each computed at guard precision `P+g` / `P_t+g` and truncated into `U256`:
  - `α_lo`, `α_hi` (`U256` at scale `S = 3^P`), plus their measured gap `E_α = α_hi − α_lo` (ulp count)
  - `ln3_lo`, `ln3_hi` (`U256` at scale `S_t = 3^P_t`), plus measured `E_l3`
  - `S = 3^P`, `S_t = 3^P_t` as `U256`; `3^(P−P_t)`, `3^(P_t−70)` as `u128` (both ≤ 3^40 ≈ 1.2×10¹⁹, fits u64)
- **`error_budget(P, P_t, n_max) -> u128`** — the explicit total interval width in ulp at scale 3^P (Section 4).
- **`verify_precision(P, P_t, n_max) -> bool`** — asserts `error_budget < 3^(P−70)` (Section 4).
- **`leading_digits_have_two_fp(n, k_prime) -> Option<Option<bool>>`** — the fast path: `Some(b)` certified, `None` = ambiguous (caller falls back to BigInt).

`leading.rs`:
- `leading_digits_have_two` becomes the dispatcher: call the fp path; on `None`, run the existing BigInt loop unchanged.
- The BigInt path is untouched (it remains the ground-truth fallback and the reference for differential tests).
- New debug flag `--two-sided-bigint` forces the BigInt path end-to-end (for CLI differential runs).
- Startup (and a test) calls `verify_precision(P, n_max)`; if it fails, raise P (up to u256 capacity) or disable the fp path entirely (engine then runs pure BigInt, unchanged behavior).

## 4. Precision model: scales are derived, not hard-coded

The fast path uses **two** fixed ternary scales, both derived by `verify_precision(P, P_t, n_max, k_prime)`:

- **Product scale `S = 3^P`** — holds `n·α`, `flo`/`fhi`, and the fractional-part interval `[a,b]`. P is bracketed by:
  - *Product-fit (upper bound):* `n_max · 3^P < 2^256` so `n·α` fits `U256`. With `n_max = 2·3^K` this caps P ≈ (256 − log₂n_max)/log₂3 ≈ 122 at K=40, ≈ 120 at K=42.
  - *Resolution (lower bound):* `error_budget(P, P_t, n_max) < 3^(P − k_prime)` (k_prime = 70), i.e. the certified interval, scaled to 3^k_prime, is guaranteed narrower than the gap between distinct first-k_prime-digit prefixes.
- **Taylor scale `S_t = 3^P_t`** — the pow3 series runs here because its recurrence multiplies two ~P_t-digit values (`3^(2·P_t·log₂3) < 2^256` → `P_t ≤ 80`), which is impossible at scale 3^P. P_t is bracketed by:
  - *Product-fit:* `2·P_t·log₂3 + 2 < 256` → `P_t ≤ 80`.
  - *Resolution:* series truncation + roundings at `S_t` must leave total width `< 3^(P_t − 70)`, i.e. `P_t ≥ 76` (each Taylor term adds ~1 ulp; ~25 terms + tail ≪ 3^6).

The two scales are glued by one truncating division: `[a,b]` at `3^P` is divided by `3^(P−P_t)` (a `u64`, ≤ 3^40) with round-down/up into `[a_t, b_t]` at `S_t`.

**Constants are computed at guard precision `P+g` / `P_t+g` (g ≈ 12) with the existing BigInt `certified_alpha` / `certified_ln(3, …)`, then truncated into `U256` (lo round-down, hi round-up).** This is what keeps `E_α` ≈ 2–3 ulp: a raw `certified_alpha(P)` interval is ~P·1.585 ulp wide (one ulp per ln-Taylor term, ~187 terms at P=118) — n·E_α with that width alone would exceed the whole 70-digit budget at K=42. `error_budget` measures `E_α`/`E_l3` from the *truncated* constants, so the margin is real, not assumed.

`verify_precision(P, P_t, n_max, k_prime)` checks both constraints for a target K, using the actual per-op constants, over a candidate grid (e.g. P ∈ {112, 118, 124, 130, 136, 142, 148, 154, 160}, P_t ∈ {76, 78, 80}). The smallest passing pair is used; if none passes, the fp path is disabled for that K (pure BigInt, unchanged). The actual (P, P_t) is reported in benchmark output and findings ("peak precision").

Two requirements underlie the budget, both enforced by construction and tests:

**(a) Soundness** — the u256 interval always contains the true value: every op widens correctly (round-down for the low bound, round-up for the high bound), and the cached α/ln3 constants are truncated from the certified BigInt bounds (lo round-down, hi round-up). Verified by the containment property test (Section 6).

**(b) Sufficiency** — the prefix-span test is decisive for the first k_prime digits: total width (table below) < 3^(P − k_prime).

The error budget is composed of the *actual* per-op constants. All values are ulp at their own scale; Taylor-side terms are re-expressed at `3^P` via the factor `3^(P_t − P)`:

| term | ulp contribution | at scale |
|---|---|---|
| α-interval (truncated from P+g) | `n_max · E_α`, `E_α = α_hi − α_lo` ≈ 2–3 | 3^P |
| n·α product truncation | ≤ 2 (round-down lo, round-up hi) | 3^P |
| flo/fhi divisions by S | ≤ 2 | 3^P |
| a/b reconstruction | ≤ 2 | 3^P |
| frac truncation to S_t | ≤ P−P_t + 2, re-expressed as `3^(P_t−P)·(P−P_t+2)` | 3^P |
| Taylor terms (k_terms ≈ 25) | k_terms, re-expressed as `3^(P_t−P)·k_terms` | 3^P |
| Taylor tail | explicit bound (same formula as the BigInt path, recomputed in u256) | 3^P |
| scale-down by 3^(P_t−k_prime) | ≤ 2 | 3^P |

With P=118, P_t=78: the Taylor-side terms are ~`3^-40 · 30 ≈ 3^-37` (negligible); the dominant term is `n_max·E_α ≈ 3^41.6 · 3 ≈ 3^42.6` ulp (K=42) → total width ≈ 3^42.6 ulp = 3^-75.4 absolute, comfortably under 3^-70 (~5.4 digits margin). `verify_precision` computes the exact value from the real constants (no hand-tuning), parameterized by `n_max = 2·3^K` for the target K, so adequacy is provable per milestone.

## 5. Fast path data flow (per candidate n)

1. `nlo = n·α_lo` round-down, `nhi = n·α_hi` round-up (U256 at scale `3^P`).
2. `flo = nlo / S`, `fhi = nhi / S` (round-down / round-up). If `flo != fhi` → ambiguous (fallback).
3. `a = nlo − flo·S`, `b = nhi − fhi·S` (the fractional-part interval at scale `3^P`).
4. Scale down to the Taylor scale: `a_t = a / 3^(P−P_t)` round-down, `b_t = (b + 3^(P−P_t) − 1) / 3^(P−P_t)` round-up (U256 / u64).
5. `(ylo, yhi) = certified_pow3_interval_256(a_t, b_t, P_t, ln3_lo, ln3_hi)` — Taylor series in U256 at scale `S_t` with round-down/up terms and the explicit tail bound.
6. Scale to 3^k_prime: `ylo_k = ylo / 3^(P_t−k_prime)` round-down, `yhi_k = (yhi + 3^(P_t−k_prime) − 1) / 3^(P_t−k_prime)` round-up.
7. `r = to_ternary_digits(ylo_k, k_prime+GUARDS)`, `r_hi = to_ternary_digits(yhi_k, k_prime+GUARDS)`.
8. **Prefix-span test**: if `r[..k_prime] == r_hi[..k_prime]` → `Some(prefix contains 2)`; else ambiguous → fallback.

The prefix-span test is identical in meaning to the Phase 9 fix (digits of both endpoints; lexicographic monotonicity certifies the whole span shares the common prefix). All digit logic and the engine's k_prime = 70 semantics are unchanged.

## 6. Testing and benchmark hard gate

The following must all pass before any K=40 run is launched. Order is enforced.

1. **Unit tests**: U256 arithmetic (rounding modes, overflow), `to_ternary_digits`, `error_budget`/`verify_precision` for the target K.
2. **Containment property test**: for random `(n, k_prime)`, the u256 interval always contains the BigInt interval.
3. **Differential test, scale 10⁵–10⁶ candidates**: random + adversarial n (near 3^m, near digit boundaries, small n, huge u128 n); assert `leading_digits_have_two_fp` fallback-or-match equals the BigInt result; **result mismatches must be zero**.
4. **Existing suites stay green**: `cargo test` (brute-force n ≤ 10⁴, record, two-sided deep-set, saye, ternary_mod). The brute-force and record tests must still pass with the fp path active.
5. **Two-sided engine parity**: K=25/30/35 counts and `deep={0,2,8}` identical with and without `--two-sided-bigint`.
6. **Benchmark gate** (before K=40):
   - BigInt checker candidates/sec (baseline)
   - u256 checker candidates/sec
   - total candidates/sec; u256-only time; BigInt fallback count and %; ambiguous cases; peak precision (P used)
   - speedup factor (report even if 2×; still useful before committing days of compute)
   - Gate: only proceed to K=40/K=42 if speedup is real and mismatches = 0.

## 7. Integration and docs

- `leading_digits_have_two` dispatches fp-then-BigInt; two-sided engine and CLI unchanged except `--two-sided-bigint`.
- Spec → this file. Plan → `docs/superpowers/plans/2026-08-18-phase10-fixedpoint-leading.md` (via writing-plans).
- ROADMAP: Phase 10 section with milestone plan and K=39 status.
- Findings → `verify_erdos_rs/PHASE10_FINDINGS.md` (K=40/K=42 records + benchmark table + peak precision).
- Commits: one per logical change (test-first), benchmark gate results recorded before K=40.

## 8. Risks

- u256 at 3^P (~190 bits) leaves < 70 bits of headroom; error-budget verification (two-scale, measured constants) is the mitigation and is mandatory.
- The guard-precision trick (constants at `P+g`, truncated) is what keeps `E_α` ≈ 2–3 ulp; if the measured `E_α` is unexpectedly large, `verify_precision` fails and the fp path is disabled — never silently wrong.
- Taylor tail in u256 must match the BigInt tail's rigor; reuse the same formula and test containment.
- Fallback rate rising at large n (n·E_α term grows with K): `verify_precision` per-K catches it; worst case the fp path degrades to pure BigInt (no loss of correctness).
- False confidence from microbenchmarks: the gate's differential test is on real candidate streams from `for_each_candidate`, not synthetic inputs.