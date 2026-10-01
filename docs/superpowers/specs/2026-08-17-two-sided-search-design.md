# Two-Sided Search Engine — Phase 9 Design

Date: 2026-08-17
Status: Approved
Related: ROADMAP Phase 9; Phase 8 findings (`verify_middle/PHASE8_FINDINGS.md`)

## Problem and Goal

Saye (2022) verified the Erdős ternary conjecture (only `2⁰, 2², 2⁸` are 2-free in base 3) for `n ≤ 5.9×10²¹` using trailing-digit (3-adic) pruning alone. This project's Phase 1 reimplemented Saye's tree (`verify_erdos_rs`, K ≤ 38, coverage `n ≤ 9×10¹⁷`), but large candidates are only checked for 54 trailing digits — the verification is *incomplete* beyond `n ≤ 10⁶`.

**Goal:** build a two-sided pruning engine — Saye's trailing-digit tree **plus** a certified leading-digit check from Phase 8 — that delivers a **complete verification** of `n ≤ 2·3^{K−1}` for the largest feasible K, targeting and then beating Saye's `5.9×10²¹` (K = 46, 47).

## The verification argument (completeness)

For any `n ≤ B = 2·3^{K−1}`:

1. If `2ⁿ` has a 2 among its **trailing 54** ternary digits → verified (Saye tree prunes these; only the 2-free-trailing candidates survive to the candidate set).
2. Otherwise `n` is a Saye candidate. Compute the **first K′ leading digits** of `2ⁿ = 3^{frac(n·log₃2)}` via certified interval arithmetic. If a 2 is certified there → verified.
3. Candidates that are 2-free in *both* blocks are **deep**. If the deep set is exactly `{0, 2, 8}` and small n (where the two blocks would overlap, `n ≲ (K′+54)/log₃2`) are brute-forced, then every `n ≤ B` is verified.

Deep `⊇ {0,2,8}` always (those are genuinely 2-free). Saye's 5.9×10²¹ result independently certifies that no middle-only candidate exists in range, so deep == `{0,2,8}` at K ≤ 45 is both the validation target and the completeness certificate.

## Key constraints discovered during exploration

- **u64 overflow:** candidates `j ≤ 2·3^{K−1}` exceed u64 at K ≥ 39 (u64 max ≈ 1.8×10¹⁹). `saye.rs` currently stores `Vec<u64>` and casts `j as u64`. Must become `u128`.
- **`escalate`/`L(n)` are u64-bound** in `verify_middle`; the leading check needs only the first K′ digits for `n: u128`, so a trimmed port lives in `verify_erdos_rs` (not a cross-crate lib refactor).
- **Candidate counts:** ~3× per K level (K=38 → 209.3M; K=46 → ~1.4×10¹²). The engine must **stream** candidates through the leading check (never materialize `Vec<u128>` of all candidates) — reuse the existing "collect branches → rayon over branches → recurse" structure.
- Both crates use `num-bigint 0.4`. `verify_erdos_rs` already has `rayon`, `num_cpus`, `ctrlc`, checkpoint/resume.

## Design decisions

| Decision | Choice | Why |
|---|---|---|
| Location | extend `verify_erdos_rs` (new modules `leading.rs`, `two_sided.rs`) | the verification crate; has rayon/checkpoint/CLI/tests |
| Leading math | port Phase 8 `certified.rs` interval machinery (`certified_ln/alpha/pow3_interval`, `digits_of`, `add_one_msb`) | self-contained BigInt code, no `Mantissa` dependency besides `GUARDS` (copy const = 20) |
| Candidate type | `u128` throughout (`saye.rs`, checkpoint, `u_k`) | required for K ≥ 39 |
| Leading check | `leading_digits_have_two(n: u128, k_prime: usize) -> Option<bool>` | Some(true) certified 2; Some(false) certified all ≠ 2; None ambiguous → deep |
| Leading precision | `k_prime = 70` default (configurable) | survival `(2/3)⁷⁰ ≈ 1.6×10⁻¹³` → expected deep ≈ 0 beyond {0,2,8} |
| Streaming | `for_each_candidate(chi, max_depth, parallel_depth, f)` in `saye.rs` | avoids materializing 10¹² candidates |
| Small-n overlap | brute-force `n ≤ 10⁶` (existing cross-check in `main.rs`) | closes the block-overlap gap |

## Architecture

`verify_erdos_rs/src/`:
- `leading.rs` (new): `digits_of`, `certified_ln`, `certified_alpha`, `certified_pow3_interval`, `add_one_msb` (ported, verified identical semantics), plus `leading_digits_have_two(n: u128, k_prime: usize) -> Option<bool>` with an exact BigUint path for small n and a bounded precision-doubling recursion.
- `saye.rs` (modify): candidates → `Vec<u128>`; `u_k(k) -> u128`; remove `j as u64` casts and the `u64::MAX` guard; add `for_each_candidate<F: FnMut(u128) + Sync + Send>` (phase-1 branch collection + rayon over branches + sequential recursion emitting each 2-free-trailing candidate); reimplement `run_saye` on top of it (tests unchanged).
- `two_sided.rs` (new): `run_two_sided(k, k_prime, chi, parallel_depth) -> TwoSidedReport { candidates, eliminated, deep: Vec<u128>, ambiguous, elapsed }`; per candidate apply `leading_digits_have_two`, count eliminated, push every deep candidate — **including {0,2,8}**, since validation requires the deep set to equal {0,2,8} exactly; checkpoint deep candidates; progress reporting.
- `main.rs` (modify): `mod leading; mod two_sided;` + `--two-sided K [k_prime]` CLI mode (coverage print = `2·3^{K−1}`, counts, deep list, timing).

## Interfaces

```rust
// leading.rs
pub fn leading_digits_have_two(n: u128, k_prime: usize) -> Option<bool>

// saye.rs
pub fn u_k(k: usize) -> u128
pub fn for_each_candidate<F>(chi: u8, max_depth: usize, parallel_depth: usize, f: F)
where F: FnMut(u128) + Sync + Send
pub fn run_saye(chi: u8, max_depth: usize) -> Vec<u128>   // unchanged behavior, now u128

// two_sided.rs
pub struct TwoSidedReport { pub candidates: u64, pub eliminated: u64, pub deep: Vec<u128>, pub ambiguous: u64 }
pub fn run_two_sided(k: usize, k_prime: usize, chi: u8, parallel_depth: usize) -> TwoSidedReport
```

## Validation

1. **Unit (leading.rs):** for `n ≤ 10⁵`, `leading_digits_have_two(n, 50)` matches a brute-force base-3 digit scan of `2ⁿ` (BigUint), with no `None`.
2. **Unit (saye.rs):** existing `test_saye_depth_10/15` still pass after the u128 change; `for_each_candidate` produces the same candidate multiset as `run_saye` at K=15.
3. **Engine (two_sided.rs):** `deep == {0,2,8}` at K = 10, 15, 20 (k_prime = 70); eliminated+deep+trivial = all n ≤ coverage.
4. **K=38 cross-check:** candidate count == 209.3M (Phase 1 parity) and `deep == {0,2,8}` — an independent confirmation of Saye's 5.9×10²¹ verification. Brute-force `n ≤ 10⁶` spot-check that every eliminated candidate truly has a 2.
5. **Completeness claim** recorded per run in a CSV + `verify_middle/PHASE9_FINDINGS.md` (mirrors Phase 8 findings convention).

## Milestones (timing-gated, checkpointed/resumable)

| K | coverage | est. time @16 cores | gate |
|---|---|---|---|
| 38 | 9×10¹⁷ | ~5 min | validation parity |
| 40 | 8×10¹⁸ | ~40 min | crate record |
| 42 | 7×10¹⁹ | ~6 h | push |
| 44 | 6.7×10²⁰ | ~2 d | push |
| 46 | 5.9×10²¹ | ~3 wk | match Saye |
| 47 | 1.8×10²² | ~9 wk | beat Saye |

Runs over the 30-min gate use checkpoint/resume and record results; per-project convention, full pushes may be deferred/optimized.

## Risks

- **Deep candidates beyond {0,2,8}:** would be a genuine counterexample candidate; engine records it (the whole point of the search).
- **Leading-check cost:** per-candidate ~20–50 µs (BigInt interval at scale `3^{k_prime+64}`). If K ≥ 44 runs stall, add incremental digit-by-digit elimination (stop at first certified 2) or hoist `certified_ln/alpha` to max precision.
- **Ambiguity (None):** expected ~0 (straddle probability ≈ width/3⁶⁴); recorded separately, treated as deep.
- **u128 branch count:** parallel branch vector at `parallel_depth` ≈ `2^{20}` ≈ 10⁶ — fine.