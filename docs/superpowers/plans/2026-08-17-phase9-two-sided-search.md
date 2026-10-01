# Phase 9 Two-Sided Search Engine — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Complete verification of `n ≤ 2·3^{K−1}` for the largest feasible K, by pruning Saye's trailing-digit candidate tree with a certified leading-digit check; validate to K=38, then push toward and past Saye's 5.9×10²¹.

**Architecture:** extend the `verify_erdos_rs` crate. A new `leading.rs` ports Phase 8's certified interval-arithmetic for the first K′ ternary digits of `3^{frac(n·log₃2)}` to `u128` n. `saye.rs` is upgraded to `u128` candidates and gains a streaming `for_each_candidate` visitor. A new `two_sided.rs` engine drives candidates through the leading check, counting eliminated vs deep (deep must equal `{0,2,8}`). Spec: `docs/superpowers/specs/2026-08-17-two-sided-search-design.md`.

**Tech Stack:** Rust 2021, `num-bigint 0.4` (BigInt/BigUint interval arithmetic), `rayon 1.10` (parallel), `num_cpus`, `ctrlc` — all already in `verify_erdos_rs/Cargo.toml`. No new dependencies.

## Global Constraints

- Work in `verify_erdos_rs/` (crate name `verify_erdos`). Edition 2021.
- **All candidate exponents are `u128`** — K ≥ 39 exceeds u64 (u64 max ≈ 1.8×10¹⁹). Remove every `j as u64` cast and the `u64::MAX` guard.
- `leading_digits_have_two` must be **certified** (interval arithmetic): `Some(true)` only when a 2 is rigorously present; `Some(false)` only when all first `k_prime` digits are rigorously ≠ 2; `None` on ambiguity.
- `cargo test` inside `verify_erdos_rs/` must pass after every task (existing tests stay green: `test_saye_depth_10/15`, `ternary_str`, `ternary_mod` suite).
- Milestone runs over the 30-minute gate use checkpoint/resume and record results to `verify_erdos_rs/PHASE9_FINDINGS.md`.
- No comments that restate the code; doc comments (`///`) for public items only.

---

## Amendment (2026-08-17, after Task 4)

Measured timing reality on this 4-core machine (`nproc` = 4):
- Saye traversal ≈ 2^K nodes × ~300 ns/node (dominant cost; K=25 → 4.8 s, K=30 → 186 s, K=35 → ~90 min, K=38 → ~6–12 h). The leading check is ~0.4 ms/candidate, adding ~6 h at K=38's 209.3M candidates.
- The plan's "< 30 min" gates for K=38 and K=39/40 were ~30x too optimistic; Task 6's K=44–47 targets are not reachable on this hardware regardless of leading-check optimization (traversal wall).

**Amended approach (approved):** run the validation ladder and the K=38 cross-check as checkpointed background jobs (precedent: Phase 1's K=38 and Phase 8's over-gate runs), record results in `PHASE9_FINDINGS.md`, and treat all timing gates as "record elapsed; amend estimate" rather than hard stop. Task 6 K≥42 runs use the plan's existing checkpoint/resume hedge; if they stall, record the partial run + optimization note and defer.

---

### Task 1: Port certified leading-digit machinery (`leading.rs`)

**Files:**
- Create: `verify_erdos_rs/src/leading.rs`
- Modify: `verify_erdos_rs/src/main.rs` (add `mod leading;`)
- Test: inline `#[cfg(test)] mod tests` in `leading.rs`

**Interfaces:**
- Produces: `pub fn leading_digits_have_two(n: u128, k_prime: usize) -> Option<bool>` — `Some(true)` certified 2 among first `k_prime` leading ternary digits of `3^{frac(n·α)}`; `Some(false)` certified all ≠ 2; `None` ambiguous. Internal `certified_ln/certified_alpha/certified_pow3_interval/digits_of/add_one_msb` ported from `verify_middle/src/certified.rs`.

- [x] **Step 1: Baseline — confirm current tests pass**

Run: `cargo test` (in `verify_erdos_rs/`)
Expected: all tests pass (Saye depth 10/15, ternary_str, ternary_mod).

- [x] **Step 2: Write the failing validation test**

Add to `verify_erdos_rs/src/leading.rs`:

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigUint;

    fn brute_first_k_have_two(pow2: &BigUint, k_prime: usize) -> bool {
        pow2.to_str_radix(3).bytes().take(k_prime).any(|b| b == b'2')
    }

    #[test]
    fn leading_check_matches_bruteforce() {
        let mut pow2 = BigUint::from(1u8);
        for n in 0u128..=10_000 {
            let got = leading_digits_have_two(n, 50);
            let expect = brute_first_k_have_two(&pow2, 50);
            assert_eq!(got, Some(expect), "mismatch at n={n}");
            pow2 *= 2u32;
        }
    }

    #[test]
    fn known_record_agrees_with_phase8() {
        // Phase 8 record n = 464,263,536 has f(n) = 50 (first 2 at 0-indexed
        // position 50): first 50 leading digits are 2-free, first 51 are not.
        let n = 464_263_536u128;
        assert_eq!(leading_digits_have_two(n, 50), Some(false));
        assert_eq!(leading_digits_have_two(n, 51), Some(true));
    }
}
```

- [x] **Step 3: Run the test to verify it fails**

Run: `cargo test --lib leading`
Expected: FAIL — `leading_digits_have_two` not found.

- [x] **Step 4: Implement `leading.rs`**

```rust
//! Certified leading ternary digits of 3^{frac(n·log_3 2)} (2^n's leading digits).
//!
//! Port of verify_middle/src/certified.rs interval arithmetic, trimmed to the
//! first `k_prime` digits for u128 n. Public entry: `leading_digits_have_two`.

use num_bigint::{BigInt, BigUint};

/// Guard digits appended after the reportable prefix (matches verify_middle).
const GUARDS: usize = 20;

fn digits_of(v: &BigInt, p: usize) -> Vec<u8> {
    let g = p + GUARDS;
    let three = BigInt::from(3u8);
    let mut x = v.clone();
    let mut lsb = Vec::new();
    if x == BigInt::from(0u8) {
        lsb.push(0);
    }
    while x > BigInt::from(0u8) {
        let d = (&x % &three).to_str_radix(10).parse::<u8>().unwrap();
        lsb.push(d);
        x /= &three;
    }
    lsb.reverse();
    let mut out = vec![0u8; g];
    out[..lsb.len()].copy_from_slice(&lsb);
    out
}

fn add_one_msb(digits: &[u8]) -> Vec<u8> {
    let mut out = digits.to_vec();
    let mut carry = 1u8;
    for i in (0..out.len()).rev() {
        let s = out[i] + carry;
        out[i] = s % 3;
        carry = s / 3;
        if carry == 0 {
            break;
        }
    }
    if carry > 0 {
        out.insert(0, carry);
    }
    out
}

/// ln(x) ∈ [lo, hi]·3^-p for x ∈ {2, 3}, rigorous (port of certified_ln).
pub fn certified_ln(x: u32, p: usize) -> (BigInt, BigInt) {
    let s = BigInt::from(3u32).pow(p as u32);
    let xb = BigInt::from(x);
    let xm1 = BigInt::from(x - 1);
    let xp1 = BigInt::from(x + 1);
    let t = (x - 1) as f64 / (x + 1) as f64;
    let need = (p as f64 * 3f64.ln() / (1f64 / t).ln()).ceil() as usize + 20;
    let t2n = &xm1 * &xm1;
    let t2d = &xp1 * &xp1;
    let mut num = xm1.clone();
    let mut den = xp1.clone();
    let mut lo = BigInt::from(0u8);
    let mut hi = BigInt::from(0u8);
    for k in 0..need as u64 {
        let n = 2 * &s * &num;
        let d = &den * BigInt::from(2 * k + 1);
        let q = &n / &d;
        lo += &q;
        hi += &q + 1;
        num *= &t2n;
        den *= &t2d;
    }
    let nbig = BigInt::from(need as i64);
    let rn = 2 * &s * &num * &xp1;
    let rd = &den * (2 * &nbig + 1) * 4 * &xb;
    let rem = &rn / &rd;
    hi += &rem + 1;
    (lo, hi)
}

/// α = log₃2 ∈ [lo, hi]·3^-p.
pub fn certified_alpha(p: usize) -> (BigInt, BigInt) {
    let s = BigInt::from(3u32).pow(p as u32);
    let (l2lo, l2hi) = certified_ln(2, p);
    let (l3lo, l3hi) = certified_ln(3, p);
    let lo = &l2lo * &s / &l3hi;
    let hi = &l2hi * &s / &l3lo + 1;
    (lo, hi)
}

/// 3^t ∈ [lo, hi]·3^-p for all t ∈ [a, b]·3^-p ⊆ [0, 1) (port of certified_pow3_interval).
pub fn certified_pow3_interval(a: &BigInt, b: &BigInt, p: usize) -> (BigInt, BigInt) {
    let m: usize = 60;
    let sc = BigInt::from(3u32).pow((p + m) as u32);
    let two_p = BigInt::from(3u32).pow(2 * p as u32);
    let (l3lo, l3hi) = certified_ln(3, p);
    let u1n = b * &l3hi;
    let u1d = two_p.clone();
    let log_sc = (p + m) as f64 * 3f64.ln();
    let mut k_terms: usize = 16;
    loop {
        let kk = k_terms as f64;
        if kk * kk.ln() - kk > log_sc + kk * 1.1f64.ln() {
            break;
        }
        k_terms *= 2;
    }
    k_terms += 20;
    let mut lo = sc.clone();
    let mut hi = sc.clone();
    let mut tklo = sc.clone();
    let mut tkhi = sc.clone();
    for k in 1..=k_terms as u64 {
        let kd = BigInt::from(k as i64);
        let lo_k = &tklo * a * &l3lo / (&kd * &two_p);
        let hi_k = &tkhi * b * &l3hi / (&kd * &two_p);
        lo += &lo_k;
        hi += &hi_k;
        tklo = lo_k;
        tkhi = hi_k;
    }
    let kn = BigInt::from(k_terms as i64);
    let tail_num = &tkhi * &u1n * BigInt::from((k_terms + 2) as i64) * &u1d;
    let tail_den = (&kn + 1) * &u1d * (BigInt::from((k_terms + 2) as i64) * &u1d - &u1n);
    let tail = (&tail_num + &tail_den - 1) / &tail_den;
    let upper = &hi + &kn + &tail;
    let sm = BigInt::from(3u32).pow(m as u32);
    (&lo / &sm, (upper + &sm - 1) / &sm)
}

/// Certified answer: does 3^{frac(n·α)} have a digit 2 among its first k_prime
/// ternary digits? `Some(true)` certifies a 2, `Some(false)` certifies all
/// ≠ 2, `None` means the interval stayed ambiguous (caller treats as deep).
pub fn leading_digits_have_two(n: u128, k_prime: usize) -> Option<bool> {
    if k_prime > 512 {
        return None;
    }
    let small_limit = (k_prime + 1) as f64 * 1.585;
    if (n as f64) <= small_limit {
        let two_n = BigUint::from(2u8).pow(n as u32);
        let s = two_n.to_str_radix(3);
        return Some(s.bytes().take(k_prime).any(|b| b == b'2'));
    }
    let p_hi = k_prime + 64;
    let s_hi = BigInt::from(3u32).pow(p_hi as u32);
    let (alo, ahi) = certified_alpha(p_hi);
    let nb = BigInt::from(n);
    let nlo = &nb * &alo;
    let nhi = &nb * &ahi;
    let flo = &nlo / &s_hi;
    let fhi = &nhi / &s_hi;
    if &flo != &fhi {
        return leading_digits_have_two(n, k_prime * 2);
    }
    let k = flo;
    let kp = &k * &s_hi;
    let a = &nlo - &kp;
    let b = &nhi - &kp;
    let (ylo, yhi) = certified_pow3_interval(&a, &b, p_hi);
    let sm = BigInt::from(3u32).pow(64u32);
    let ylo_p = &ylo / &sm;
    let yhi_p = (&yhi + &sm - 1) / &sm;
    if &yhi_p - &ylo_p > BigInt::from(1u8) {
        return leading_digits_have_two(n, k_prime * 2);
    }
    let r = digits_of(&ylo_p, k_prime);
    let r1 = add_one_msb(&r[..=k_prime]);
    let r1 = &r1[..=k_prime];
    for i in 0..=k_prime {
        let a_d = r[i];
        let b_d = r1[i];
        if a_d != b_d {
            if a_d == 2 || b_d == 2 {
                return None;
            }
        } else if a_d == 2 {
            return Some(true);
        }
    }
    Some(false)
}
```

- [x] **Step 5: Run the tests to verify they pass**

Run: `cargo test leading`
Expected: PASS — brute-force grid n ≤ 10⁴ and the Phase 8 record check both green.

- [x] **Step 6: Commit**

```bash
git add verify_erdos_rs/src/leading.rs verify_erdos_rs/src/main.rs
git commit -m "feat(verify_erdos): certified leading-digit check (u128) for the two-sided engine"
```

---

### Task 2: Upgrade Saye candidates to u128

**Files:**
- Modify: `verify_erdos_rs/src/saye.rs`
- Modify: `verify_erdos_rs/src/main.rs`
- Test: existing `test_saye_depth_10/15` in `saye.rs` (update expectations to u128)

**Interfaces:**
- Consumes: nothing new.
- Produces: `pub fn u_k(k: usize) -> u128`; `pub fn run_saye(chi: u8, max_depth: usize) -> Vec<u128>`; `pub fn run_saye_with_parallel_depth(chi: u8, max_depth: usize, parallel_depth: usize) -> Vec<u128>`; `pub fn run_saye_with_checkpoint(...) -> Vec<u128>`; `pub fn load_checkpoint(path: &str) -> Vec<u128>`; `pub fn save_checkpoint(candidate: u128, path: &str)`.

- [x] **Step 1: Write the failing test (u128 expectation)**

Update `saye.rs` tests:

```rust
    #[test]
    fn test_saye_depth_10() {
        let results = run_saye(2, 10);
        let mut r = results.clone();
        r.sort();
        assert_eq!(r, vec![0u128, 2, 8]);
    }

    #[test]
    fn test_saye_depth_15() {
        let results = run_saye(2, 15);
        let mut r = results.clone();
        r.sort();
        assert_eq!(r, vec![0u128, 2, 8]);
    }
```

- [x] **Step 2: Run the test to verify it fails (type error)**

Run: `cargo test test_saye_depth_10`
Expected: FAIL to compile — `Vec<u64>` vs `Vec<u128>` mismatch.

- [x] **Step 3: Implement the u128 upgrade in `saye.rs`**

Apply these exact edits:

```rust
/// u_k = 2·3^{k-1}, as u128 (needed for k ≥ 39 where u_k > u64::MAX).
pub fn u_k(k: usize) -> u128 {
    if k == 0 { return 1; }
    2u128 * 3u128.pow((k - 1) as u32)
}
```

```rust
fn generate_sequential(
    k: usize,
    u_k: u128,
    pow_uk: TernaryMod,
    j: u128,
    pow_j: TernaryMod,
    chi: u8,
    max_depth: usize,
    counter: &AtomicU64,
    results: &mut Vec<u128>,
) {
```

```rust
fn generate_sequential_inner(
    k: usize,
    u_k: u128,
    pow_uk: TernaryMod,
    j: u128,
    pow_j: TernaryMod,
    chi: u8,
    max_depth: usize,
    counter: &mut u64,
    results: &mut Vec<u128>,
) {
    *counter += 1;

    if k >= max_depth {
        if !pow_j.has_digit(chi, KAPPA) {
            results.push(j);
        }
        return;
    }

    let u_next = 3u128 * u_k;
    let pow_uk_next = pow_uk.pow(3);
    let pow_uk_sq = pow_uk.mul(&pow_uk);

    for i in 0..3u128 {
        let j_new = j + i * u_k;
        let pow_j_new = match i {
            0 => pow_j,
            1 => pow_j.mul(&pow_uk),
            _ => pow_j.mul(&pow_uk_sq),
        };

        let digit_k1 = pow_j_new.ternary_digit(k);

        if digit_k1 != chi {
            generate_sequential_inner(
                k + 1, u_next, pow_uk_next,
                j_new, pow_j_new, chi,
                max_depth, counter, results,
            );
        }
    }
}
```

```rust
fn collect_branches(
    k: usize,
    u_k: u128,
    pow_uk: TernaryMod,
    j: u128,
    pow_j: TernaryMod,
    chi: u8,
    parallel_depth: usize,
    counter: &AtomicU64,
) -> Vec<(u128, TernaryMod, u128, TernaryMod)> {
    if k >= parallel_depth {
        return vec![(j, pow_j, u_k, pow_uk)];
    }

    counter.fetch_add(1, Ordering::Relaxed);

    let u_next = 3u128 * u_k;
    let pow_uk_next = pow_uk.pow(3);
    let pow_uk_sq = pow_uk.mul(&pow_uk);
    let mut branches = Vec::with_capacity(3);

    for i in 0..3u128 {
        let j_new = j + i * u_k;
        let pow_j_new = match i {
            0 => pow_j,
            1 => pow_j.mul(&pow_uk),
            _ => pow_j.mul(&pow_uk_sq),
        };

        let digit_k1 = pow_j_new.ternary_digit(k);

        if digit_k1 != chi {
            let sub = collect_branches(
                k + 1, u_next, pow_uk_next,
                j_new, pow_j_new, chi,
                parallel_depth, counter,
            );
            branches.extend(sub);
        }
    }

    branches
}
```

And in `run_saye_full`:
- `let mut existing: Vec<u128> = ...`;
- branch destructure stays `(j, pow_j, u_k, pow_uk)` (now u128);
- initial `collect_branches(1, 2u128, TernaryMod::from_u64(4), 0, TernaryMod::one(), chi, parallel_depth, &counter)`;
- `run_saye_full(chi, max_depth, parallel_depth, checkpoint, resume) -> Vec<u128>`;
- `run_saye_with_checkpoint(..., parallel_depth: Option<usize>) -> Vec<u128>`;
- `save_checkpoint(candidate: u128, path: &str)` (writeln of u128 is fine);
- `load_checkpoint` parses `u128`:

```rust
pub fn load_checkpoint(checkpoint_path: &str) -> Vec<u128> {
    use std::fs;
    fs::read_to_string(checkpoint_path)
        .unwrap_or_default()
        .lines()
        .filter_map(|line| line.trim().parse().ok())
        .collect()
}
```

- [x] **Step 4: Update `main.rs` for u128 candidates**

In the `--saye` cross-check block: `for &n in &candidates` with `n: u128`; guard `if n <= cross_check_limit` (u128 vs u64 — compare `n as u128`), `let val = two.pow(n as u32)`, `ternary_str(n as u64)`; `large_candidates: Vec<u128>`; prints unchanged. Coverage print uses `saye::u_k(max_depth)` (now u128, Display works).

- [x] **Step 5: Run the full test suite**

Run: `cargo test`
Expected: PASS — depth 10/15 tests now assert u128 lists; ternary_mod suite unaffected.

- [x] **Step 6: Commit**

```bash
git add verify_erdos_rs/src/saye.rs verify_erdos_rs/src/main.rs
git commit -m "refactor(verify_erdos): Saye candidates u128 (unlocks K >= 39)"
```

---

### Task 3: Streaming candidate visitor `for_each_candidate`

**Files:**
- Modify: `verify_erdos_rs/src/saye.rs`
- Test: inline in `saye.rs`

**Interfaces:**
- Produces: `pub fn for_each_candidate<F>(chi: u8, max_depth: usize, parallel_depth: usize, f: F) where F: FnMut(u128) + Sync + Send` — visits every candidate (2-free in the first `KAPPA` trailing digits) once, in parallel, without materializing them. Consumed by the engine (Task 4) and by the equivalence test here.

- [x] **Step 1: Write the failing equivalence test**

Add to `saye.rs` tests:

```rust
    #[test]
    fn for_each_candidate_matches_run_saye() {
        let all = run_saye(2, 15);
        let mut seen: Vec<u128> = Vec::new();
        for_each_candidate(2, 15, 8, |j| seen.push(j));
        seen.sort_unstable();
        assert_eq!(seen, all, "for_each_candidate vs run_saye disagree");
    }
```

- [x] **Step 2: Run to verify it fails**

Run: `cargo test for_each_candidate_matches_run_saye`
Expected: FAIL — `for_each_candidate` not found.

- [x] **Step 3: Implement `for_each_candidate`**

Add to `saye.rs` (reuses `collect_branches` and `generate_sequential_inner`):

```rust
/// Visit every candidate exponent (2-free in the first KAPPA trailing digits)
/// at depth max_depth, in parallel, streaming — never materializes the set.
pub fn for_each_candidate<F>(chi: u8, max_depth: usize, parallel_depth: usize, f: F)
where
    F: FnMut(u128) + Sync + Send,
{
    let parallel_depth = std::cmp::min(parallel_depth, max_depth);
    let counter = AtomicU64::new(0);
    let branches = collect_branches(
        1, 2u128, TernaryMod::from_u64(4),
        0, TernaryMod::one(), chi, parallel_depth, &counter,
    );
    let total_branches = branches.len() as u64;
    let progress = AtomicU64::new(0);
    let started = Instant::now();
    let f = std::sync::Mutex::new(f);
    branches.into_par_iter().for_each(|(j, pow_j, u_k, pow_uk)| {
        let mut local_count = 0u64;
        let mut leaf = Vec::new();
        generate_sequential_inner(
            parallel_depth, u_k, pow_uk,
            j, pow_j, chi, max_depth, &mut local_count, &mut leaf,
        );
        let mut f = f.lock().unwrap();
        for cand in leaf {
            f(cand);
        }
        drop(f);
        let done = progress.fetch_add(1, Ordering::Relaxed) + 1;
        if done % 1000 == 0 || done == total_branches {
            eprintln!("    [{done}/{total_branches}] branches, {:.1?}", started.elapsed());
        }
    });
}
```

Note: `generate_sequential_inner` already pushes the candidate to `results` only when `!pow_j.has_digit(chi, KAPPA)`, so `leaf` holds exactly the candidates of that branch.

- [x] **Step 4: Run to verify it passes**

Run: `cargo test for_each_candidate_matches_run_saye`
Expected: PASS — same candidate multiset as `run_saye` at K=15.

- [x] **Step 5: Commit**

```bash
git add verify_erdos_rs/src/saye.rs
git commit -m "feat(verify_erdos): for_each_candidate streaming visitor"
```

---

### Task 4: Two-sided engine + CLI

**Files:**
- Create: `verify_erdos_rs/src/two_sided.rs`
- Modify: `verify_erdos_rs/src/main.rs` (add `mod two_sided;` + `--two-sided` mode)
- Test: inline in `two_sided.rs`

**Interfaces:**
- Consumes: `leading::leading_digits_have_two(n: u128, k_prime: usize) -> Option<bool>`; `saye::{for_each_candidate, optimal_parallel_depth, u_k}`.
- Produces:
  ```rust
  pub struct TwoSidedReport {
      pub candidates: u64,      // Saye candidates visited (2-free trailing 54)
      pub eliminated: u64,      // certified 2 in the first k_prime leading digits
      pub deep: Vec<u128>,      // 2-free in leading k_prime AND trailing 54 (incl. {0,2,8})
      pub ambiguous: u64,       // leading check returned None
      pub elapsed: std::time::Duration,
  }
  pub fn run_two_sided(k: usize, k_prime: usize, chi: u8, parallel_depth: usize) -> TwoSidedReport
  ```

- [x] **Step 1: Write the failing engine test**

Add to `verify_erdos_rs/src/two_sided.rs`:

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn deep_set_is_known_solutions() {
        for k in [10usize, 15, 20, 25, 30] {
            let rep = run_two_sided(k, 70, 2, 10);
            assert_eq!(rep.deep, vec![0u128, 2, 8], "deep set at K={k}");
            assert_eq!(
                rep.candidates,
                rep.eliminated + rep.deep.len() as u64 + rep.ambiguous,
                "bookkeeping at K={k}"
            );
        }
    }
}
```

- [x] **Step 2: Run to verify it fails**

Run: `cargo test deep_set_is_known_solutions`
Expected: FAIL — `run_two_sided` not found.

- [x] **Step 3: Implement `two_sided.rs`**

```rust
//! Two-sided pruning engine: Saye trailing-digit candidates + certified
//! leading-digit check. Completeness (spec): if `deep == {0,2,8}` and small n
//! are brute-forced, every n <= 2·3^{K-1} is verified.

use crate::leading::leading_digits_have_two;
use crate::saye::{for_each_candidate, optimal_parallel_depth, u_k};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Mutex;
use std::time::{Duration, Instant};

pub struct TwoSidedReport {
    pub candidates: u64,
    pub eliminated: u64,
    pub deep: Vec<u128>,
    pub ambiguous: u64,
    pub elapsed: Duration,
}

pub fn run_two_sided(k: usize, k_prime: usize, chi: u8, parallel_depth: usize) -> TwoSidedReport {
    let started = Instant::now();
    let candidates = AtomicU64::new(0);
    let eliminated = AtomicU64::new(0);
    let ambiguous = AtomicU64::new(0);
    let deep = Mutex::new(Vec::new());

    for_each_candidate(chi, k, parallel_depth, |n| {
        candidates.fetch_add(1, Ordering::Relaxed);
        match leading_digits_have_two(n, k_prime) {
            Some(true) => {
                eliminated.fetch_add(1, Ordering::Relaxed);
            }
            Some(false) => {
                deep.lock().unwrap().push(n);
            }
            None => {
                ambiguous.fetch_add(1, Ordering::Relaxed);
            }
        }
    });

    let mut deep = deep.into_inner().unwrap();
    deep.sort_unstable();
    deep.dedup();

    TwoSidedReport {
        candidates: candidates.load(Ordering::Relaxed),
        eliminated: eliminated.load(Ordering::Relaxed),
        deep,
        ambiguous: ambiguous.load(Ordering::Relaxed),
        elapsed: started.elapsed(),
    }
}

/// Machine-readable one-line report (used by CLI and milestone runs).
pub fn report_line(rep: &TwoSidedReport, k: usize, k_prime: usize, chi: u8) -> String {
    format!(
        "K={} coverage={} k_prime={} chi={} candidates={} eliminated={} deep={:?} ambiguous={} elapsed={:.2?}",
        k, u_k(k), k_prime, chi, rep.candidates, rep.eliminated, rep.deep, rep.ambiguous, rep.elapsed
    )
}
```

- [x] **Step 4: Wire the `--two-sided` CLI mode**

In `main.rs` add `mod two_sided;` and, before the brute-force branch:

```rust
    if args.len() > 1 && args[1] == "--two-sided" {
        let k: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(38);
        let k_prime: usize = args.get(3).and_then(|s| s.parse().ok()).unwrap_or(70);
        let chi: u8 = 2;
        let parallel_depth = two_sided::optimal_parallel_depth(k);
        println!("=== Two-Sided Search (K={k}, k_prime={k_prime}) ===");
        println!("Coverage: n ≤ {}", saye::u_k(k));
        println!("Parallel depth: {parallel_depth}");
        let rep = two_sided::run_two_sided(k, k_prime, chi, parallel_depth);
        println!("{}", two_sided::report_line(&rep, k, k_prime, chi));
        return;
    }
```

Also add the mode to the `--help` text (add a line `verify_erdos --two-sided K [k_prime]   Two-sided pruning engine`).

Note: `optimal_parallel_depth` is currently defined in `saye.rs`; re-export it from `two_sided` usage via `crate::saye::optimal_parallel_depth`, and use that in main.rs to avoid a new public path.

- [x] **Step 5: Run the tests**

Run: `cargo test deep_set_is_known_solutions`
Expected: PASS — deep == `{0,2,8}` and bookkeeping exact at K = 10, 15, 20, 25, 30.

- [x] **Step 6: Quick smoke run**

Run: `cargo run --release -- --two-sided 25 70`
Expected: `candidates=130 eliminated=127 deep=[0, 2, 8] ambiguous=0` (matches Phase 1's "130 candidates, 3 fully verified").

- [x] **Step 7: Commit**

```bash
git add verify_erdos_rs/src/two_sided.rs verify_erdos_rs/src/main.rs
git commit -m "feat(verify_erdos): two-sided engine (Saye + certified leading check) with CLI"
```

---

### Task 5: Validation harness and K=38 cross-check

**Files:**
- Create: `verify_erdos_rs/PHASE9_FINDINGS.md`
- Test: none new (validates via CLI runs); results recorded in the findings file

**Interfaces:**
- Consumes: `run_two_sided` + `report_line` from Task 4.

- [x] **Step 1: Run the full validation ladder**

Run:
```bash
cargo run --release -- --two-sided 10 70
cargo run --release -- --two-sided 15 70
cargo run --release -- --two-sided 20 70
cargo run --release -- --two-sided 25 70
cargo run --release -- --two-sided 30 70
cargo run --release -- --two-sided 35 70
```
Expected: every line reports `deep=[0, 2, 8] ambiguous=0`; `candidates` matches the Phase 1 counts at K = 25/30/35 (130 / 31,894 / 7,749,016 approx — record the exact numbers).

- [x] **Step 2: Brute-force spot-check eliminated candidates (n ≤ 10⁶)**

Run: `cargo run --release -- --two-sided 30 70` and confirm separately (via the existing brute-force mode `verify_erdos 1000000`, which already proves every n ≤ 10⁶ has a 2) that no contradiction exists: every eliminated candidate's `2ⁿ` truly contains a 2.
Expected: brute-force mode finds counterexamples = {} (empty) for n = 9..10⁶; this closes the small-n block-overlap gap.

- [x] **Step 3: K=38 cross-check (gate: < 30 min → AMENDED: ~12–18 h background run, record results)**

Run:
```bash
cargo run --release -- --two-sided 38 70
```
Expected: `candidates ≈ 209,300,000` (Phase 1 parity, exact count recorded), `deep=[0, 2, 8]`, `ambiguous=0`. This independently re-derives Saye's 5.9×10²¹ verification (every candidate n ≤ 9×10¹⁷ with 2-free trailing 54 digits provably has a 2 in its first 70 leading digits, except the three solutions).

- [x] **Step 4: Write `verify_erdos_rs/PHASE9_FINDINGS.md`**

Record: the completeness argument (spec), the validation table (K, coverage, candidates, eliminated, deep, ambiguous, elapsed), the K=38 result, and the brute-force small-n note.

- [x] **Step 5: Update ROADMAP Phase 9 checkboxes**

Mark `- [x] Two-sided pruning engine` and `- [x] Validate engine ... at K ≤ 38` in `ROADMAP.md`.

- [x] **Step 6: Commit**

```bash
git add verify_erdos_rs/PHASE9_FINDINGS.md ROADMAP.md
git commit -m "data: two-sided engine validated to K=38 (deep={0,2,8}), independent of Saye's 5.9e21"
```

---

### Task 6: Milestone runs and record push (timing-gated)

**Files:**
- Modify: `verify_erdos_rs/PHASE9_FINDINGS.md`
- Modify: `ROADMAP.md`

**Interfaces:**
- Consumes: `--two-sided K k_prime` CLI from Task 4.

- [ ] **Step 1: K=39 and K=40 runs (new crate records, gate: < 30 min each → AMENDED: background runs, ~1–2 d, record elapsed)**

Run:
```bash
cargo run --release -- --two-sided 39 70
cargo run --release -- --two-sided 40 70
```
Expected: coverage 2.7×10¹⁸ and 8.1×10¹⁸ respectively; `deep=[0, 2, 8]`, `ambiguous=0`. These are complete verifications beyond Phase 1's 9×10¹⁷.

- [ ] **Step 2: Best-effort K=42, 44 (gate: over 30 min → checkpoint/resume, record only)**

Run with a nohup/background shell, monitoring progress:
```bash
nohup cargo run --release -- --two-sided 42 70 > /tmp/k42.log 2>&1 &
```
Expected: coverage 7.3×10¹⁹ (K=42) and 6.6×10²⁰ (K=44); deep `{0,2,8}`. Record elapsed. If K ≥ 42 stalls (> ~6 h for K=42, ~2 d for K=44), stop and record the partial run + note the per-candidate-cost optimization (incremental digit-by-digit elimination, or hoisting `certified_ln/alpha` to max precision) as a follow-up rather than waiting.

- [ ] **Step 3: Stretch K=46 (match Saye 5.9×10²¹) / K=47 (beat)**

Run as a long background job only if K ≤ 44 completed within estimate. Expected K=46 coverage 5.9×10²¹, K=47 coverage 1.8×10²². Document results or the deferral decision (optimization required) in findings.

- [ ] **Step 4: Update findings + roadmap**

Append milestone results (K, coverage, candidates, eliminated, deep, elapsed) to `verify_erdos_rs/PHASE9_FINDINGS.md`; mark the remaining Phase 9 checkboxes in `ROADMAP.md` (`- [x] Push verification record beyond 5.9×10²¹` only when K=47 lands; otherwise leave unchecked with a note).

- [ ] **Step 5: Commit**

```bash
git add verify_erdos_rs/PHASE9_FINDINGS.md ROADMAP.md
git commit -m "data: two-sided verification milestones K=39..44 (records + findings)"
```
