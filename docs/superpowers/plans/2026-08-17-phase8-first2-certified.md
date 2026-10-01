# Phase 8 M1: Certified First-2-Position Records f(n) — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [x]`) syntax for tracking.

**Goal:** Produce the first certified dataset of `f(n)` — the number of leading (most-significant) ternary digits of `2ⁿ` that are ≠ 2 before the first digit 2 — for n up to 10⁹, with record-holder statistics and the ratio `f(n)/L(n)`, every value mathematically certified via interval enclosures.

**Architecture:** Extend the `verify_middle` Rust crate with a certified mantissa stream. The mantissa `yₙ = 2ⁿ/3^⌊nα⌋ ∈ [1,3)`, α = log₃2, evolves by `yₙ₊₁ = 2yₙ/3^δₙ` with `δₙ = 1 ⟺ 2yₙ ≥ 3`. We store big-endian ternary digits: reportable precision `p` (positions 0..p, always an exact-or-one-low truncation of yₙ) plus `GUARDS = 20` guard digits used for exact arithmetic. The δ decision and the f(n) scan are certified against the enclosure `[R, R+1]·3⁻ᵖ`. Any ambiguity (δ near 3/2, truncation boundary, or first-2 beyond the reportable window) triggers **escalation**: an independent certified computation of `yₙ = 3^{frac(n·α)}` via rigorous interval arithmetic (atanh series for ln2/ln3, Taylor `e^t` with verified remainder), re-seeding the stream at precision `p′ = 4p`. Records are re-verified through the same independent route.

**Tech Stack:** Rust (edition 2021, `num-bigint` only — no new deps), Python 3 (stdlib only), Cargo. Mirrors `verify_middle` Phase 7 conventions.

## Global Constraints
- Repo root: `/media/playplatoon/New Volume/projects/erdos problem ternary expansion`
- No new third-party deps; Rust deps: `num-bigint` only (do NOT add `num-traits`/`num-rational` — use `BigInt::from(n)` and manual comparison instead).
- Big-endian mantissa digits: `digits[0]` = integer digit `d₀ ∈ {1,2}` (most significant), `digits[1..=p]` reportable fractional, `digits[p+1..]` guard digits. Length `g = p + GUARDS`, `GUARDS = 20`.
- Reportable value `R = digits[0..=p]` (as integer in units of `3⁻ᵖ`). Invariant: `yₙ ∈ [R, R+1]·3⁻ᵖ` (R is an exact-or-one-low truncation).
- `L(n) = ⌊n·α⌋ + 1`, maintained as `len` in the stream (`lenₙ₊₁ = lenₙ + δₙ`); `f(n) ≥ L ⟺ A_L` (Phase 7 event). `f(n)=0` ⟺ leading digit is 2; if `2ⁿ` is entirely 2-free then `f(n) = L(n)`.
- Records CSV columns (exact order): `n,f,L,ratio,prefix,mantissa_precision,record_number,gap_from_previous_record`.
- Commit after each task (local git; push is deferred — do NOT attempt push).
- No code comments unless they encode a math fact needed for correctness.

---

### Task 1: `mantissa.rs` — certified mantissa stream (step + f_scan)

**Files:**
- Create: `verify_middle/src/mantissa.rs`
- Modify: `verify_middle/src/main.rs` (add `mod mantissa;`)
- Test: inline `#[cfg(test)]` in `verify_middle/src/mantissa.rs`

**Interfaces:**
- Consumes: `stream::Stream` (Phase 7) for the test only.
- Produces:
  - `pub const GUARDS: usize = 20`
  - `pub const DEFAULT_P: usize = 200`
  - `pub struct Mantissa { pub n: u64, pub p: usize, pub digits: Vec<u8>, pub len: u64 }`
  - `impl Mantissa { pub fn new(p: usize) -> Self; pub fn from_parts(n: u64, p: usize, digits: Vec<u8>, len: u64) -> Self; pub fn f_scan(&self) -> Option<usize>; pub fn step(&mut self) -> Result<(), ()> }`
  - helpers `doubled(&[u8]) -> Vec<u8>`, `div3(&[u8]) -> Vec<u8>`, `add_at_end(&[u8], u8) -> Vec<u8>`, `cmp_digits(&[u8], &[u8]) -> Ordering` (all big-endian).
  - `pub fn exact_f(digits_lsb: &[u8]) -> usize` (test/validation helper).

- [x] **Step 1: Write the failing test** (`verify_middle/src/mantissa.rs`)

```rust
use crate::stream::Stream;

pub const GUARDS: usize = 20;
pub const DEFAULT_P: usize = 200;

pub struct Mantissa {
    pub n: u64,
    pub p: usize,
    pub digits: Vec<u8>,
    pub len: u64,
}

/// First-2 position from the MSB side of a least-significant-first digit array.
/// Returns `digits.len()` if the number is entirely 2-free.
pub fn exact_f(digits_lsb: &[u8]) -> usize {
    for (j, &d) in digits_lsb.iter().rev().enumerate() {
        if d == 2 {
            return j;
        }
    }
    digits_lsb.len()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn stream_mantissa_f(m: &mut Mantissa) -> usize {
        match m.f_scan() {
            Some(f) => f,
            None if (m.p as u64) >= m.len => m.len as usize,
            None => panic!("unexpected escalation needed at p={}", m.p),
        }
    }

    #[test]
    fn mantissa_matches_exact_f() {
        let mut m = Mantissa::new(DEFAULT_P);
        let mut s = Stream::new();
        for n in 0..=30 {
            let fex = exact_f(&s.digits);
            let fm = stream_mantissa_f(&mut m);
            assert_eq!(fm, fex, "f mismatch at n={n}");
            m.step().expect("step ambiguous at p=200");
            s.double();
        }
    }
}
```

- [x] **Step 2: Run test to verify it fails**

Run: `cd verify_middle && cargo test`
Expected: FAIL — `Mantissa`, `f_scan`, `step` not defined.

- [x] **Step 3: Implement the digit helpers and `Mantissa`**

Add to `verify_middle/src/mantissa.rs`:

```rust
use std::cmp::Ordering;

/// 2 * digits, big-endian, carry from the right. Returns `len+1` digits.
fn doubled(digits: &[u8]) -> Vec<u8> {
    let mut out = vec![0u8; digits.len() + 1];
    let mut carry: u8 = 0;
    for i in (0..digits.len()).rev() {
        let s = 2 * digits[i] + carry;
        out[i + 1] = s % 3;
        carry = s / 3;
    }
    out[0] = carry;
    out
}

/// floor(digits / 3), big-endian long division. Same length as input.
fn div3(digits: &[u8]) -> Vec<u8> {
    let mut out = vec![0u8; digits.len()];
    let mut rem: u8 = 0;
    for i in 0..digits.len() {
        let cur = rem * 3 + digits[i];
        out[i] = cur / 3;
        rem = cur % 3;
    }
    out
}

/// digits + k at the last position, carry leftward. May grow by one digit.
fn add_at_end(digits: &[u8], k: u8) -> Vec<u8> {
    let mut out = digits.to_vec();
    let mut carry = k;
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

/// Compare two equal-length big-endian digit arrays.
fn cmp_digits(a: &[u8], b: &[u8]) -> Ordering {
    for (x, y) in a.iter().zip(b.iter()) {
        if x != y {
            return x.cmp(y);
        }
    }
    Ordering::Equal
}

impl Mantissa {
    pub fn new(p: usize) -> Self {
        let g = p + GUARDS;
        let mut digits = vec![0u8; g];
        digits[0] = 1; // y_0 = 1.000...
        Mantissa { n: 0, p, digits, len: 1 }
    }

    pub fn from_parts(n: u64, p: usize, digits: Vec<u8>, len: u64) -> Self {
        Mantissa { n, p, digits, len }
    }

    /// Certified f(n) from the enclosure [R, R+1]·3^-p.
    /// Some(r) = first-2 at position r is certified; None = not certifiable
    /// (first-2 beyond position p, or the digit boundary is ambiguous).
    pub fn f_scan(&self) -> Option<usize> {
        let r = &self.digits[..=self.p];
        let r1 = add_at_end(r, 1);
        let r1 = &r1[..=self.p];
        for i in 0..=self.p {
            let a = r[i];
            let b = r1[i];
            if a != b {
                if a == 2 || b == 2 {
                    return None;
                }
            } else if a == 2 {
                return Some(i);
            }
        }
        None
    }

    /// Advance n -> n+1 with certified δ decision and exact re-truncation.
    /// Err = ambiguity (δ near 3/2, or truncation boundary) -> caller escalates.
    pub fn step(&mut self) -> Result<(), ()> {
        // δ decision from reportable R (enclosure [R, R+1]·3^-p).
        let r = self.digits[..=self.p].to_vec();
        let r2 = doubled(&r); // value 2R, p+2 digits
        let mut thresh = vec![0u8; r2.len()];
        thresh[0] = 1; // 3^(p+1)
        let delta = match cmp_digits(&r2, &thresh) {
            Ordering::Greater => 1,
            Ordering::Less => {
                let r2p2 = add_at_end(&r2, 2); // 2R + 2
                if cmp_digits(&r2p2, &thresh) == Ordering::Less {
                    0
                } else {
                    return Err(()); // 3 ∈ [2R, 2R+2]·3^-p
                }
            }
            Ordering::Equal => return Err(()),
        };
        // new value: δ=1 -> floor(2F/3); δ=0 -> 2F. doubled(F) = [carry, digits],
        // with carry=0 when δ=0 (2F < 3^g) and when δ=1 (exact div by 3).
        let buf = doubled(&self.digits);
        let newval: Vec<u8> = if delta == 1 {
            div3(&buf)[1..].to_vec()
        } else {
            buf[1..].to_vec()
        };
        // exact re-truncation check: R' from newval vs newval+2 must agree
        let rp_lo = newval[..=self.p].to_vec();
        let rp_hi = add_at_end(&newval, 2);
        let rp_hi = rp_hi[..=self.p].to_vec();
        if rp_lo != rp_hi {
            return Err(()); // truncation boundary ambiguous
        }
        self.digits = newval;
        self.len += delta as u64;
        self.n += 1;
        Ok(())
    }
}
```

- [x] **Step 4: Add `mod mantissa;` to `main.rs`** (top of `verify_middle/src/main.rs`):

```rust
mod mantissa;
mod metrics;
mod stream;
```

- [x] **Step 5: Run tests to verify they pass**

Run: `cd verify_middle && cargo test`
Expected: PASS (3 tests: stream + mantissa + metrics).

- [x] **Step 6: Commit**

```bash
git add verify_middle/src/mantissa.rs verify_middle/src/main.rs
git commit -m "feat: certified mantissa stream (step + f_scan) for first-2 positions"
```

---

### Task 2: `certified.rs` — escalation path `3^{frac(n·α)}` with interval arithmetic

**Files:**
- Create: `verify_middle/src/certified.rs`
- Modify: `verify_middle/src/main.rs` (add `mod certified;`)
- Test: inline `#[cfg(test)]` in `verify_middle/src/certified.rs`

**Interfaces:**
- Consumes: nothing (only `num_bigint::BigInt`).
- Produces:
  - `pub fn certified_ln(x: u32, p: usize) -> (BigInt, BigInt)` with `lo ≤ ln(x)·3^p ≤ hi`
  - `pub fn certified_alpha(p: usize) -> (BigInt, BigInt)` with `lo ≤ α·3^p ≤ hi`
  - `pub fn certified_pow3_interval(a: &BigInt, b: &BigInt, p: usize) -> (BigInt, BigInt)` with `lo ≤ 3^t·3^p ≤ hi` for all `t ∈ [a, b]·3⁻ᵖ ⊆ [0,1)`
  - `pub fn escalate(n: u64, p: usize) -> (Vec<u8>, u64)` — certified digits of `yₙ` (length `p + GUARDS`, `R` exact-or-one-low) and `L(n)`.

- [x] **Step 1: Write the failing test** (`verify_middle/src/certified.rs`)

```rust
use num_bigint::BigInt;

use crate::mantissa::GUARDS;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn alpha_interval_is_tight() {
        let (lo, hi) = certified_alpha(200);
        let s = BigInt::from(3u32).pow(200);
        // α = log_3 2 ≈ 0.6309 ∈ (0.5, 0.8); interval must be tight and placed.
        // certified_ln's width is ~2·need ≈ 2·(p+20) units, so bound < 1000.
        assert!(lo > BigInt::from(0u8) && lo <= hi, "bad interval");
        assert!(hi - lo < BigInt::from(1000i64), "interval too wide");
        let half = (&s * 5) / 10;
        let four_fifths = (&s * 8) / 10;
        assert!(lo < four_fifths && hi > half, "alpha interval misplaced");
    }

    #[test]
    fn escalate_matches_exact_mantissa_digits() {
        // y_n = 2^n / 3^(L(n)-1). escalate returns R ∈ {t, t-1} (exact-or-
        // one-low truncation), t = 2^n·3^(p-L+1). Verify digits against both.
        use num_bigint::BigUint;
        for n in 0u64..=12 {
            let p = 200usize;
            let (digits, len) = escalate(n, p);
            let n3 = BigUint::from(2u8).pow(n as u32);
            let l = n3.to_str_radix(3).len() as u64;
            assert_eq!(len, l, "L({n}) wrong");
            let t = n3 * BigUint::from(3u8).pow((p - l as usize + 1) as u32);
            let t = BigInt::from(t);
            let (d_t, d_tm1) = (digits_of(&t, p), digits_of(&(&t - 1), p));
            assert!(
                digits == d_t || digits == d_tm1,
                "y_{n} digits not exact-or-one-low"
            );
        }
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

    /// Certified f from an exact-or-one-low R (enclosure [R, R+1]·3^-p),
    /// mirroring Mantissa::f_scan.
    fn scan_f_enclosure(digits: &[u8], p: usize) -> Option<usize> {
        let r = &digits[..=p];
        let r1 = add_one_msb(r);
        let r1 = &r1[..=p];
        for i in 0..=p {
            let a = r[i];
            let b = r1[i];
            if a != b {
                if a == 2 || b == 2 {
                    return None;
                }
            } else if a == 2 {
                return Some(i);
            }
        }
        None
    }

    // NOTE: added during execution. The exact-path test above only covers
    // n ≤ 12; interval_path_cross_check is the only coverage of the interval
    // path (n > 1.585·(p+1)). It caught the digits_of alignment bug (f=24 vs
    // true 5 at n=400) and validated n = 10^9 via p=200 vs p=400 consistency.
    #[test]
    fn interval_path_cross_check() {
        use crate::mantissa::{DEFAULT_P, Mantissa};
        let p = DEFAULT_P;
        // 1) n in the interval-path regime (n > ~318 at p=200), vs streaming.
        let small = [400u64, 1000, 5000, 100_000];
        let mut m = Mantissa::new(p);
        let mut idx = 0usize;
        for n in 0u64..=100_000 {
            if idx < small.len() && n == small[idx] {
                let fm = match m.f_scan() {
                    Some(f) => Some(f),
                    None if (m.p as u64) >= m.len => Some(m.len as usize),
                    None => None,
                };
                let (dig, _) = escalate(n, p);
                let fe = scan_f_enclosure(&dig, p);
                assert_eq!(fe, fm, "f mismatch at n={n}");
                idx += 1;
            }
            m.step().expect("step ambiguous");
        }
        assert_eq!(idx, small.len());
        // 2) larger n: escalate at p=200 must agree with escalate at p=400.
        for n in [1_000_000u64, 10_000_000, 1_000_000_000] {
            let (d2, _) = escalate(n, 200);
            let (d4, _) = escalate(n, 400);
            let (f2, f4) = (scan_f_enclosure(&d2, 200), scan_f_enclosure(&d4, 400));
            assert_eq!(f2, f4, "f(p=200) vs f(p=400) mismatch at n={n}");
        }
    }
}
```

- [x] **Step 2: Run test to verify it fails**

Run: `cd verify_middle && cargo test`
Expected: FAIL — `certified_alpha`, `escalate` not defined.

- [x] **Step 3: Implement `certified.rs`**

```rust
use num_bigint::{BigInt, BigUint};

use crate::mantissa::GUARDS;

/// base-3 big-endian digits of v, left-aligned and zero-padded to length
/// p + GUARDS (matches `Mantissa`'s layout: reportable prefix at 0..=p).
/// Requires v < 3^(p+1).
/// NOTE: originally right-aligned (out[g-len..]); that misaligns escalate's
/// output vs Mantissa::f_scan/step/from_parts, which expect the leading digit
/// at index 0 (caught by interval_path_cross_check at n=400: f=24 vs true 5).
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

/// ln(x) ∈ [lo, hi]·3^-p for x ∈ {2, 3}, rigorous via
/// ln(x) = 2·Σ_{k≥0} t^(2k+1)/(2k+1), t = (x-1)/(x+1),
/// with the geometric tail bounded by integer division (each term ±1 unit).
pub fn certified_ln(x: u32, p: usize) -> (BigInt, BigInt) {
    let s = BigInt::from(3u32).pow(p as u32);
    let xb = BigInt::from(x);
    let xm1 = BigInt::from(x - 1);
    let xp1 = BigInt::from(x + 1);
    let t = (x - 1) as f64 / (x + 1) as f64;
    let need = (p as f64 * 3f64.ln() / (1f64 / t).ln()).ceil() as usize + 20;
    let t2n = &xm1 * &xm1;
    let t2d = &xp1 * &xp1;
    let mut num = xm1.clone(); // (x-1)^(2k+1)
    let mut den = xp1.clone(); // (x+1)^(2k+1)
    let mut lo = BigInt::from(0u8);
    let mut hi = BigInt::from(0u8);
    for k in 0..need as u64 {
        let n = 2 * &s * &num; // 2·3^p·(x-1)^(2k+1)
        let d = &den * BigInt::from(2 * k + 1);
        let q = &n / &d;
        lo += &q;
        hi += &q + 1;
        num *= &t2n;
        den *= &t2d;
    }
    // tail bound (units of 3^-p): 2·3^p·t^(2N+1)·(x+1)² / ((x+1)^(2N+1)·(2N+1)·4x)
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

/// 3^t ∈ [lo, hi]·3^-p for all t ∈ [a, b]·3^-p ⊆ [0, 1).
/// u = t·ln3 ∈ [u0, u1]; e^u = Σ u^k/k! + tail. The recurrence runs at
/// internal scale 3^(p+m) (m = 60) with separate lower/upper trackers; a
/// single rigorous geometric tail bound is added once, then one final rounding
/// to scale 3^p keeps the returned width ≤ 1 (required by `escalate`).
pub fn certified_pow3_interval(a: &BigInt, b: &BigInt, p: usize) -> (BigInt, BigInt) {
    let m: usize = 60;
    let sc = BigInt::from(3u32).pow((p + m) as u32); // internal scale
    let two_p = BigInt::from(3u32).pow(2 * p as u32);
    let (l3lo, l3hi) = certified_ln(3, p);
    let u1n = b * &l3hi; // u1 = u1n / 3^(2p), with u1 < 1.1 (t < 1, ln3 < 1.1)
    let u1d = two_p.clone();
    // K = terms needed so sc·1.1^K/K! < 1, via Stirling ln(K!) ≥ K·lnK − K.
    let log_sc = (p + m) as f64 * 3f64.ln();
    let mut K: usize = 16;
    loop {
        let kk = K as f64;
        if kk * kk.ln() - kk > log_sc + kk * 1.1f64.ln() {
            break;
        }
        K *= 2;
    }
    K += 20;
    let mut lo = sc.clone();
    let mut hi = sc.clone();
    let mut tklo = sc.clone(); // lower floor term, ≤ true T_k·sc
    let mut tkhi = sc.clone(); // upper floor term, ≥ true T_k·sc − k
    for k in 1..=K as u64 {
        let kd = BigInt::from(k as i64);
        let lo_k = &tklo * a * &l3lo / (&kd * &two_p);
        let hi_k = &tkhi * b * &l3hi / (&kd * &two_p);
        lo += &lo_k;
        hi += &hi_k;
        tklo = lo_k;
        tkhi = hi_k;
    }
    // Σ_{k≤K} true terms ≤ hi + K (each upper term < 1 off) + tail,
    // tail ≤ T_{K+1}/(1 − u1/(K+2)) ≤ tkhi·u1·(K+2)/((K+1)·(K+2−u1)).
    let kn = BigInt::from(K as i64);
    let tail_num = &tkhi * &u1n * BigInt::from((K + 2) as i64) * &u1d;
    let tail_den = (kn + 1) * &u1d * (BigInt::from((K + 2) as i64) * &u1d - &u1n);
    let tail = (&tail_num + &tail_den - 1) / &tail_den;
    let upper = &hi + &kn + &tail;
    // final rounding to scale 3^p: floor/ceil of (internal / 3^m)
    let sm = BigInt::from(3u32).pow(m as u32);
    (lo / &sm, (upper + &sm - 1) / &sm)
}

/// Certified digits of y_n = 3^{frac(n·α)} to p digits, plus L(n) = ⌊nα⌋+1.
/// Returns (digits, len); digits has length p + GUARDS with the reportable
/// prefix (first p+1 entries) an exact-or-one-low truncation of y_n.
/// Recurses with doubled precision when the certified interval is too wide
/// or n·α straddles an integer.
///
/// NOTE (final design, supersedes the naive recursion below): the naive
/// recursion computed n·α at scale p only, whose certified interval width
/// (~3.4·p units) is CONSTANT in p after the floor divide — so for any n with
/// L(n) ≤ p+1 (y_n·3^p = 2^n·3^(p-L+1) an integer divisible by 3^q) the
/// interval always straddles the down-conversion boundary and the recursion
/// never terminates (observed hang for n = 1, 2). Two fixes:
///   1. EXACT PATH when L(n) ≤ p+1 (n ≤ 1.585·(p+1), 2^n < 3^(p+1)):
///      compute 2^n exactly via BigUint, l = ternary digit count,
///      return digits_of(2^n·3^(p-l+1)) — no interval arithmetic.
///   2. INTERVAL PATH for larger n: compute α at p_hi = p + 64 (width ≈
///      3.4·p_hi units at its own scale, resolving n·α to sub-unit precision
///      at scale 3^p for n up to ~10^40), 3^frac interval via
///      certified_pow3_interval at scale p_hi, then down-convert once by
///      /3^64 (straddle probability ≈ W/3^64 ≈ 0 for n ≤ 10^9). Recursion
///      only as a safety net.
pub fn escalate(n: u64, p: usize) -> (Vec<u8>, u64) {
    let small_limit = (p + 1) as f64 * 1.585;
    if (n as f64) <= small_limit {
        let two_n = BigUint::from(2u8).pow(n as u32);
        let l = two_n.to_str_radix(3).len() as u64;
        let t = two_n * BigUint::from(3u8).pow((p - l as usize + 1) as u32);
        return (digits_of(&BigInt::from(t), p), l);
    }
    let p_hi = p + 64;
    let s_hi = BigInt::from(3u32).pow(p_hi as u32);
    let (alo, ahi) = certified_alpha(p_hi);
    let nb = BigInt::from(n);
    let nlo = &nb * &alo;
    let nhi = &nb * &ahi;
    let flo = &nlo / &s_hi;
    let fhi = &nhi / &s_hi;
    if &flo != &fhi {
        return escalate(n, p * 2);
    }
    let k = flo;
    let len = k.to_str_radix(10).parse::<u64>().unwrap() + 1;
    let kp = &k * &s_hi;
    let a = &nlo - &kp; // ≥ 0 and < 3^p_hi (since flo == fhi)
    let b = &nhi - &kp;
    let (ylo, yhi) = certified_pow3_interval(&a, &b, p_hi);
    // down-convert the 3^frac interval to scale 3^p (width ≤ 1)
    let sm = BigInt::from(3u32).pow(64u32);
    let ylo_p = &ylo / &sm;
    let yhi_p = (&yhi + &sm - 1) / &sm;
    if &yhi_p - &ylo_p > BigInt::from(1u8) {
        return escalate(n, p * 2);
    }
    let digits = digits_of(&ylo_p, p);
    (digits, len)
}
```

- [x] **Step 4: Add `mod certified;` to `main.rs`**

```rust
mod certified;
mod mantissa;
mod metrics;
mod stream;
```

- [x] **Step 5: Run tests to verify they pass**

Run: `cd verify_middle && cargo test`
Expected: PASS (6 tests). The `escalate_matches_exact_mantissa_digits` test must verify digits 0..29 of `yₙ` for n ≤ 12 against `2ⁿ`'s base-3 digits; `interval_path_cross_check` must match the streaming f for n = 400/1000/5000/100000 and agree across p=200 vs p=400 for n = 10⁶/10⁷/10⁹.

- [x] **Step 6: Commit**

```bash
git add verify_middle/src/certified.rs verify_middle/src/main.rs
git commit -m "feat: certified escalation path via 3^frac(n*alpha) interval arithmetic"
```

---

### Task 3: `--first2` records mode

**Files:**
- Modify: `verify_middle/src/main.rs`

**Interfaces:**
- Consumes: `Mantissa::f_scan/step` (Task 1), `escalate` (Task 2).
- Produces: CLI `verify_middle --first2 N out.csv` writing the records CSV with columns `n,f,L,ratio,prefix,mantissa_precision,record_number,gap_from_previous_record`; prints record summary to stdout.

- [x] **Step 1: Add the driver loops** to `verify_middle/src/main.rs`

```rust
use certified::escalate;
use mantissa::{Mantissa, DEFAULT_P};

/// Certified f(n), escalating when the first-2 is beyond the reportable window.
fn certified_f(m: &mut Mantissa) -> usize {
    loop {
        if let Some(f) = m.f_scan() {
            return f;
        }
        if (m.p as u64) >= m.len {
            return m.len as usize;
        }
        let (digits, len) = escalate(m.n, m.p * 4);
        *m = Mantissa::from_parts(m.n, m.p * 4, digits, len);
    }
}

/// Advance n -> n+1, escalating until the step is certified.
fn advance(m: &mut Mantissa) {
    loop {
        if m.step().is_ok() {
            return;
        }
        let (digits, len) = escalate(m.n, m.p * 4);
        *m = Mantissa::from_parts(m.n, m.p * 4, digits, len);
    }
}

fn first2(nmax: u64, out_path: &str) {
    let mut m = Mantissa::new(DEFAULT_P);
    let mut w = BufWriter::new(File::create(out_path).expect("create csv"));
    writeln!(
        w,
        "n,f,L,ratio,prefix,mantissa_precision,record_number,gap_from_previous_record"
    )
    .unwrap();
    let mut max_f = 0usize;
    let mut record_count = 0usize;
    let mut prev: Option<u64> = None;
    loop {
        let n = m.n;
        if n > nmax {
            break;
        }
        let f = certified_f(&mut m);
        if f > max_f {
            max_f = f;
            record_count += 1;
            let gap = n - prev.unwrap_or(0);
            let prefix: String = m.digits[..f].iter().map(|&d| (b'0' + d) as char).collect();
            let ratio = f as f64 / m.len as f64;
            writeln!(
                w,
                "{n},{f},{},{ratio:.10},{prefix},{},{record_count},{gap}",
                m.len, m.p
            )
            .unwrap();
            prev = Some(n);
        }
        advance(&mut m);
        if n % 10_000_000 == 0 {
            eprintln!("n={n} max_f={max_f} p={}", m.p);
        }
    }
    println!("== first-2 records: count={record_count} max_f={max_f} ==");
}
```

- [x] **Step 2: Wire `--first2` into `main`**

```rust
        Some("--first2") => {
            let n: u64 = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(1_000_000_000);
            let out = args.get(3).cloned().unwrap_or_else(|| "first2_records.csv".to_string());
            first2(n, &out);
        }
```

- [x] **Step 3: Build and run on a small range**

Run: `cd verify_middle && cargo build --release`
Run: `./target/release/verify_middle --first2 2000 /tmp/f2_small.csv`
Expected: prints `== first-2 records: count=... max_f=... ==`; the CSV's first rows include `0,1,1,...` (n=0, f=1, prefix `1`), `2,2,2,...` (n=2, f=2, prefix `11`), `8,6,6,...` (n=8, f=6, prefix `100111`).

- [x] **Step 4: Spot-check every record against `exact_f`** (`python3 - <<'EOF'`)

```python
import csv, math
rows = list(csv.DictReader(open('/tmp/f2_small.csv')))
def f_exact(n):
    d = []
    x = pow(2, n)
    while x:
        d.append(x % 3); x //= 3
    for j, v in enumerate(reversed(d)):
        if v == 2: return j
    return len(d)
for r in rows:
    n = int(r['n']); f = int(r['f'])
    assert f == f_exact(n), (n, f)
    assert int(r['L']) == math.floor(n*math.log(2)/math.log(3)) + 1, n
print("records spot-checked ok:", len(rows))
```
Expected: prints `records spot-checked ok: N` with no assertion error.

- [x] **Step 5: Commit**

```bash
git add verify_middle/src/main.rs
git commit -m "feat: --first2 certified first-2-position records mode"
```

---

### Task 4: Validation layer 1 — mantissa stream vs exact digits (n ≤ 10⁵, plus escalation stress)

**Files:**
- Modify: `verify_middle/src/main.rs` (add `--first2-check`)

**Interfaces:**
- Consumes: `certified_f`, `advance` (Task 3), `Stream`, `exact_f`.
- Produces: CLI `verify_middle --first2-check NMAX [p]` that asserts the mantissa-derived `f(n)` equals the exact digit-stream `f(n)` for every n ≤ NMAX.

- [x] **Step 1: Add `first2_check`**

```rust
use mantissa::exact_f;

fn first2_check(nmax: u64, p: usize) {
    let mut m = Mantissa::new(p);
    let mut s = Stream::new();
    for n in 0..=nmax {
        let fex = exact_f(&s.digits);
        let fm = certified_f(&mut m);
        assert_eq!(fm, fex, "f mismatch at n={n}");
        advance(&mut m);
        s.double();
        if n % 20_000 == 0 {
            eprintln!("check n={n} p={}", m.p);
        }
    }
    println!("first2-check ok through n={nmax} at p={p}");
}
```

Wire into `main`:

```rust
        Some("--first2-check") => {
            let n: u64 = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100_000);
            let p: usize = args.get(3).and_then(|s| s.parse().ok()).unwrap_or(DEFAULT_P);
            first2_check(n, p);
        }
```

- [x] **Step 2: Run the main check (p = 200, n ≤ 10⁵)**

Run: `cd verify_middle && cargo run --release -- --first2-check 100000 200`
Expected: prints `first2-check ok through n=100000 at p=200`.

- [x] **Step 3: Run the escalation stress check (tiny precision)**

Run: `./target/release/verify_middle --first2-check 2000 2`
Expected: prints `first2-check ok through n=2000 at p=2`. This forces δ-ambiguity and truncation-boundary escalations at nearly every step, exercising the certified escalation path heavily. (Any visible `p=` progress lines rising above 2 confirm escalation fired.)

- [x] **Step 4: Run a medium-precision stress check**

Run: `./target/release/verify_middle --first2-check 20000 6`
Expected: prints `first2-check ok through n=20000 at p=6`.

- [x] **Step 5: Commit**

```bash
git add verify_middle/src/main.rs
git commit -m "test: validate mantissa f(n) against exact digit stream (incl. escalation stress)"
```

---

### Task 5: Validation layer 2 — `P(f ≥ L)` vs `events_m1.csv` `P(A_L)`

**Files:**
- Modify: `verify_middle/src/main.rs` (add `--first2-events`)
- Create: `verify_middle/first2_events_compare.py`

**Interfaces:**
- Consumes: `certified_f`, `advance`; `verify_middle/events_m1.csv` (Phase 7).
- Produces: CLI `verify_middle --first2-events N out.csv L1,L2,..` writing `L,N,P_f_ge_L`; `first2_events_compare.py` compares `P(f ≥ L)` against the `P(A_L)` marginals (K=1 rows) of `events_m1.csv`.

- [x] **Step 1: Add `first2_events`**

```rust
fn first2_events(nmax: u64, out_path: &str, grid: &[usize]) {
    let lmax = *grid.iter().max().unwrap();
    let mut m = Mantissa::new(DEFAULT_P);
    let mut cnt = vec![0usize; lmax + 1];
    let mut ncnt = vec![0usize; lmax + 1];
    loop {
        let n = m.n;
        if n > nmax {
            break;
        }
        if n >= 9 {
            let f = certified_f(&mut m);
            let len = m.len as usize;
            for &l in grid {
                if l <= len {
                    ncnt[l] += 1;
                    if f >= l {
                        cnt[l] += 1;
                    }
                }
            }
        }
        advance(&mut m);
    }
    let mut w = BufWriter::new(File::create(out_path).expect("create csv"));
    writeln!(w, "L,N,P_f_ge_L").unwrap();
    for &l in grid {
        let p = cnt[l] as f64 / ncnt[l] as f64;
        writeln!(w, "{l},{},{p:.6}", ncnt[l]).unwrap();
    }
    println!("first2-events done through n={nmax}");
}
```

Wire into `main` (same grid default as the Phase 7 events mode):

```rust
        Some("--first2-events") => {
            let n: u64 = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(1_000_000);
            let out = args.get(3).cloned().unwrap_or_else(|| "first2_events.csv".to_string());
            let grid: Vec<usize> = args
                .get(4)
                .map(|g| g.split(',').filter_map(|x| x.parse().ok()).collect())
                .unwrap_or_else(|| vec![1, 2, 3, 4, 5, 6, 8, 10, 12, 16, 20, 24, 30]);
            first2_events(n, &out, &grid);
        }
```

- [x] **Step 2: Run to 10⁶**

Run: `cd verify_middle && ./target/release/verify_middle --first2-events 1000000 /tmp/f2_events.csv`
Expected: prints `first2-events done through n=1000000`.

- [x] **Step 3: Write the comparison script** (`verify_middle/first2_events_compare.py`)

```python
import csv
import math
import sys

events = {}
with open("verify_middle/events_m1.csv") as f:
    for r in csv.DictReader(f):
        if r["K"] == "1":
            events[int(r["L"])] = (int(r["N"]), float(r["P_A"]))

rows = list(csv.DictReader(open(sys.argv[1])))
bad = 0
for r in rows:
    l = int(r["L"])
    p = float(r["P_f_ge_L"])
    if l not in events:
        continue
    n, pa = events[l]
    se = math.sqrt(pa * (1 - pa) / n) if n else 0.0
    z = (p - pa) / se if se > 0 else 0.0
    print(f"L={l:2d} P(f>=L)={p:.6f} P(A_L)={pa:.6f} z={z:+.2f} (N={n})")
    if abs(z) > 3.5:
        bad += 1
print("cells with |z|>3.5:", bad)
```

- [x] **Step 4: Run the comparison**

Run: `python3 verify_middle/first2_events_compare.py /tmp/f2_events.csv`
Expected: `P(f ≥ L)` within sampling error of `P(A_L)` for every grid L (≈ 1–2 cells with |z|>1.96 out of 13, zero cells with |z|>3.5), consistent with the Phase 7 finding that leading digits are Benford-like.

- [x] **Step 5: Commit**

```bash
git add verify_middle/src/main.rs verify_middle/first2_events_compare.py
git commit -m "test: validate P(f>=L) distribution vs Phase 7 events P(A_L)"
```

---

### Task 6: Validation layer 3 — independent re-verification of every record

**Files:**
- Modify: `verify_middle/src/main.rs` (add `--first2-verify-records`)

**Interfaces:**
- Consumes: `escalate`, `certified_f`.
- Produces: CLI `verify_middle --first2-verify-records out.csv` that re-derives `f(n)` for every record-holder purely from `3^{frac(n·α)}` (no stream state) and asserts it matches the recorded value.

- [x] **Step 1: Add `verify_records`** (no CSV crate — split lines; no field contains a comma)

```rust
fn verify_records(path: &str) {
    let data = std::fs::read_to_string(path).expect("read csv");
    let mut lines = data.lines();
    let _header = lines.next();
    let mut verified = 0usize;
    for line in lines {
        let parts: Vec<&str> = line.split(',').collect();
        let n: u64 = parts[0].parse().unwrap();
        let f: usize = parts[1].parse().unwrap();
        let (digits, len) = escalate(n, DEFAULT_P);
        let mut m = Mantissa::from_parts(n, DEFAULT_P, digits, len);
        let fv = certified_f(&mut m);
        assert_eq!(fv, f, "record n={n} failed independent verification");
        verified += 1;
    }
    println!("verified {verified} records independently via 3^frac(n*alpha)");
}
```

Wire into `main`:

```rust
        Some("--first2-verify-records") => {
            let p = args.get(2).cloned().unwrap_or_else(|| "first2_records.csv".to_string());
            verify_records(&p);
        }
```

- [x] **Step 2: Run against the small records file**

Run: `cd verify_middle && ./target/release/verify_middle --first2-verify-records /tmp/f2_small.csv`
Expected: prints `verified N records independently via 3^frac(n*alpha)` (includes n=0, 2, 8).

- [x] **Step 3: Commit**

```bash
git add verify_middle/src/main.rs
git commit -m "test: independently re-verify record-holders via certified 3^frac(n*alpha)"
```

---

### Task 7: Full 10⁹ run, records/ratio analysis, findings, ROADMAP

**Files:**
- Create: `verify_middle/first2_analysis.py`
- Create: `verify_middle/PHASE8_FINDINGS.md`
- Modify: `ROADMAP.md`

**Interfaces:**
- Consumes: `verify_middle/first2_records.csv` (Task 3 output).
- Produces: `PHASE8_FINDINGS.md` with the records table, gap structure, `f(n)/L(n)` ratio analysis, and a Phase 8 conjecture; updated ROADMAP.

- [x] **Step 1: Run the full 10⁹ run**

Run: `cd verify_middle && time ./target/release/verify_middle --first2 1000000000 first2_records.csv`
Expected: completes with `== first-2 records: count=... max_f=... ==`. Timing gate: if wall time exceeds ~30 min, record the measured time and the max `p` reached in the commit body and in `PHASE8_FINDINGS.md` (optimization deferred, as in Phase 7). Expected shape: ~51 records (from `(2/3)^f·10⁹ ≈ 1`), `f` growing roughly like `log_{3/2} n ≈ 2.7·log₃ n`, `ratio = f/L ≈ 10⁻⁷`.

- [x] **Step 2: Verify records independently**

Run: `cd verify_middle && ./target/release/verify_middle --first2-verify-records first2_records.csv`
Expected: prints `verified N records independently ...` (all of them).

- [x] **Step 3: Write the analysis script** (`verify_middle/first2_analysis.py`, stdlib only)

```python
import csv
import math

rows = list(csv.DictReader(open("verify_middle/first2_records.csv")))
ns = [int(r["n"]) for r in rows]
fs = [int(r["f"]) for r in rows]
gaps = [int(r["gap_from_previous_record"]) for r in rows]
ratios = [float(r["ratio"]) for r in rows]

print(f"records: {len(rows)}")
print("n      f  L/1e6  ratio      gap   prefix")
for r in rows:
    print(f"{int(r['n']):<7d} {int(r['f']):<3d} {int(r['L'])/1e6:7.3f} {float(r['ratio']):.3e} {int(r['gap']):<6d} {r['prefix']}")

# growth fit: f vs log_{3/2}(n), least squares slope + intercept
def ls(xs, ys):
    n = len(xs)
    mx, my = sum(xs) / n, sum(ys) / n
    num = sum((x - mx) * (y - my) for x, y in zip(xs, ys))
    den = sum((x - mx) ** 2 for x in xs)
    return num / den, my - (num / den) * mx

lg = [math.log(n) / math.log(1.5) for n in ns]
slope, intercept = ls(lg, fs)
print(f"f ~ {slope:.3f} * log_(3/2)(n) + {intercept:.2f}")
print(f"max ratio f/L = {max(ratios):.3e} at n={ns[ratios.index(max(ratios))]}")
print(f"max gap = {max(gaps)} at n={ns[gaps.index(max(gaps))]}")
```

- [x] **Step 4: Run the analysis**

Run: `python3 verify_middle/first2_analysis.py`
Expected: records table printed; slope ≈ 1 (records follow `f ≈ log_{3/2} n`), intercept small, max ratio ≈ 10⁻⁷, max gap on the order of 10⁹.

- [x] **Step 5: Write `verify_middle/PHASE8_FINDINGS.md`** (real numbers from the run — do NOT invent)

Include:
- the records table (n, f, L, ratio, gap) and `max_f`, record count;
- the `f/L` ratio analysis (decay rate, max);
- the growth-rate fit (slope vs `log_{3/2} n`) and **one new conjecture**, e.g. `f(n) ≤ C·log₃ n` for all n with an estimated constant `C` from the fit, or a gap-structure statement;
- the timing and max `p` reached; confirmation that all records passed the independent `3^{frac(n·α)}` verification.

- [x] **Step 6: Update `ROADMAP.md`** (Phase 8 section)

Mark the Phase 8 deliverables done: fast certified f(n) to 10⁹, record table + gap analysis + growth conjecture, `f(n)/L(n)` ratio data, link to the potential theorem `f(n) ≤ C·log₃ n`. Note Phase 8 M3/Lean work remains out of scope.

- [x] **Step 7: Commit**

```bash
git add verify_middle/first2_records.csv verify_middle/first2_analysis.py verify_middle/PHASE8_FINDINGS.md ROADMAP.md
git commit -m "data: certified first-2 records to n=10^9, analysis, findings, roadmap"
```

---

## Out of Scope (later plans)

- Phase 8 gap-structure deep-dive and a proven `f(n) ≤ C·log₃ n` theorem.
- Phase 9 two-sided search (uses these records).
- Phase 7 M3 Lean formalization of the base-3 doubling transducer.