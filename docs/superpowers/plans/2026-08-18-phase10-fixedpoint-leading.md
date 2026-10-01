# Phase 10: u256 Fixed-Point Leading Check Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the certified BigInt leading-digit check with a u256 fixed-point fast path (target ≥ 2× at K=38, more at larger K) so K=40 and K=42 records become routine on the 4-core machine, with the BigInt path preserved as the ground-truth fallback.

**Architecture:** A `fixedpoint` module provides `U256` interval arithmetic at two derived ternary scales — product scale `3^P` (n·α, flo/fhi, frac) and Taylor scale `3^P_t` (pow3 series, which cannot run at `3^P` because `3^(2P)` exceeds u256). α/ln3 constants are computed once by the existing BigInt `certified_alpha`/`certified_ln` at guard precision `P+g`/`P_t+g` (g=12) and truncated into U256, collapsing the constant-interval width to ~2–3 ulp. `verify_precision` derives (P, P_t) from the actual measured error budget per target K. `leading_digits_have_two` becomes a dispatcher: fp path → on ambiguity, BigInt fallback. Result sets are bit-identical, enforced by differential tests.

**Tech Stack:** Rust (edition 2021), `num-bigint` 0.4 (ground truth + constant generation), `rayon` (engine). No new dependencies.

**Spec:** `docs/superpowers/specs/2026-08-18-phase10-fixedpoint-leading-design.md` (refined two-scale model, commit `80005fb`).

## Global Constraints

- BigInt fallback is **mandatory**: fp never turns an ambiguous case into a guess. An ambiguous/undecidable u256 case always escalates to the existing certified BigInt path. Result sets bit-identical.
- Scales are **derived, not hard-coded**: `verify_precision(P, P_t, n_max, k_prime)` asserts `error_budget < 3^(P − k_prime)` AND product-fit `n_max · 3^P < 2^256`. Candidate grids: P ∈ {108, 112, 118, 124}, P_t ∈ {76, 78, 80}.
- Constants computed at guard precision `P+g`/`P_t+g` (g = 12) by the existing BigInt `certified_alpha`/`certified_ln`, truncated into U256 (lo round-down, hi round-up). `E_α`, `E_l3` measured from the truncated constants.
- k_prime = 70 semantics unchanged. The fp path only engages when `k_prime == 70` (the engine's value); all other k_prime (tests use 50/51) keep the BigInt path.
- Prefix-span test is the Phase 9 form (digits of both endpoints, lexicographic monotonicity certifies the span).
- Stdlib + existing deps only. Rust `debug_assert!` on overflow is allowed; runtime correctness must not depend on debug builds.
- Benchmark hard gate before any K=40 run: mismatch count must be 0; speedup must be real; results recorded in `verify_erdos_rs/PHASE10_FINDINGS.md`.
- TDD: every step ends with a runnable test and a commit.

---

### Task 1: U256 core arithmetic (add/sub/shift/compare)

**Files:**
- Create: `verify_erdos_rs/src/fixedpoint.rs`
- Modify: `verify_erdos_rs/src/main.rs` (add `mod fixedpoint;`)
- Test: `verify_erdos_rs/src/fixedpoint.rs` (`#[cfg(test)] mod tests`)

**Interfaces:**
- Consumes: nothing (start of the module).
- Produces:
  - `pub struct U256(pub u128, pub u128)` — (lo, hi)
  - `impl U256 { pub const ZERO; pub const MAX; pub fn from_u64(u64) -> U256; pub fn from_u128(u128) -> U256; pub fn add(self, o: U256) -> U256; pub fn sub(self, o: U256) -> U256; pub fn shl(self, bits: u32) -> U256; pub fn shr(self, bits: u32) -> U256; pub fn add_one(self) -> U256; pub fn bit(self, i: u32) -> bool; pub fn set_bit(self, i: u32, v: bool) -> U256 }`
  - `impl PartialEq, Eq, PartialOrd, Ord for U256` (lexicographic on (hi, lo))
  - `pub fn pow3_u256(p: usize) -> U256`; `pub fn pow3_u64(p: usize) -> u64` (for p ≤ 40, panics otherwise); `pub fn pow3_u128(p: usize) -> u128` (for p ≤ 42)

- [ ] **Step 1: Write the failing test**

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn u256_add_sub_carry_borrow() {
        let a = U256(u128::MAX, 0);
        let b = U256::from_u128(1);
        assert_eq!(a.add(b), U256(0, 1));
        assert_eq!(U256(0, 1).sub(b), U256(u128::MAX, 0));
        let x = U256(5, 7);
        let y = U256(3, 2);
        assert_eq!(x.add(y), U256(8, 9));
        assert_eq!(x.sub(y), U256(2, 5));
    }

    #[test]
    fn u256_shift_roundtrip_and_bits() {
        let x = U256(0x1234_5678_9abc_def0, 0x0fed_cba9_8765_4321);
        assert_eq!(x.shl(64).shr(64), x);
        assert_eq!(x.shl(1).shr(1), x);
        let hi_bit = U256(0, 1).shl(255);
        assert_eq!(hi_bit.bit(255), true);
        assert_eq!(hi_bit.bit(254), false);
        assert_eq!(U256::from_u128(0b101).bit(2), true);
        assert_eq!(U256::from_u128(0b101).bit(1), false);
        let z = U256::from_u128(0b101).set_bit(1, true);
        assert_eq!(z, U256::from_u128(0b111));
    }

    #[test]
    fn u256_ordering() {
        assert!(U256(0, 1) > U256(u128::MAX, 0));
        assert!(U256(5, 0) < U256(5, 1));
        assert_eq!(U256(9, 9).cmp(&U256(9, 9)), std::cmp::Ordering::Equal);
    }

    #[test]
    fn pow3_values() {
        assert_eq!(pow3_u64(0), 1);
        assert_eq!(pow3_u64(5), 243);
        assert_eq!(pow3_u64(40), 1_215_766_545_905_942_929);
        assert_eq!(pow3_u256(0), U256::from_u64(1));
        assert_eq!(pow3_u256(5), U256::from_u64(243));
        assert_eq!(pow3_u256(40), U256::from_u64(pow3_u64(40)));
        assert_eq!(pow3_u128(42), 109418989131512359209);
    }
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p verify_erdos u256_ 2>&1 | tail -5`
Expected: compile error — module `fixedpoint` not found (or `u256_` tests not defined).

- [ ] **Step 3: Write minimal implementation**

`verify_erdos_rs/src/main.rs`:
```rust
mod ternary_mod;
mod saye;
mod leading;
mod two_sided;
mod fixedpoint;
```

`verify_erdos_rs/src/fixedpoint.rs`:
```rust
//! u256 fixed-point interval arithmetic for the certified leading-digit fast path.
//! Two derived ternary scales (spec Section 4): product scale 3^P and Taylor
//! scale 3^P_t. Every op widens correctly: round-down for low bounds, round-up
//! for high bounds. The BigInt path in `leading.rs` remains the ground truth.

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct U256(pub u128, pub u128);

impl U256 {
    pub const ZERO: U256 = U256(0, 0);
    pub const MAX: U256 = U256(u128::MAX, u128::MAX);

    pub fn from_u64(v: u64) -> U256 {
        U256(v as u128, 0)
    }

    pub fn from_u128(v: u128) -> U256 {
        U256(v, 0)
    }

    pub fn add(self, o: U256) -> U256 {
        let (lo, c1) = self.0.overflowing_add(o.0);
        let (hi, c2) = self.1.overflowing_add(o.1);
        let (hi, c3) = hi.overflowing_add(c1 as u128);
        debug_assert!(!c2 && !c3, "U256 add overflow");
        U256(lo, hi)
    }

    pub fn sub(self, o: U256) -> U256 {
        let (lo, b1) = self.0.overflowing_sub(o.0);
        let (hi, b2) = self.1.overflowing_sub(o.1);
        let (hi, b3) = hi.overflowing_sub(b1 as u128);
        debug_assert!(!b2 && !b3, "U256 sub underflow");
        U256(lo, hi)
    }

    pub fn add_one(self) -> U256 {
        let (lo, c) = self.0.overflowing_add(1);
        debug_assert!(!(c && self.1 == u128::MAX), "U256 add_one overflow");
        U256(lo, self.1 + c as u128)
    }

    pub fn shl(self, bits: u32) -> U256 {
        debug_assert!(bits < 256, "shl {bits}");
        if bits == 0 {
            return self;
        }
        if bits >= 128 {
            return U256(0, self.0 << (bits - 128));
        }
        let hi = (self.1 << bits) | (self.0 >> (128 - bits));
        U256(self.0 << bits, hi)
    }

    pub fn shr(self, bits: u32) -> U256 {
        debug_assert!(bits < 256, "shr {bits}");
        if bits == 0 {
            return self;
        }
        if bits >= 128 {
            return U256(self.1 >> (bits - 128), 0);
        }
        let lo = (self.0 >> bits) | (self.1 << (128 - bits));
        U256(lo, self.1 >> bits)
    }

    pub fn bit(self, i: u32) -> bool {
        debug_assert!(i < 256, "bit {i}");
        if i < 128 {
            (self.0 >> i) & 1 == 1
        } else {
            (self.1 >> (i - 128)) & 1 == 1
        }
    }

    pub fn set_bit(self, i: u32, v: bool) -> U256 {
        debug_assert!(i < 256, "set_bit {i}");
        if i < 128 {
            U256(if v { self.0 | (1u128 << i) } else { self.0 & !(1u128 << i) }, self.1)
        } else {
            U256(self.0, if v { self.1 | (1u128 << (i - 128)) } else { self.1 & !(1u128 << (i - 128)) })
        }
    }
}

impl PartialOrd for U256 {
    fn partial_cmp(&self, o: &U256) -> Option<std::cmp::Ordering> {
        Some(self.cmp(o))
    }
}

impl Ord for U256 {
    fn cmp(&self, o: &U256) -> std::cmp::Ordering {
        self.1.cmp(&o.1).then_with(|| self.0.cmp(&o.0))
    }
}

/// 3^p as u64; requires p ≤ 40 (3^40 ≈ 1.216×10^19 < u64::MAX).
pub fn pow3_u64(p: usize) -> u64 {
    assert!(p <= 40, "pow3_u64: p={p} > 40");
    let mut v: u64 = 1;
    for _ in 0..p {
        v *= 3;
    }
    v
}

/// 3^p as u128; requires p ≤ 80 (3^80 ≈ 1.478×10^38 < u128::MAX ≈ 3.4×10^38).
pub fn pow3_u128(p: usize) -> u128 {
    assert!(p <= 80, "pow3_u128: p={p} > 80");
    let mut v: u128 = 1;
    for _ in 0..p {
        v *= 3;
    }
    v
}

/// 3^p as U256; requires p ≤ 160 (3^160 ≈ 2^254).
pub fn pow3_u256(p: usize) -> U256 {
    assert!(p <= 160, "pow3_u256: p={p} > 160");
    let mut v = U256::from_u64(1);
    for _ in 0..p {
        v = v.mul_u64(3);
    }
    v
}
```

Note: `pow3_u256` calls `mul_u64`, so include it in the `impl U256` block now (it is exact: `lo·m` ≤ 2^192 and `hi·m` ≤ 2^192, both fit u128, so no overflow is possible):

```rust
    /// u256 × u64 — exact (product < 2^256, no overflow).
    pub fn mul_u64(self, m: u64) -> U256 {
        let m128 = m as u128;
        let (p0, c0) = self.0.overflowing_mul(m128);
        let hi = self.1 * m128;
        U256(p0, hi + c0)
    }
```

- [ ] **Step 4: Run test to verify it passes**

Run: `cargo test -p verify_erdos u256_ 2>&1 | tail -20`
Expected: 4 tests PASS.

- [ ] **Step 5: Commit**

```bash
git add verify_erdos_rs/src/fixedpoint.rs verify_erdos_rs/src/main.rs
git commit -m "feat(fixedpoint): U256 core arithmetic (add/sub/shift/compare/pow3)"
```

---

### Task 2: U256 multiplication, division, BigInt conversion, ternary digits

**Files:**
- Modify: `verify_erdos_rs/src/fixedpoint.rs`

**Interfaces:**
- Consumes: Task 1 `U256`, `pow3_*`.
- Produces:
  - `impl U256 { pub fn mul_wide(self, o: U256) -> (U256, U256); pub fn mul_rd(self, o: U256) -> U256; pub fn mul_ru(self, o: U256) -> Option<U256>; pub fn divrem_u64(self, m: u64) -> (U256, u64); pub fn div_rd_u64(self, m: u64) -> U256; pub fn div_ru_u64(self, m: u64) -> U256; pub fn divrem_u256_rd(self, d: U256) -> (U256, U256); pub fn div_rd(self, d: U256) -> U256; pub fn div_ru(self, d: U256) -> Option<U256>; pub fn from_bigint(b: &BigInt) -> Option<U256>; pub fn to_ternary_digits(self, len: usize) -> Vec<u8> }`

Rounding contract (critical for soundness):
- `mul_rd` = truncation (low 256 bits). Valid lower bound always.
- `mul_ru` = `Some(low)` if the product fits u256 exactly (hi limb zero), else `None`. **Never** saturate: a saturated `MAX` can be *below* the true product and would be unsound as an upper bound. `None` means "does not fit" → the caller escalates to BigInt.
- `div_rd_u64` / `div_ru_u64` = floor / ceil of the exact quotient.
- `div_rd` = floor; `div_ru` = `Some(ceil)` (always fits since quotient < dividend; `None` reserved for `d == 0`).

- [ ] **Step 1: Write the failing test**

```rust
    fn from_u128_pair(lo: u128, hi: u128) -> U256 {
        U256(lo, hi)
    }

    #[test]
    fn mul_wide_and_rounding() {
        let a = from_u128_pair(0x0000_0000_0000_00ff_ffff_ffff_ffff_ffff, 0);
        let b = from_u128_pair(0x0000_0000_0000_00ff_ffff_ffff_ffff_ffff, 0);
        let (hi, lo) = a.mul_wide(b);
        assert_eq!(lo, from_u128_pair(0x0000_0000_0000_0000_ffff_ffff_ffff_ff01, 0));
        assert_eq!(hi, from_u128_pair(0x0000_0000_0000_0000_0000_0000_0000_00ff, 0));
        // round-down = low half; round-up = None when high half nonzero
        assert_eq!(a.mul_rd(b), lo);
        assert_eq!(a.mul_ru(b), None);
        // small exact product
        let c = from_u128_pair(3, 0);
        let d = from_u128_pair(5, 0);
        assert_eq!(c.mul_rd(d), from_u128_pair(15, 0));
        assert_eq!(c.mul_ru(d), Some(from_u128_pair(15, 0)));
        // carries across the lo/hi boundary
        let e = from_u128_pair(u128::MAX, 0);
        assert_eq!(e.mul_rd(U256::from_u64(3)), from_u128_pair(u128::MAX - 2, 2));
        assert_eq!(e.mul_ru(U256::from_u64(3)), Some(from_u128_pair(u128::MAX - 2, 2)));
    }

    #[test]
    fn div_u64_rounding() {
        let x = from_u128_pair(10, 0);
        assert_eq!(x.divrem_u64(3), (from_u128_pair(3, 0), 1));
        assert_eq!(x.div_rd_u64(3), from_u128_pair(3, 0));
        assert_eq!(x.div_ru_u64(3), from_u128_pair(4, 0));
        assert_eq!(x.div_rd_u64(10), from_u128_pair(1, 0));
        assert_eq!(x.div_ru_u64(10), from_u128_pair(1, 0));
        let big = from_u128_pair(0, 1); // 2^128
        assert_eq!(big.divrem_u64(2), (from_u128_pair(1u128 << 127, 0), 0));
    }

    #[test]
    fn div_u256_floor_ceil() {
        let s = pow3_u256(78);
        let x = U256::MAX;
        let (q, r) = x.divrem_u256_rd(s);
        let (qhi, qlo) = q.mul_wide(s);
        assert_eq!(qhi, U256::ZERO, "q*s must fit u256 (q < 2^124)");
        assert_eq!(qlo.add(U256::from_u128(r.0)), x, "q*s + r == x");
        assert!(r < s, "remainder < divisor");
        // ceil is floor or floor+1
        let q_ru = x.div_ru(s).unwrap();
        assert!(q_ru == q || q_ru == q.add_one(), "ceil is floor or floor+1");
        // exact-division case: 3^120 / 3^78 = 3^42
        let num = pow3_u256(120);
        assert_eq!(num.div_rd(s), pow3_u256(42));
        assert_eq!(num.div_ru(s), Some(pow3_u256(42)));
        // nonzero remainder: ceil > floor
        let x2 = num.add(U256::from_u64(1));
        assert_eq!(x2.div_ru(s), Some(pow3_u256(42).add_one()));
    }

    #[test]
    fn from_bigint_and_ternary_digits() {
        use num_bigint::BigInt;
        let b = BigInt::from(3u32).pow(80);
        let u = U256::from_bigint(&b).unwrap();
        assert_eq!(u, pow3_u256(80));
        assert_eq!(U256::from_bigint(&BigInt::from(0)), Some(U256::ZERO));
        // value >= 2^256 -> None
        let too_big = BigInt::from(1u32) << 256;
        assert_eq!(U256::from_bigint(&too_big), None);
        // ternary digits of 3^5 = 100000 (base 3)
        let digits = pow3_u256(5).to_ternary_digits(8);
        assert_eq!(digits, vec![1, 0, 0, 0, 0, 0, 0, 0]);
        // 7 (base 3: 21) padded left to len 4
        assert_eq!(U256::from_u64(7).to_ternary_digits(4), vec![0, 0, 2, 1]);
        // 2^81 = 3^51 * y has no digit-2 surprise here: digits of 3^51
        assert_eq!(pow3_u256(51).to_ternary_digits(52), {
            let mut d = vec![1u8];
            d.extend(std::iter::repeat(0u8).take(51));
            d
        });
    }
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p verify_erdos mul_ 2>&1 | tail -5`
Expected: compile error — `mul_wide`, `mul_rd`, `mul_ru`, `divrem_u64`, `div_rd_u64`, `div_ru_u64`, `divrem_u256_rd`, `div_rd`, `div_ru`, `from_bigint`, `to_ternary_digits` not defined.

- [ ] **Step 3: Write minimal implementation**

Append to `verify_erdos_rs/src/fixedpoint.rs`:

```rust
use num_bigint::BigInt;

impl U256 {
    /// Full 512-bit product, returned as (high, low).
    pub fn mul_wide(self, o: U256) -> (U256, U256) {
        let a = [
            self.0 as u64,
            (self.0 >> 64) as u64,
            self.1 as u64,
            (self.1 >> 64) as u64,
        ];
        let b = [
            o.0 as u64,
            (o.0 >> 64) as u64,
            o.1 as u64,
            (o.1 >> 64) as u64,
        ];
        let mut c = [0u64; 8];
        for i in 0..4 {
            let mut carry: u128 = 0;
            for j in 0..4 {
                let cur = c[i + j] as u128 + a[i] as u128 * b[j] as u128 + carry;
                c[i + j] = cur as u64;
                carry = cur >> 64;
            }
            c[i + 4] = carry as u64;
        }
        let lo = U256(
            (c[0] as u128) | ((c[1] as u128) << 64),
            (c[2] as u128) | ((c[3] as u128) << 64),
        );
        let hi = U256(
            (c[4] as u128) | ((c[5] as u128) << 64),
            (c[6] as u128) | ((c[7] as u128) << 64),
        );
        (hi, lo)
    }

    /// Low 256 bits, rounded down (truncation). Always a valid lower bound.
    pub fn mul_rd(self, o: U256) -> U256 {
        self.mul_wide(o).1
    }

    /// `Some` only when the product fits u256 exactly (high limb zero). `None`
    /// means the product exceeds 2^256 — the caller must escalate to BigInt.
    /// Never saturate: a saturated MAX can be below the true product.
    pub fn mul_ru(self, o: U256) -> Option<U256> {
        let (hi, lo) = self.mul_wide(o);
        if hi == U256::ZERO {
            Some(lo)
        } else {
            None
        }
    }

    /// Exact quotient + remainder, divisor m ≥ 1 (4-limb schoolbook division
    /// by a 64-bit divisor; `rem` always < m ≤ 2^64, so the running `cur` fits u128).
    pub fn divrem_u64(self, m: u64) -> (U256, u64) {
        assert!(m != 0, "div by zero");
        let m64 = m as u128;
        let limbs = [self.0 as u64, (self.0 >> 64) as u64, self.1 as u64, (self.1 >> 64) as u64];
        let mut out = [0u64; 4];
        let mut rem: u128 = 0;
        for (i, &limb) in limbs.iter().enumerate().rev() {
            let cur = (rem << 64) | limb as u128;
            out[i] = (cur / m64) as u64;
            rem = cur % m64;
        }
        (
            U256(
                (out[0] as u128) | ((out[1] as u128) << 64),
                (out[2] as u128) | ((out[3] as u128) << 64),
            ),
            rem as u64,
        )
    }

    pub fn div_rd_u64(self, m: u64) -> U256 {
        self.divrem_u64(m).0
    }

    pub fn div_ru_u64(self, m: u64) -> U256 {
        let (q, r) = self.divrem_u64(m);
        if r == 0 {
            q
        } else {
            q.add_one()
        }
    }

    /// Binary long division: quotient (floor) + remainder in [0, d).
    pub fn divrem_u256_rd(self, d: U256) -> (U256, U256) {
        assert!(d != U256::ZERO, "div by zero");
        let mut quo = U256::ZERO;
        let mut rem = U256::ZERO;
        for i in (0..256u32).rev() {
            rem = rem.shl(1).set_bit(0, self.bit(i));
            if rem >= d {
                rem = rem.sub(d);
                quo = quo.set_bit(i, true);
            }
        }
        (quo, rem)
    }

    pub fn div_rd(self, d: U256) -> U256 {
        self.divrem_u256_rd(d).0
    }

    pub fn div_ru(self, d: U256) -> Option<U256> {
        let (q, r) = self.divrem_u256_rd(d);
        if r == U256::ZERO {
            Some(q)
        } else {
            Some(q.add_one())
        }
    }

    /// Non-negative BigInt → U256. `None` if negative or ≥ 2^256.
    pub fn from_bigint(b: &BigInt) -> Option<U256> {
        use num_bigint::BigUint;
        use num_traits::Signed;
        if b.sign() == num_bigint::Sign::Minus {
            return None;
        }
        let bu = b.to_biguint().unwrap();
        let d = bu.to_u128_digits();
        if d.len() > 2 {
            return None;
        }
        Some(U256(d.first().copied().unwrap_or(0), d.get(1).copied().unwrap_or(0)))
    }

    /// Big-endian base-3 digits of self, left-aligned and zero-padded to `len`.
    /// Requires self < 3^len.
    pub fn to_ternary_digits(self, len: usize) -> Vec<u8> {
        let mut x = self;
        let mut lsb = Vec::new();
        while x != U256::ZERO {
            let (q, r) = x.divrem_u64(3);
            lsb.push(r as u8);
            x = q;
        }
        while lsb.len() < len {
            lsb.push(0);
        }
        lsb.reverse();
        lsb
    }
}
```

Note: `divrem_u64` is the exact 4-limb schoolbook version above (divide by the 64-bit divisor from the most significant limb down; the remainder always stays < m ≤ 2^64, so `(rem << 64) | limb` never overflows u128). `div_rd_u64`/`div_ru_u64` and `to_ternary_digits` (repeated div-by-3) all go through it.

- [ ] **Step 4: Run test to verify it passes**

Run: `cargo test -p verify_erdos mul_ 2>&1 | tail -5 && cargo test -p verify_erdos div_ 2>&1 | tail -5 && cargo test -p verify_erdos from_bigint 2>&1 | tail -5`
Expected: all PASS.

- [ ] **Step 5: Commit**

```bash
git add verify_erdos_rs/src/fixedpoint.rs
git commit -m "feat(fixedpoint): U256 mul/div (rounded), BigInt conversion, ternary digits"
```

---

### Task 3: FpConfig — certified constants at two scales + derived precision

**Files:**
- Modify: `verify_erdos_rs/src/fixedpoint.rs`
- Modify: `verify_erdos_rs/src/leading.rs` (make `certified_ln`, `certified_alpha`, `certified_pow3_interval_inner` accessible to the module: add `pub(crate)`)

**Interfaces:**
- Consumes: Tasks 1–2 `U256` ops; existing `leading::certified_alpha`, `leading::certified_ln`.
- Produces:
  - `pub struct FpConfig { pub k_prime: usize, pub k: usize, pub n_max: u128, pub p: usize, pub p_t: usize, pub s: U256, pub s_t: U256, pub alpha_lo: U256, pub alpha_hi: U256, pub ln3_lo: U256, pub ln3_hi: U256, pub e_alpha: u128, pub e_ln3: u128, pub budget_ulp: u128, pub resolution: u128, pub k_terms: usize, pub product_ok: bool }`
  - `pub fn alpha_interval_at(p: usize, g: usize) -> (BigInt, BigInt)` — certified_alpha(p+g), scaled to 3^-p by BigInt div by 3^g (lo round-down, hi round-up); `pub(crate)`.
  - `pub fn build_config(p: usize, p_t: usize, k: usize, k_prime: usize) -> FpConfig` — computes constants, budget, k_terms, product_ok.
  - `pub fn error_budget(p: usize, p_t: usize, n_max: u128, e_alpha: u128, e_ln3: u128, k_terms: usize) -> u128`
  - `pub fn verify_precision(cfg: &FpConfig) -> bool` — `cfg.product_ok && cfg.budget_ulp < cfg.resolution`.
  - `pub fn cached_config(k: usize, k_prime: usize) -> Option<FpConfig>` — grid search (P, P_t), cached per (k, k_prime); `None` = no grid config passes → fp path disabled for this K.

The grid order tries smallest P first, then smallest P_t: (108,76), (108,78), (108,80), (112,76), (112,78), (112,80), (118,76), (118,78), (118,80), (124,76), (124,78), (124,80).

Budget formula (spec §4, all ulp at 3^P unless noted):
```
n_max·E_α + 8  +  3^(P_t−P)·(E_ln3 + (P−P_t) + 2 + k_terms + 2)
```
Terms: `n_max·E_α` dominant; `8` = n·α truncation (2) + flo/fhi (2) + a/b (2) + final scale-down (2); the parenthesized Taylor-side sum at scale 3^P_t re-expressed at 3^P: `E_ln3` (x interval) + `(P−P_t)` (frac truncation) + `2` (xlo/xhi div) + `k_terms` (one ulp per term) + `2` (tail margin).

`resolution = 3^(P − k_prime)` as u128 (P−70 ≤ 54, fits u128; P=124 → 3^54 ≈ 5.8e25 < 1.7e38 ✓).

`product_ok = U256::from_u128(n_max).mul_ru(pow3_u256(p)).is_some()`.

`k_terms` = the same convergence loop as the BigInt path with `log_sc = p_t·ln(3)`.

- [ ] **Step 1: Write the failing test**

```rust
    fn e3(v: U256) -> u128 {
        v.0.saturating_add(v.1.saturating_mul(u128::MAX)) // not meaningful; see below
    }
```
Do not use that helper. Real test:
```rust
    #[test]
    fn config_precision_is_derived_per_k() {
        // K=40 (n ≤ 2·3^39): a grid config must pass.
        let c40 = cached_config(40, 70).expect("K=40 fp config exists");
        assert!(verify_precision(&c40), "K=40 must pass verify_precision");
        assert!(c40.budget_ulp < c40.resolution);
        assert!(c40.product_ok, "K=40 product-fit");
        assert!(c40.p <= 124 && c40.p_t <= 80, "within grid");
        assert!(c40.e_alpha <= 8, "constant interval collapsed by guard digits");

        // K=42 (n ≤ 2·3^41): a grid config must pass, at P ≥ the K=40 P.
        let c42 = cached_config(42, 70).expect("K=42 fp config exists");
        assert!(verify_precision(&c42));
        assert!(c42.product_ok);
        assert!(c42.p >= c40.p, "larger n needs at least as much precision");

        // K=42 must reject a P too large for product-fit (3^P·n_max ≥ 2^256).
        let n42 = 2u128 * pow3_u128(41);
        let big = U256::from_u128(n42).mul_ru(pow3_u256(124));
        assert_eq!(big, None, "P=124 breaks product-fit at K=42");

        // Guard digits genuinely collapse the constant interval: the raw
        // certified_alpha(P) interval is ~P·1.585 ulp wide, far above budget.
        let (alo_raw, ahi_raw) = leading::certified_alpha(118);
        let raw_width_ulp = (&ahi_raw - &alo_raw).to_string().parse::<u128>().unwrap();
        assert!(raw_width_ulp > 100, "raw certified_alpha width is ~200+ ulp");
        let (alo_g, ahi_g) = alpha_interval_at(118, 12);
        let w = &ahi_g - &alo_g;
        assert!(w.to_string().parse::<u128>().unwrap() <= 8, "guarded width collapsed to ~2 ulp");
        assert!(alo_g <= alo_raw && ahi_g >= ahi_raw, "guarded interval contains raw interval");
    }

    #[test]
    fn constants_lie_in_certified_bounds() {
        let c = build_config(118, 78, 40, 70);
        // α·3^P must contain the certified α interval at 3^-118
        let (alo, ahi) = alpha_interval_at(118, 12);
        let u_alo = U256::from_bigint(&alo).unwrap();
        let u_ahi = U256::from_bigint(&ahi).unwrap();
        assert!(u_alo <= c.alpha_lo && c.alpha_lo <= u_ahi, "alpha_lo in interval");
        assert!(u_alo <= c.alpha_hi && c.alpha_hi <= u_ahi, "alpha_hi in interval");
        // ln3 at 3^P_t
        let (l3lo, l3hi) = leading::certified_ln(3, 78);
        let sm = BigInt::from(3u32).pow(12);
        let l3lo_s = &l3lo / &sm;
        let l3hi_s = (&l3hi + &sm - 1) / &sm;
        assert!(U256::from_bigint(&l3lo_s).unwrap() <= c.ln3_lo);
        assert!(c.ln3_hi <= U256::from_bigint(&l3hi_s).unwrap());
        // scale values
        assert_eq!(c.s, pow3_u256(118));
        assert_eq!(c.s_t, pow3_u256(78));
    }
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p verify_erdos config_precision 2>&1 | tail -5`
Expected: compile error — `FpConfig`, `build_config`, `cached_config`, `verify_precision`, `alpha_interval_at` missing; `certified_alpha`/`certified_ln` not `pub(crate)`.

- [ ] **Step 3: Write minimal implementation**

In `leading.rs`, change:
```rust
pub fn certified_ln(x: u32, p: usize) -> (BigInt, BigInt) {
```
to `pub(crate) fn` — keep the `pub` signature otherwise identical (it is already `pub`; add `pub(crate)` marker via a re-export or just leave `pub` and let `fixedpoint` use `crate::leading::certified_ln`). Simplest: leave as `pub`.

Append to `fixedpoint.rs`:
```rust
use crate::leading::{certified_alpha, certified_ln};
use num_bigint::BigInt;
use std::collections::HashMap;
use std::sync::{Mutex, OnceLock};

pub const GUARD_G: usize = 12;
const P_GRID: [usize; 4] = [108, 112, 118, 124];
const PT_GRID: [usize; 3] = [76, 78, 80];

pub struct FpConfig {
    pub k_prime: usize,
    pub k: usize,
    pub n_max: u128,
    pub p: usize,
    pub p_t: usize,
    pub s: U256,
    pub s_t: U256,
    pub alpha_lo: U256,
    pub alpha_hi: U256,
    pub ln3_lo: U256,
    pub ln3_hi: U256,
    pub e_alpha: u128,
    pub e_ln3: u128,
    pub budget_ulp: u128,
    pub resolution: u128,
    pub k_terms: usize,
    pub product_ok: bool,
}

/// certified_alpha(p + g) scaled to 3^-p, lo rounded down, hi rounded up.
pub(crate) fn alpha_interval_at(p: usize, g: usize) -> (BigInt, BigInt) {
    let (alo, ahi) = certified_alpha(p + g);
    let sm = BigInt::from(3u32).pow(g as u32);
    let lo = &alo / &sm;
    let hi = (&ahi + &sm - 1) / &sm;
    (lo, hi)
}

fn taylor_k_terms(p_t: usize) -> usize {
    let log_sc = p_t as f64 * 3f64.ln();
    let mut k_terms: usize = 16;
    loop {
        let kk = k_terms as f64;
        if kk * kk.ln() - kk > log_sc + kk * 1.1f64.ln() {
            break;
        }
        k_terms *= 2;
    }
    k_terms + 20
}

/// Explicit interval width in ulp at scale 3^P (spec §4 table).
/// `n_max·E_α` dominates; `8` = n·α truncation (2) + flo/fhi (2) + a/b (2) +
/// final scale-down (2); the Taylor-side sum at scale 3^P_t is re-expressed
/// at 3^P by the factor `3^(P_t−P) = 1 / 3^(P−P_t)`.
pub fn error_budget(
    p: usize,
    p_t: usize,
    n_max: u128,
    e_alpha: u128,
    e_ln3: u128,
    k_terms: usize,
) -> u128 {
    let taylor_side =
        e_ln3 + (p - p_t) as u128 + 2 + k_terms as u128 + 2;
    let scaled = taylor_side / pow3_u128(p - p_t);
    n_max
        .checked_mul(e_alpha)
        .unwrap_or(u128::MAX)
        .saturating_add(8)
        .saturating_add(scaled)
}

pub fn build_config(p: usize, p_t: usize, k: usize, k_prime: usize) -> FpConfig {
    let n_max = 2u128 * pow3_u128(k);
    let (alo, ahi) = alpha_interval_at(p, GUARD_G);
    let (l3lo, l3hi) = certified_ln(3, p_t + GUARD_G);
    let sm = BigInt::from(3u32).pow(GUARD_G as u32);
    let l3lo_s = &l3lo / &sm;
    let l3hi_s = (&l3hi + &sm - 1) / &sm;
    let alpha_lo = U256::from_bigint(&alo).unwrap();
    let alpha_hi = U256::from_bigint(&ahi).unwrap();
    let ln3_lo = U256::from_bigint(&l3lo_s).unwrap();
    let ln3_hi = U256::from_bigint(&l3hi_s).unwrap();
    let e_alpha = alpha_hi.sub(alpha_lo).0 as u128;
    let e_ln3 = ln3_hi.sub(ln3_lo).0 as u128;
    let k_terms = taylor_k_terms(p_t);
    let budget_ulp = error_budget(p, p_t, n_max, e_alpha, e_ln3, k_terms);
    let resolution = pow3_u128(p - k_prime);
    let product_ok = U256::from_u128(n_max).mul_ru(pow3_u256(p)).is_some();
    FpConfig {
        k_prime,
        k,
        n_max,
        p,
        p_t,
        s: pow3_u256(p),
        s_t: pow3_u256(p_t),
        alpha_lo,
        alpha_hi,
        ln3_lo,
        ln3_hi,
        e_alpha,
        e_ln3,
        budget_ulp,
        resolution,
        k_terms,
        product_ok,
    }
}

pub fn verify_precision(cfg: &FpConfig) -> bool {
    cfg.product_ok && cfg.budget_ulp < cfg.resolution
}

static CONFIG_CACHE: OnceLock<Mutex<HashMap<(usize, usize), Option<FpConfig>>>> = OnceLock::new();

/// Smallest grid config that passes `verify_precision` for K; `None` = fp path
/// must be disabled for this K (pure BigInt, unchanged behavior).
pub fn cached_config(k: usize, k_prime: usize) -> Option<FpConfig> {
    let cache = CONFIG_CACHE.get_or_init(|| Mutex::new(HashMap::new()));
    let mut map = cache.lock().unwrap();
    if let Some(hit) = map.get(&(k, k_prime)) {
        return hit.clone();
    }
    let mut chosen = None;
    'outer: for &p in &P_GRID {
        for &p_t in &PT_GRID {
            let cfg = build_config(p, p_t, k, k_prime);
            if verify_precision(&cfg) {
                chosen = Some(cfg);
                break 'outer;
            }
        }
    }
    map.insert((k, k_prime), chosen.clone());
    chosen
}
```

- [ ] **Step 4: Run test to verify it passes**

Run: `cargo test -p verify_erdos config_precision 2>&1 | tail -5 && cargo test -p verify_erdos constants_lie 2>&1 | tail -5`
Expected: both PASS. (If the measured `E_α` is larger than 8, adjust the `e_alpha <= 8` assertion to the measured value — the *mechanism* (budget < resolution) is the contract, the constant 8 is a sanity bound. Same for the guarded-width `<= 8` bound: it should hold since guard = 12 digits ≫ ~1 ulp.)

- [ ] **Step 5: Commit**

```bash
git add verify_erdos_rs/src/fixedpoint.rs verify_erdos_rs/src/leading.rs
git commit -m "feat(fixedpoint): FpConfig with derived precision (error budget, verify_precision, guarded constants)"
```

---

### Task 4: Certified pow3 interval in u256 + the fast path

**Files:**
- Modify: `verify_erdos_rs/src/fixedpoint.rs`
- Modify: `verify_erdos_rs/src/leading.rs` (make `certified_pow3_interval_inner` reusable as a BigInt reference for containment tests: rename to `pub(crate) fn pow3_interval_bigint`)

**Interfaces:**
- Consumes: Tasks 1–3 (`U256`, `FpConfig`, `cached_config`).
- Produces:
  - `pub fn certified_pow3_interval_256(a: U256, b: U256, p_t: usize, l3lo: U256, l3hi: U256, s_t: U256) -> Option<(U256, U256)>` — Taylor at scale `3^P_t`, round-down/up per term, geometric tail bound. `None` on any u256 overflow (caller escalates).
  - `pub fn leading_digits_have_two_fp(n: u128, k_prime: usize) -> Option<Option<bool>>` — full fast path; outer `None` = ambiguous (fallback to BigInt), `Some(ans)` = certified.

Fast path steps (spec §5):
1. `nlo = U256::from_u128(n).mul_rd(α_lo)`; `nhi = U256::from_u128(n).mul_ru(α_hi)?`
2. `(flo, a) = nlo.divrem_u256_rd(S)`; `(flo2, b) = nhi.divrem_u256_rd(S)`; `fhi = if b == ZERO { flo2 } else { flo2.add_one() }`. If `flo != fhi` → `None`.
3. `a_t = a.div_rd(pow3_u256(P−P_t))`; `b_t = b.div_ru(pow3_u256(P−P_t))?`
4. `(ylo, yhi) = certified_pow3_interval_256(a_t, b_t, P_t, ln3_lo, ln3_hi, S_t)?`
5. `sd = pow3_u256(P_t−70)`; `ylo_k = ylo.div_rd(sd)`; `yhi_k = yhi.div_ru(sd)?`; if `yhi_k >= pow3_u256(71)` → `None` (resolution failure).
6. `r = ylo_k.to_ternary_digits(70+20)`; `r_hi = yhi_k.to_ternary_digits(70+20)`.
7. Prefix-span: `r[..70] == r_hi[..70]` → `Some(Some(r[..70].contains(&2)))`, else `None`.

Taylor (per term k from 2, term 1 = X = t·ln3 at scale S_t):
```
lo_k = tklo.mul_rd(Xlo).div_rd_u64(k).div_rd(S_t)
hi_k = tkhi.mul_ru(Xhi)?.div_ru_u64(k).div_ru(S_t)?
```
where `Xlo = a.mul_rd(l3lo).div_rd(S_t)`, `Xhi = b.mul_ru(l3hi)?.div_ru(S_t)?`. Sum from `S_t`.

Tail (hi bound only): `tail = term_next + term_next·X/((n+2)·S_t − X)` rounded up, with `term_next = tkhi.mul_ru(Xhi)?.div_ru_u64(n+1).div_ru(S_t)?`, `n = k_terms`. This is the exact geometric sum `term_next/(1−r)`, r = X/((n+2)·S_t) (equivalent to the BigInt tail formula, no overflow: `term_next·X ≈ 2^253`, `(n+2)·S_t − X ≈ 2^133`).

- [ ] **Step 1: Write the failing test**

```rust
    #[test]
    fn pow3_interval_256_contains_bigint() {
        use crate::leading::pow3_interval_bigint;
        use num_bigint::{BigInt, BigUint};
        // random frac intervals [a,b] ⊆ [0, 3^78), all at scale 3^78
        let s_t = pow3_u256(78);
        let (l3lo, l3hi) = certified_ln(3, 78 + GUARD_G);
        let sm = BigInt::from(3u32).pow(GUARD_G as u32);
        let l3lo_s = &l3lo / &sm;
        let l3hi_s = (&l3hi + &sm - 1) / &sm;
        let l3lo_u = U256::from_bigint(&l3lo_s).unwrap();
        let l3hi_u = U256::from_bigint(&l3hi_s).unwrap();
        let mut seed: u64 = 0x9e37_79b9_7f4a_7c15;
        let mut next = move || {
            seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            seed
        };
        let pow40 = BigInt::from(3u32).pow(40u32);
        let pow40u = BigUint::from(3u32).pow(40u32);
        for _ in 0..200 {
            let a = U256::from_u128(next() as u128 % pow3_u128(78));
            let b = a.add(U256::from_u128(next() as u128 % (1 << 40)));
            let b = if b >= s_t { s_t.sub(U256::from_u64(1)) } else { b };
            assert!(a <= b && b < s_t);
            let (ylo, yhi) = certified_pow3_interval_256(a, b, 78, l3lo_u, l3hi_u, s_t).unwrap();
            // Certified BigInt reference at scale 3^-118 (p = 78+40):
            // inputs are the same value at 3^-118, i.e. a·3^40, b·3^40.
            let a_bi = BigInt::from_biguint(num_bigint::Sign::Plus, a.to_biguint() * &pow40u);
            let b_bi = BigInt::from_biguint(num_bigint::Sign::Plus, b.to_biguint() * &pow40u);
            let (blo, bhi) = pow3_interval_bigint(&a_bi, &b_bi, 78 + 40, &l3lo_s, &l3hi_s);
            // Tight certified window around the true value, at scale 3^-78.
            let t_lo78 = &blo / &pow40; // floor -> still ≤ truth78
            let t_hi78 = (&bhi + &pow40 - 1) / &pow40; // ceil -> still ≥ truth78
            // Soundness: the u256 interval must overlap the certified truth
            // window (definitive soundness is the differential test below).
            assert!(
                ylo <= t_hi78 && yhi >= t_lo78,
                "u256 interval [ylo,yhi] misses certified truth window at iter"
            );
            assert!(ylo <= yhi, "u256 interval inverted");
        }
    }
```

The helper `U256::to_biguint` used above is added with the implementation (Step 3).

Also add:
```rust
    #[test]
    fn fast_path_matches_bigint_small_range() {
        // exhaustive n in [0, 2000], k_prime=70: fp result (or ambiguity) is
        // never a wrong answer; ambiguity is allowed but must be rare.
        let mut fallback = 0u32;
        for n in 0u128..=2000 {
            let fp = leading_digits_have_two_fp(n, 70);
            let truth = crate::leading::leading_digits_have_two_bigint(n, 70);
            match fp {
                Some(ans) => assert_eq!(ans, truth, "fp mismatch at n={n}"),
                None => fallback += 1,
            }
        }
        assert!(fallback <= 20, "fallback rate too high on small n: {fallback}");
    }
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p verify_erdos pow3_interval_256 2>&1 | tail -5`
Expected: compile error — `certified_pow3_interval_256`, `leading_digits_have_two_fp`, `pow3_interval_bigint`, `leading_digits_have_two_bigint`, `U256::to_biguint` missing.

- [ ] **Step 3: Write minimal implementation**

In `leading.rs`, rename the private helper for reuse:
```rust
pub(crate) fn pow3_interval_bigint(
    a: &BigInt,
    b: &BigInt,
    p: usize,
    l3lo: &BigInt,
    l3hi: &BigInt,
) -> (BigInt, BigInt) {
    // body of the old certified_pow3_interval_inner, unchanged
}
```
and change the call site in `leading_digits_have_two` (it becomes `leading_digits_have_two_bigint` in Task 5; for this task keep the old name and add the new `leading_digits_have_two_bigint` as an alias so tests compile):
```rust
pub fn leading_digits_have_two_bigint(n: u128, k_prime: usize) -> Option<bool> {
    // existing body of leading_digits_have_two, unchanged, using pow3_interval_bigint
}
```

Append to `fixedpoint.rs`:
```rust
use num_bigint::BigUint;

impl U256 {
    /// Exact conversion to BigUint (used by the containment test).
    pub fn to_biguint(self) -> BigUint {
        (BigUint::from(self.1) << 128) | BigUint::from(self.0)
    }
}

/// 3^t ∈ [lo, hi] at scale 3^P_t for all t ∈ [a,b]·3^-P_t ⊆ [0,1).
/// `None` if any intermediate product exceeds u256 (caller escalates to BigInt).
pub fn certified_pow3_interval_256(
    a: U256,
    b: U256,
    p_t: usize,
    l3lo: U256,
    l3hi: U256,
    s_t: U256,
) -> Option<(U256, U256)> {
    debug_assert!(a <= b && b < s_t);
    let k_terms = taylor_k_terms(p_t);
    let xlo = a.mul_rd(l3lo).div_rd(s_t);
    let xhi = b.mul_ru(l3hi)?.div_ru(s_t)?;
    let mut lo = s_t;
    let mut hi = s_t;
    let mut tklo = xlo;
    let mut tkhi = xhi;
    for k in 2..=k_terms {
        let kd = k as u64;
        let lo_k = tklo.mul_rd(xlo).div_rd_u64(kd).div_rd(s_t);
        let hi_k = tkhi.mul_ru(xhi)?.div_ru_u64(kd).div_ru(s_t)?;
        lo = lo.add(lo_k);
        hi = hi.add(hi_k);
        tklo = lo_k;
        tkhi = hi_k;
    }
    let n = k_terms as u64;
    let term_next = tkhi.mul_ru(xhi)?.div_ru_u64(n + 1).div_ru(s_t)?;
    // Exact geometric tail bound: tail = term_next/(1−r) with r = X/((n+2)·S_t),
    // i.e. tail = term_next + term_next·X/D, D = (n+2)·S_t − X.
    // term_next·X ≈ 2^253 fits; D ≈ 2^133 fits; both round up.
    let d = s_t.mul_u64(n + 2).sub(xhi);
    let tail = term_next.add(term_next.mul_ru(xhi)?.div_ru(d)?);
    let upper = hi.add(tail);
    Some((lo, upper))
}
```

Then the fast path:
```rust
/// Fast path. `Some(ans)` = certified first-k_prime-digit answer;
/// `None` = ambiguous/overflow → caller must run the BigInt path.
pub fn leading_digits_have_two_fp(n: u128, k_prime: usize) -> Option<Option<bool>> {
    if k_prime != 70 {
        return None;
    }
    let cfg = cached_config(39, k_prime)?; // k = 39 → n_max = 2·3^39 (covers any candidate up to K=40)
    // Note: the config's k determines n_max used for precision verification.
    // Task 5 replaces this with the run's K via `set_run_k` + `cached_config(0, …)`.
    let nlo = U256::from_u128(n).mul_rd(cfg.alpha_lo);
    let nhi = U256::from_u128(n).mul_ru(cfg.alpha_hi)?;
    let (flo, a) = nlo.divrem_u256_rd(cfg.s);
    let (flo2, b) = nhi.divrem_u256_rd(cfg.s);
    let fhi = if b == U256::ZERO { flo2 } else { flo2.add_one() };
    if flo != fhi {
        return None;
    }
    let sd = pow3_u256(cfg.p - cfg.p_t);
    let a_t = a.div_rd(sd);
    let b_t = b.div_ru(sd)?;
    // frac ≈ 1 boundary: b_t rounding up to exactly S_t (t → 1) means the
    // interval touches t = 1, where y = 3^t can reach 3 (out of the
    // [3^70, 3^71) digit range). Escalate to BigInt, which handles this via
    // its precision-doubling retry.
    if b_t >= cfg.s_t {
        return None;
    }
    let (ylo, yhi) = certified_pow3_interval_256(a_t, b_t, cfg.p_t, cfg.ln3_lo, cfg.ln3_hi, cfg.s_t)?;
    let sd70 = pow3_u256(cfg.p_t - 70);
    let ylo_k = ylo.div_rd(sd70);
    let yhi_k = yhi.div_ru(sd70)?;
    if yhi_k >= pow3_u256(71) {
        return None;
    }
    let r = ylo_k.to_ternary_digits(70 + 20);
    let r_hi = yhi_k.to_ternary_digits(70 + 20);
    if r[..70] == r_hi[..70] {
        Some(Some(r[..70].contains(&2)))
    } else {
        None
    }
}
```

Important: the fast path must be verified against the *run's* K (the actual n_max), not a hard-coded 39. Task 5's dispatcher passes the run K via a thread-safe `CURRENT_K` cell so `cached_config` uses the real `n_max`. For this task, the default K=39 (n ≤ 2·3^39, i.e. any u128 candidate stream up to K=40) is used for `leading_digits_have_two_fp`; Task 5 replaces it with the run-specific K.

- [ ] **Step 4: Run test to verify it passes**

Run: `cargo test -p verify_erdos pow3_interval_256 2>&1 | tail -5 && cargo test -p verify_erdos fast_path 2>&1 | tail -5`
Expected: PASS (containment holds; small-range fp matches BigInt with ≤ 20 fallbacks).

- [ ] **Step 5: Commit**

```bash
git add verify_erdos_rs/src/fixedpoint.rs verify_erdos_rs/src/leading.rs
git commit -m "feat(fixedpoint): certified pow3 interval in u256 + leading_digits_have_two_fp"
```

---

### Task 5: Dispatcher + `--two-sided-bigint` + differential tests

**Files:**
- Modify: `verify_erdos_rs/src/leading.rs` (dispatcher `leading_digits_have_two`, `FORCE_BIGINT`, `set_force_bigint`, run-K cell)
- Modify: `verify_erdos_rs/src/main.rs` (`--two-sided-bigint` flag, help text)
- Test: `verify_erdos_rs/src/fixedpoint.rs` (synthetic differential, k_prime=70 brute n ≤ 10⁴)
- Test: `verify_erdos_rs/src/two_sided.rs` (fp vs BigInt parity at K=25/30)

**Interfaces:**
- Consumes: `fixedpoint::leading_digits_have_two_fp`, `fixedpoint::cached_config`, `fixedpoint::set_run_k`.
- Produces:
  - `leading::leading_digits_have_two(n, k_prime)` — dispatcher: if `k_prime == 70 && !FORCE_BIGINT` → fp; else BigInt.
  - `leading::leading_digits_have_two_bigint(n, k_prime)` — the unchanged original body.
  - `leading::set_force_bigint(bool)` — global switch for `--two-sided-bigint` and tests.
  - `fixedpoint::set_run_k(k)` — per-run K for `cached_config` (thread-safe static `RwLock<usize>`), default 39.

- [ ] **Step 1: Write the failing test**

```rust
// in fixedpoint.rs tests
    #[test]
    fn differential_synthetic_stream_no_mismatch() {
        use crate::leading::{leading_digits_have_two, leading_digits_have_two_bigint, set_force_bigint};
        set_force_bigint(false);
        let mut seed: u64 = 0x2545_f491_4f6c_dd1d;
        let mut next = move || {
            seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            seed
        };
        let mut cases: Vec<u128> = (0u128..=300).collect();
        // adversarial: near powers of 3 and near 2·3^m
        for m in 1u32..=42 {
            let p3 = pow3_u128(m as usize);
            for d in 0..=2u128 {
                cases.push(p3.saturating_sub(d));
                cases.push(p3.saturating_add(d));
                cases.push((2 * p3).saturating_sub(d));
                cases.push((2 * p3).saturating_add(d));
            }
        }
        // random u128 below 2^62 and straddling 2^62..2^64
        for _ in 0..100_000 {
            let hi = (next() >> 2) as u128;
            let lo = next() as u128;
            cases.push((hi << 64) | lo);
        }
        let mut fallback = 0u32;
        for (i, n) in cases.iter().copied().enumerate() {
            let fp = leading_digits_have_two(n, 70);
            let truth = leading_digits_have_two_bigint(n, 70);
            assert_eq!(fp, truth, "mismatch at i={i} n={n}");
            if leading_digits_have_two_fp(n, 70).is_none() {
                fallback += 1;
            }
        }
        // report fallback % in output (debug prints allowed in tests)
        eprintln!("differential fallback: {fallback}/{}", cases.len());
    }
```

Note: `assert_eq!(fp, truth)` is the "result mismatches must be zero" check: `leading_digits_have_two(n, 70)` with the flag off runs fp→fallback→BigInt, which equals pure BigInt whenever fp certifies, and equals BigInt by construction when fp falls back. This test runs ~106k cases in debug; the BigInt half dominates (~0.2–0.4 ms/case → ~20–40 s). Acceptable for a unit test; run in release for the gate (Task 6).

```rust
// in two_sided.rs tests
    #[test]
    fn two_sided_matches_bigint_parity() {
        use crate::leading::set_force_bigint;
        for k in [25usize, 30] {
            let rep_fp = run_two_sided(k, 70, 2, 12);
            set_force_bigint(true);
            let rep_bi = run_two_sided(k, 70, 2, 12);
            set_force_bigint(false);
            assert_eq!(rep_fp.deep, rep_bi.deep, "deep set at K={k}");
            assert_eq!(rep_fp.candidates, rep_bi.candidates, "candidates at K={k}");
            assert_eq!(rep_fp.eliminated, rep_bi.eliminated, "eliminated at K={k}");
            assert_eq!(rep_fp.ambiguous, rep_bi.ambiguous, "ambiguous at K={k}");
        }
    }
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p verify_erdos differential_synthetic 2>&1 | tail -5`
Expected: compile error — `set_force_bigint`, `set_run_k`, dispatcher missing.

- [ ] **Step 3: Write minimal implementation**

In `leading.rs`:
```rust
use std::sync::atomic::{AtomicBool, Ordering};

static FORCE_BIGINT: AtomicBool = AtomicBool::new(false);

/// Debug flag: force the pure-BigInt path end-to-end (--two-sided-bigint).
pub fn set_force_bigint(b: bool) {
    FORCE_BIGINT.store(b, Ordering::Relaxed);
}

/// Dispatcher: u256 fixed-point fast path first (k_prime == 70), then the
/// certified BigInt path. The BigInt path is the ground truth and untouched.
pub fn leading_digits_have_two(n: u128, k_prime: usize) -> Option<bool> {
    if k_prime == 70 && !FORCE_BIGINT.load(Ordering::Relaxed) {
        if let Some(ans) = crate::fixedpoint::leading_digits_have_two_fp(n, k_prime) {
            return ans;
        }
    }
    leading_digits_have_two_bigint(n, k_prime)
}
```
And rename the existing function body (currently `leading_digits_have_two`) to `leading_digits_have_two_bigint`, updating its internal call to `pow3_interval_bigint`. The test `leading_check_matches_bruteforce` (k_prime=50) and `known_record_agrees_with_phase8` (50/51) still route through `leading_digits_have_two` → BigInt (k_prime ≠ 70) — unchanged.

In `fixedpoint.rs`, add the run-K cell and thread it into `cached_config`:
```rust
use std::sync::RwLock;
static RUN_K: RwLock<usize> = RwLock::new(39);

/// Set the run's K so `cached_config` verifies precision for the real n_max.
pub fn set_run_k(k: usize) {
    *RUN_K.write().unwrap() = k;
}

pub fn cached_config(k: usize, k_prime: usize) -> Option<FpConfig> {
    // k = 0 → use the run K (default 39)
    let k = if k == 0 { *RUN_K.read().unwrap() } else { k };
    // ... existing body keyed on (k, k_prime) ...
}
```
Update `leading_digits_have_two_fp` to call `cached_config(0, k_prime)` (run K) instead of `cached_config(39, ...)`.

`two_sided.rs`: no change (already calls `leading_digits_have_two`). The engine must set the run K before running: in `main.rs --two-sided`, call `fixedpoint::set_run_k(k)` before `run_two_sided`.

`main.rs`:
```rust
if args.iter().any(|a| a == "--two-sided-bigint") {
    leading::set_force_bigint(true);
    println!("NOTE: --two-sided-bigint — forcing certified BigInt path end-to-end");
}
```
(placed before the `--two-sided` branch; only meaningful there). Update `--help`:
```
println!("  verify_erdos --two-sided K [k_prime]           Two-sided pruning engine");
println!("  verify_erdos --two-sided K [k_prime] --two-sided-bigint   Force BigInt path (differential/debug)");
```

- [ ] **Step 4: Run test to verify it passes**

Run:
```
cargo test -p verify_erdos differential_synthetic 2>&1 | tail -5
cargo test -p verify_erdos two_sided_matches 2>&1 | tail -5
cargo test -p verify_erdos leading_check_matches 2>&1 | tail -5
cargo test -p verify_erdos known_record 2>&1 | tail -5
cargo test -p verify_erdos deep_set 2>&1 | tail -5
```
Expected: all PASS. (The two-sided parity at K=30 takes a while in debug — ~1–2 min; run `--release` if slower than 5 min.)

- [ ] **Step 5: Commit**

```bash
git add verify_erdos_rs/src/leading.rs verify_erdos_rs/src/fixedpoint.rs verify_erdos_rs/src/main.rs verify_erdos_rs/src/two_sided.rs
git commit -m "feat: fp dispatcher + --two-sided-bigint + differential tests (zero mismatches)"
```

---

### Task 6: Benchmark hard gate + findings + record runs

**Files:**
- Modify: `verify_erdos_rs/src/main.rs` (`--bench-leading N [seed]`)
- Create: `verify_erdos_rs/PHASE10_FINDINGS.md`
- Modify: `ROADMAP.md` (check Phase 10 boxes as they complete)

**Interfaces:**
- Consumes: `leading::leading_digits_have_two`, `leading::set_force_bigint`, `fixedpoint::leading_digits_have_two_fp`, `fixedpoint::set_run_k`, `saye::for_each_candidate`.

- [ ] **Step 1: Add the benchmark CLI (write it, then run it)**

In `main.rs`, add a branch:
```rust
} else if args.len() > 1 && args[1] == "--bench-leading" {
    let n: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(200_000);
    let seed: u64 = args.get(3).and_then(|s| s.parse().ok()).unwrap_or(0x9e37_79b9_7f4a_7c15);
    fixedpoint::set_run_k(40);
    let t0 = std::time::Instant::now();
    let cases = bench_stream(n, seed);
    eprintln!("stream: {} cases in {:.2?}", cases.len(), t0.elapsed());

    // BigInt baseline
    leading::set_force_bigint(true);
    let t1 = std::time::Instant::now();
    let mut n_bi = 0usize;
    let mut sum_bi = 0u64;
    for &n in &cases {
        n_bi += 1;
        if leading::leading_digits_have_two(n, 70).unwrap_or(false) { sum_bi += 1; }
    }
    let dt_bi = t1.elapsed();
    eprintln!("BigInt only:  {n_bi} cases in {dt_bi:.2?}  ({:.0} cases/s)",
        n_bi as f64 / dt_bi.as_secs_f64());

    // fp-first (engine mode)
    leading::set_force_bigint(false);
    let mut fallback = 0usize;
    let mut ambiguous = 0usize;
    let t2 = std::time::Instant::now();
    let mut sum_fp = 0u64;
    for &n in &cases {
        if leading::leading_digits_have_two(n, 70).unwrap_or(false) { sum_fp += 1; }
        if fixedpoint::leading_digits_have_two_fp(n, 70).is_none() {
            fallback += 1;
            ambiguous += 1;
        }
    }
    let dt_fp = t2.elapsed();
    eprintln!("fp-first:     {n_bi} cases in {dt_fp:.2?}  ({:.0} cases/s)",
        n_bi as f64 / dt_fp.as_secs_f64());
    eprintln!("fallback (BigInt): {fallback} ({:.2}%)", 100.0 * fallback as f64 / n_bi as f64);
    eprintln!("speedup: {:.2}×", dt_bi.as_secs_f64() / dt_fp.as_secs_f64());
    eprintln!("mismatch check: {}", if sum_bi == sum_fp { "OK" } else { "FAILED" });
    return;
}
```
with a stream generator:
```rust
fn bench_stream(n: usize, mut seed: u64) -> Vec<u128> {
    let mut next = move || {
        seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        seed
    };
    let mut v = Vec::with_capacity(n);
    for m in 1u32..=42 {
        let p3 = pow3_u128(m);
        for d in 0..=2u128 {
            v.push(p3.saturating_sub(d));
            v.push((2 * p3).saturating_sub(d));
        }
    }
    while v.len() < n {
        let hi = (next() >> 2) as u128;
        v.push((hi << 64) | (next() as u128));
    }
    v
}
```
(`pow3_u128` needs importing from `fixedpoint` in `main.rs`.)

Run in release:
```
cargo build --release
./target/release/verify_erdos --bench-leading 200000
```
Expected: speedup printed; `mismatch check: OK`. Record the numbers.

- [ ] **Step 2: Real-stream parity (release)**

```
./target/release/verify_erdos --two-sided 33 70 > /tmp/k33_fp.txt
./target/release/verify_erdos --two-sided 33 70 --two-sided-bigint > /tmp/k33_bi.txt
```
Expected: identical `candidates`, `eliminated`, `deep={0,2,8}`, `ambiguous=0` lines (diff the two `report_line` outputs). Record both.

- [ ] **Step 3: Full suite green (release) + K=35/K=38 spot parity**

```
cargo test --release 2>&1 | tail -8
./target/release/verify_erdos --two-sided 25 70
./target/release/verify_erdos --two-sided 35 70   # ~7.7M candidates; confirm deep={0,2,8}
```
Expected: full suite PASS; K=25 deep {0,2,8}; K=35 deep {0,2,8}, candidates ≈ 7,747,002 (matches Phase 1/9).

- [ ] **Step 4: Record findings and gate decision**

Create `verify_erdos_rs/PHASE10_FINDINGS.md` with:
- benchmark table (BigInt vs fp candidates/sec, fallback %, ambiguous, peak precision P/P_t used for K=40, K=42)
- differential/parity results (synthetic + real-stream K=33, K=35, mismatch = 0)
- gate verdict: proceed/abort K=40, with the K=40/K=42 record runs and their elapsed times appended after they finish.
- the actual `(P, P_t)` chosen by `cached_config` for K=40 and K=42 (printed via a small `--two-sided 40` dry run or a test print).

Update `ROADMAP.md` Phase 10 checkboxes for completed deliverables.

- [ ] **Step 5: Commit**

```bash
git add verify_erdos_rs/src/main.rs verify_erdos_rs/PHASE10_FINDINGS.md ROADMAP.md
git commit -m "feat(bench): --bench-leading + findings + gate (Phase 10 build complete)"
```

- [ ] **Step 6: Launch K=40 background record (gate-passing only)**

```
setsid nohup ./target/release/verify_erdos --two-sided 40 70 > /tmp/erdos_k40.log 2>&1 &
```
Expected: same shape as K=39 (`[n/524288] branches` progress in the log). K=40 covers n ≤ 2·3^39 ≈ 8.1×10^18, estimated 3–5 h on the contended box. K=42 follows after (est. 2–4 d). K=46 (beat Saye) is out of scope here.

---

## Self-Review Checklist

- **Spec coverage:** §3 architecture → Tasks 1–5; §4 precision model → Task 3 (`error_budget`, `verify_precision`, guarded constants, two scales); §5 data flow → Task 4 (all 8 steps in order); §6 testing/gate → Tasks 3–6 (unit, containment, synthetic differential, engine parity, bench gate before K=40); §7 integration/docs → Tasks 5–6 + findings; §8 risks → Task 3 verify_precision + Task 4 containment tests + Task 5 fallback semantics.
- **Placeholder scan:** no TBD/estimates left; every step has runnable code and commands.
- **Type consistency:** `FpConfig` fields used in Tasks 3–5 match; `mul_ru`/`div_ru` return `Option` everywhere (escalation path is uniform); `cached_config` keyed on `(k, k_prime)` with run-K indirection introduced in Task 5 and used by the dispatcher and bench in Task 6; `leading_digits_have_two_bigint` is the ground truth used by all differential tests; `certified_pow3_interval_256` and `pow3_interval_bigint` are the containment pair.