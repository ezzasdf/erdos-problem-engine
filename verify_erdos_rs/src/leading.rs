//! Certified leading ternary digits of 3^{frac(n·log_3 2)} (2^n's leading digits).
//!
//! Port of verify_middle/src/certified.rs interval arithmetic, trimmed to the
//! first `k_prime` digits for u128 n. Public entry: `leading_digits_have_two`.

use num_bigint::{BigInt, BigUint};
use std::collections::HashMap;
use std::sync::{Mutex, OnceLock};

/// Guard digits appended after the reportable prefix (matches verify_middle).
const GUARDS: usize = 20;

fn pow3_64() -> BigInt {
    static C: OnceLock<BigInt> = OnceLock::new();
    C.get_or_init(|| BigInt::from(3u32).pow(64u32)).clone()
}

/// Per-precision cache of n-independent certified values: α = log₃2 and ln 3,
/// both at scale 3^-p_hi, plus 3^p_hi. Reused across all candidates.
struct PrecisionCache {
    alpha: (BigInt, BigInt),
    ln3: (BigInt, BigInt),
    s_hi: BigInt,
}

static PRECISION_CACHE: OnceLock<Mutex<HashMap<usize, PrecisionCache>>> = OnceLock::new();

fn cached_precision(p_hi: usize) -> (BigInt, BigInt, BigInt, BigInt, BigInt) {
    let mut cache = PRECISION_CACHE.get_or_init(|| Mutex::new(HashMap::new())).lock().unwrap();
    let entry = cache.entry(p_hi).or_insert_with(|| {
        let (alo, ahi) = certified_alpha(p_hi);
        let (l3lo, l3hi) = certified_ln(3, p_hi);
        let s_hi = BigInt::from(3u32).pow(p_hi as u32);
        PrecisionCache { alpha: (alo, ahi), ln3: (l3lo, l3hi), s_hi }
    });
    (
        entry.alpha.0.clone(),
        entry.alpha.1.clone(),
        entry.ln3.0.clone(),
        entry.ln3.1.clone(),
        entry.s_hi.clone(),
    )
}

/// base-3 big-endian digits of v, left-aligned and zero-padded to length
/// p + GUARDS (reportable prefix at 0..p).
/// Requires v < 3^(p+1).
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
/// n-independent inputs (l3lo, l3hi) are hoisted by the caller.
fn certified_pow3_interval_inner(
    a: &BigInt,
    b: &BigInt,
    p: usize,
    l3lo: &BigInt,
    l3hi: &BigInt,
) -> (BigInt, BigInt) {
    let m: usize = 60;
    let sc = BigInt::from(3u32).pow((p + m) as u32);
    let two_p = BigInt::from(3u32).pow(2 * p as u32);
    let u1n = b * l3hi;
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
        let lo_k = &tklo * a * l3lo / (&kd * &two_p);
        let hi_k = &tkhi * b * l3hi / (&kd * &two_p);
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
/// first k_prime digits are ≠ 2, `None` means the interval stayed ambiguous
/// (caller treats as deep). Precision doubles on ambiguity but the answer
/// always concerns exactly the first k_prime digits.
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
    let mut p = k_prime + 4;
    loop {
        if p > 512 {
            return None;
        }
        let p_hi = p + 64;
        let (alo, ahi, l3lo, l3hi, s_hi) = cached_precision(p_hi);
        let nb = BigInt::from(n);
        let nlo = &nb * &alo;
        let nhi = &nb * &ahi;
        let flo = &nlo / &s_hi;
        let fhi = &nhi / &s_hi;
        if &flo != &fhi {
            p *= 2;
            continue;
        }
        let kp = &flo * &s_hi;
        let a = &nlo - &kp;
        let b = &nhi - &kp;
        let (ylo, yhi) = certified_pow3_interval_inner(&a, &b, p_hi, &l3lo, &l3hi);
        let sm = pow3_64();
        let ylo_p = &ylo / &sm;
        let yhi_p = (&yhi + &sm - 1) / &sm;
        let bound = BigInt::from(3u32).pow((p + 1) as u32);
        if &yhi_p >= &bound {
            p *= 2;
            continue;
        }
        let r = digits_of(&ylo_p, p);
        let r_hi = digits_of(&yhi_p, p);
        if r[..k_prime] == r_hi[..k_prime] {
            return Some(r[..k_prime].iter().any(|&d| d == 2));
        }
        p *= 2;
    }
}

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
        let n = 464_263_536u128;
        assert_eq!(leading_digits_have_two(n, 50), Some(false));
        assert_eq!(leading_digits_have_two(n, 51), Some(true));
    }
}