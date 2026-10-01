use num_bigint::{BigInt, BigUint};

use crate::mantissa::GUARDS;

/// base-3 big-endian digits of v, left-aligned and zero-padded to length
/// p + GUARDS (matches `Mantissa`'s layout: reportable prefix at 0..=p).
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
    // k_terms = terms needed so sc·1.1^K/K! < 1, via Stirling ln(K!) ≥ K·lnK − K.
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
    let mut tklo = sc.clone(); // lower floor term, ≤ true T_k·sc
    let mut tkhi = sc.clone(); // upper floor term, ≥ true T_k·sc − k
    for k in 1..=k_terms as u64 {
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
    let kn = BigInt::from(k_terms as i64);
    let tail_num = &tkhi * &u1n * BigInt::from((k_terms + 2) as i64) * &u1d;
    let tail_den = (&kn + 1) * &u1d * (BigInt::from((k_terms + 2) as i64) * &u1d - &u1n);
    let tail = (&tail_num + &tail_den - 1) / &tail_den;
    let upper = &hi + &kn + &tail;
    // final rounding to scale 3^p: floor/ceil of (internal / 3^m)
    let sm = BigInt::from(3u32).pow(m as u32);
    (&lo / &sm, (upper + &sm - 1) / &sm)
}

/// Certified digits of y_n = 3^{frac(n·α)} to p digits, plus L(n) = ⌊nα⌋+1.
/// Returns (digits, len); digits has length p + GUARDS with the reportable
/// prefix (first p+1 entries) an exact-or-one-low truncation of y_n.
/// Recurses with doubled precision when the certified interval is too wide
/// or n·α straddles an integer.
pub fn escalate(n: u64, p: usize) -> (Vec<u8>, u64) {
    // Exact path when L(n) ≤ p+1 (2^n < 3^(p+1)): y_n·3^p = 2^n·3^(p-L+1) is
    // then an integer multiple of 3^q for any q ≤ p-L+1, which any interval
    // computation can only bracket to width 2 (systematic straddle, so the
    // recursive interval path would never terminate).
    let small_limit = (p + 1) as f64 * 1.585;
    if (n as f64) <= small_limit {
        let two_n = BigUint::from(2u8).pow(n as u32);
        let l = two_n.to_str_radix(3).len() as u64;
        let t = two_n * BigUint::from(3u8).pow((p - l as usize + 1) as u32);
        return (digits_of(&BigInt::from(t), p), l);
    }
    // Interval path: α's certified interval is ~2·need ≈ 3.4·p_hi units wide at
    // its own scale, so computing at p_hi = p + 64 resolves n·α to sub-unit
    // precision at scale 3^p for n up to ~10^40. The 3^frac interval is then
    // down-converted once (straddle probability ≈ W/3^64 ≈ 0 for n ≤ 10^9).
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
        assert!(&hi - &lo < BigInt::from(1000i64), "interval too wide");
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