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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::stream::Stream;

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