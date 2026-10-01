/// Fixed-precision arithmetic modulo 3^KAPPA.
///
/// Represented as a number in base B = 3^DIGIT_BITS, stored as [d0, d1, ..., d_{NUM_DIGITS-1}]
/// where the value is d0 + d1*B + d2*B^2 + ... .
///
/// Following Saye's approach: DIGIT_BITS = 18, NUM_DIGITS = 3 → KAPPA = 54 ternary digits.
/// This covers 2^n for n up to about 3^54 ≈ 5.9 × 10²⁵.

const DIGIT_BITS: u32 = 18;
const BASE: u64 = 3u64.pow(DIGIT_BITS); // 3^18 = 387,420,489
const NUM_DIGITS: usize = 3;
pub const KAPPA: usize = (DIGIT_BITS as usize) * NUM_DIGITS; // 54

/// A number mod 3^KAPPA, stored in base 3^18.
#[derive(Clone, Copy, Debug)]
pub struct TernaryMod {
    /// digits[0] + digits[1]*B + digits[2]*B^2  (mod 3^KAPPA)
    digits: [u64; NUM_DIGITS],
}

impl TernaryMod {
    /// Zero.
    pub fn zero() -> Self {
        Self { digits: [0; NUM_DIGITS] }
    }

    /// One.
    pub fn one() -> Self {
        Self { digits: [1, 0, 0] }
    }

    /// Create from a u64 value.
    pub fn from_u64(mut n: u64) -> Self {
        let mut d = [0u64; NUM_DIGITS];
        for i in 0..NUM_DIGITS {
            d[i] = n % BASE;
            n /= BASE;
        }
        Self { digits: d }
    }

    /// Multiply two numbers mod 3^KAPPA.
    /// Uses schoolbook multiplication with modular reduction.
    pub fn mul(self, other: &Self) -> Self {
        let mut result = [0u64; NUM_DIGITS];

        // Schoolbook multiplication
        for i in 0..NUM_DIGITS {
            if self.digits[i] == 0 { continue; }
            let mut carry = 0u64;
            for j in 0..NUM_DIGITS - i {
                // self.digits[i] * other.digits[j] can be up to (3^18-1)^2 ≈ 1.5×10^17 < 2^63
                let prod = self.digits[i] * other.digits[j] + result[i + j] + carry;
                result[i + j] = prod % BASE;
                carry = prod / BASE;
            }
        }

        // Modular reduction: since BASE = 3^DIGIT_BITS, and we compute mod BASE^NUM_DIGITS,
        // the result is already reduced (no overflow past NUM_DIGITS digits).
        Self { digits: result }
    }

    /// Compute self^n mod 3^KAPPA using square-and-multiply.
    pub fn pow(mut self, mut exp: u64) -> Self {
        let mut result = Self::one();
        while exp > 0 {
            if exp & 1 == 1 {
                result = result.mul(&self);
            }
            self = self.mul(&self);
            exp >>= 1;
        }
        result
    }

    /// Extract the k-th ternary digit (0-indexed from least significant).
    /// Digit k means the coefficient of 3^k.
    pub fn ternary_digit(&self, k: usize) -> u8 {
        let word = k / (DIGIT_BITS as usize);
        let offset = k % (DIGIT_BITS as usize);
        if word >= NUM_DIGITS {
            return 0;
        }
        ((self.digits[word] / 3u64.pow(offset as u32)) % 3) as u8
    }

    /// Check if any ternary digit in range [from, to) equals `digit`.
    /// Returns the position of the first occurrence, or None.
    pub fn find_digit(&self, digit: u8, from: usize, to: usize) -> Option<usize> {
        for k in from..to {
            if self.ternary_digit(k) == digit {
                return Some(k);
            }
        }
        None
    }

    /// Check if any ternary digit in [0, to) equals `digit`.
    pub fn has_digit(&self, digit: u8, to: usize) -> bool {
        self.find_digit(digit, 0, to).is_some()
    }

    /// Extract all ternary digits as a Vec (least significant first).
    pub fn to_ternary_vec(&self, num_digits: usize) -> Vec<u8> {
        (0..num_digits).map(|k| self.ternary_digit(k)).collect()
    }

    /// Get the underlying value as u64 (only valid if < BASE^NUM_DIGITS, which it always is).
    pub fn to_u64(&self) -> u64 {
        let mut result = 0u64;
        for i in (0..NUM_DIGITS).rev() {
            result = result * BASE + self.digits[i];
        }
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic() {
        let a = TernaryMod::from_u64(256);
        // 256 in ternary: 100111
        assert_eq!(a.ternary_digit(0), 1);
        assert_eq!(a.ternary_digit(1), 1);
        assert_eq!(a.ternary_digit(2), 1);
        assert_eq!(a.ternary_digit(3), 0);
        assert_eq!(a.ternary_digit(4), 0);
        assert_eq!(a.ternary_digit(5), 1);
    }

    #[test]
    fn test_mul() {
        let two = TernaryMod::from_u64(2);
        let four = two.mul(&two);
        assert_eq!(four.to_u64(), 4);

        let eight = four.mul(&two);
        assert_eq!(eight.to_u64(), 8);
    }

    #[test]
    fn test_pow() {
        let two = TernaryMod::from_u64(2);
        let p8 = two.pow(8);
        assert_eq!(p8.to_u64(), 256);

        // 256 in ternary: 100111 (no digit 2)
        assert!(!p8.has_digit(2, KAPPA));
    }

    #[test]
    fn test_periodicity() {
        // u_1 = 2·3^0 = 2: 2^2 ≡ 1 (mod 3)
        let two = TernaryMod::from_u64(2);
        let four = two.pow(2);
        assert_eq!(four.ternary_digit(0), 1); // 4 = 11_3, last digit 1

        // u_2 = 2·3^1 = 6: 2^6 = 64 ≡ 1 (mod 9)
        let p6 = two.pow(6);
        assert_eq!(p6.ternary_digit(0), 1); // 64 mod 3 = 1
        assert_eq!(p6.ternary_digit(1), 0); // 64 mod 9 = 1 → digit 1 = 0
    }
}
