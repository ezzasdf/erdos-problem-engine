pub struct Stream {
    pub n: usize,
    pub digits: Vec<u8>,
}

impl Stream {
    pub fn new() -> Self {
        Stream { n: 0, digits: vec![1] }
    }

    pub fn double(&mut self) {
        let mut carry: u8 = 0;
        for d in self.digits.iter_mut() {
            let s = 2 * *d + carry;
            *d = s % 3;
            carry = s / 3;
        }
        if carry != 0 {
            self.digits.push(carry);
        }
        self.n += 1;
    }

    pub fn to_n(&mut self, n: usize) {
        while self.n < n {
            self.double();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn base3(mut m: usize) -> Vec<u8> {
        let mut v = Vec::new();
        while m > 0 {
            v.push((m % 3) as u8);
            m /= 3;
        }
        v
    }

    #[test]
    fn doubling_matches_powers_of_two() {
        let mut s = Stream::new();
        for n in 0..30 {
            assert_eq!(s.digits, base3(1usize << n), "digits wrong at n={n}");
            s.double();
        }
    }
}