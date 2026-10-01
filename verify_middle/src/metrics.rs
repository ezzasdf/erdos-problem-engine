pub struct WindowMetrics {
    pub freq: f64,
    pub longest_free: usize,
    pub all_free: bool,
    pub first_two: Option<usize>,
}

pub fn window_metrics(digits: &[u8], a: usize, b: usize) -> WindowMetrics {
    let win = &digits[a.min(digits.len())..b.min(digits.len())];
    let ln = win.len();
    let n2 = win.iter().filter(|&&d| d == 2).count();
    let freq = if ln == 0 { 0.0 } else { n2 as f64 / ln as f64 };
    let mut longest = 0usize;
    let mut cur = 0usize;
    for &d in win {
        if d == 2 {
            cur = 0;
        } else {
            cur += 1;
            if cur > longest {
                longest = cur;
            }
        }
    }
    let all_free = n2 == 0;
    let first_two = win.iter().position(|&d| d == 2).map(|off| a + off);
    WindowMetrics { freq, longest_free: longest, all_free, first_two }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn metrics_on_known_window() {
        // digits 1,1,0,2,1 (least-significant first) = 1 + 3 + 27 + 81 = 112
        let digits = vec![1u8, 1, 0, 2, 1];
        // window [2,5) = [0,2,1]
        let m = window_metrics(&digits, 2, 5);
        assert_eq!(m.longest_free, 1);
        assert!(!m.all_free);
        assert_eq!(m.first_two, Some(3));
        // window [0,3) = [1,1,0]
        let m2 = window_metrics(&digits, 0, 3);
        assert_eq!(m2.freq, 0.0);
        assert_eq!(m2.longest_free, 3);
        assert!(m2.all_free);
        assert_eq!(m2.first_two, None);
    }
}