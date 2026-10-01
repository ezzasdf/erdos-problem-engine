//! Two-sided pruning engine: Saye trailing-digit candidates + certified
//! leading-digit check. Completeness (spec): if `deep == {0,2,8}` and small n
//! are brute-forced, every n <= 2·3^{K-1} is verified.

use crate::leading::leading_digits_have_two;
use crate::saye::{for_each_candidate, u_k};
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn deep_set_is_known_solutions() {
        for k in [10usize, 15, 20, 25] {
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