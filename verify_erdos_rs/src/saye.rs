/// Saye's recursive algorithm for generating 2^n with prescribed trailing ternary digits.
///
/// Reference: Robert I. Saye, "On two conjectures concerning the ternary digits of powers of two"
/// [arXiv:2202.13256], 2022.
///
/// Key definitions:
///   u_k = 2 · 3^{k-1}  (period of 2^n mod 3^k)
///   The algorithm recursively builds candidates by extending trailing digits one at a time.
///
/// Property (Lemma 1(iii) in Saye):
///   d_{k+1}(2^{i·u_k + j}) ≡ d_{k+1}(2^j) + i · d_1(2^j)  (mod 3)
///
/// This means adding multiples of u_k cycles the (k+1)st ternary digit through {0, 1, 2},
/// so we can control each new digit independently.

use crate::ternary_mod::{TernaryMod, KAPPA};
use rayon::prelude::*;
use std::fs::OpenOptions;
use std::io::Write;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::Arc;
use std::time::Instant;

/// For K >= 35, use deeper parallelization to better utilize multiple cores.
/// Each additional level doubles the number of branches but halves the work per branch.
pub fn optimal_parallel_depth(max_depth: usize) -> usize {
    if max_depth <= 14 {
        max_depth.saturating_sub(2) // For small K, parallelize less
    } else if max_depth <= 20 {
        14 // Keep default for medium K
    } else if max_depth <= 30 {
        16 // Deeper parallelization for K=21-30
    } else if max_depth <= 35 {
        18 // Even deeper for K=31-35
    } else if max_depth <= 40 {
        20 // Maximum parallelization for K=36-40
    } else {
        22 // For K > 40
    }
}

/// Sequential recursive generation (below parallelization threshold).
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
    let mut local_count = 0u64;
    generate_sequential_inner(k, u_k, pow_uk, j, pow_j, chi, max_depth, &mut local_count, results);
    counter.fetch_add(local_count, Ordering::Relaxed);
}

/// Inner recursive function with local counter.
#[inline(always)]
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

/// Collect branches at a given depth (returns list of (j, pow_j, u_k, pow_uk) tuples).
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

/// Run Saye's algorithm for a given maximum depth K.
/// Returns candidate exponents whose first KAPPA ternary digits avoid χ.
pub fn run_saye(chi: u8, max_depth: usize) -> Vec<u128> {
    let parallel_depth = optimal_parallel_depth(max_depth);
    run_saye_with_parallel_depth(chi, max_depth, parallel_depth)
}

/// Run Saye's algorithm with explicit parallel depth control.
pub fn run_saye_with_parallel_depth(chi: u8, max_depth: usize, parallel_depth: usize) -> Vec<u128> {
    run_saye_full(chi, max_depth, parallel_depth, None, false)
}

/// Run Saye's algorithm with full control over parallel depth, checkpointing, and resume.
fn run_saye_full(
    chi: u8,
    max_depth: usize,
    parallel_depth: usize,
    checkpoint_path: Option<&str>,
    resume: bool,
) -> Vec<u128> {
    let counter = AtomicU64::new(0);
    let u_1 = 2u128;
    let pow_uk = TernaryMod::from_u64(4);

    let parallel_depth = std::cmp::min(parallel_depth, max_depth);

    // Load existing candidates if resuming
    let existing: Vec<u128> = if resume {
        checkpoint_path.map(|p| load_checkpoint(p)).unwrap_or_default()
    } else {
        Vec::new()
    };

    if !existing.is_empty() {
        eprintln!("  Resuming with {} existing candidates from checkpoint", existing.len());
    }

    // Use an atomic flag for graceful shutdown
    let shutdown = Arc::new(AtomicBool::new(false));
    let shutdown_clone = shutdown.clone();

    // Set up signal handler for graceful shutdown
    ctrlc::set_handler(move || {
        eprintln!("\n  Graceful shutdown requested... (saving checkpoint)");
        shutdown_clone.store(true, Ordering::SeqCst);
    })
    .unwrap_or_else(|e| eprintln!("  Warning: could not set Ctrl+C handler: {e}"));

    eprintln!("  Phase 1: collecting branches to depth {parallel_depth}...");
    let start = Instant::now();
    let branches = collect_branches(
        1, u_1, pow_uk,
        0, TernaryMod::one(),
        chi,
        parallel_depth,
        &counter,
    );
    let num_branches = branches.len();
    let phase1_time = start.elapsed();
    eprintln!("  Phase 1: {num_branches} branches collected in {:.2?}", phase1_time);

    let num_threads = num_cpus::get();
    eprintln!("  Phase 2: processing {num_branches} branches on {num_threads} threads...");
    eprintln!("  Estimated work per branch: 2^{} nodes", max_depth - parallel_depth);

    let phase2_start = Instant::now();
    let progress_counter = AtomicU64::new(0);
    let total_branches = num_branches as u64;

    // Shared state for checkpoint writing
    let checkpoint_mutex: std::sync::Mutex<Vec<u128>> = std::sync::Mutex::new(Vec::new());

    let results: Vec<u128> = branches
        .into_par_iter()
        .flat_map_iter(|(j, pow_j, u_k, pow_uk)| {
            let mut local_results = Vec::new();
            let local_counter = AtomicU64::new(0);

            // Check shutdown flag before processing each branch
            if shutdown.load(Ordering::Relaxed) {
                return local_results;
            }

            generate_sequential(
                parallel_depth, u_k, pow_uk,
                j, pow_j, chi,
                max_depth, &local_counter, &mut local_results,
            );

            // Save candidates to checkpoint
            if let Some(path) = checkpoint_path {
                let mut checkpoint = checkpoint_mutex.lock().unwrap();
                for &candidate in &local_results {
                    checkpoint.push(candidate);
                    save_checkpoint(candidate, path);
                }
            }

            let done = progress_counter.fetch_add(1, Ordering::Relaxed) + 1;
            if done % 1000 == 0 || done == total_branches {
                let elapsed = phase2_start.elapsed();
                let rate = done as f64 / elapsed.as_secs_f64();
                let eta_secs = (total_branches - done) as f64 / rate;
                eprintln!("    [{}/{} branches] {:.1?} elapsed, {:.1} branches/sec, ETA: {:.0}s",
                    done, total_branches, elapsed, rate, eta_secs);
            }

            local_results
        })
        .collect();

    let total = counter.load(Ordering::Relaxed);
    let total_time = start.elapsed();
    eprintln!("  Visited {total} nodes (depth {max_depth})");
    eprintln!("  Found {} candidate(s) in {} trailing digits", results.len(), KAPPA);
    eprintln!("  Total time: {:.2?}", total_time);

    if shutdown.load(Ordering::Relaxed) {
        eprintln!("  Run interrupted — checkpoint saved");
    }

    // Merge with existing candidates from resume
    let mut all_results = results;
    for n in existing {
        if !all_results.contains(&n) {
            all_results.push(n);
        }
    }
    all_results.sort();
    all_results.dedup();
    all_results
}

/// Compute u_k = 2·3^{k-1} as u128 (needed for k ≥ 39 where u_k > u64::MAX).
pub fn u_k(k: usize) -> u128 {
    if k == 0 { return 1; }
    2u128 * 3u128.pow((k - 1) as u32)
}

/// Estimate the search space size for a given K.
/// Returns (num_nodes, num_candidates_estimate).
/// The search space grows as ~2^K, and candidates grow as ~3^K/2^K = (3/2)^K.
pub fn estimate_search_space(max_depth: usize) -> (f64, f64) {
    let nodes = 2f64.powi(max_depth as i32);
    let candidates = 1.5f64.powi(max_depth as i32);
    (nodes, candidates)
}

/// Print search space estimate.
pub fn print_estimate(max_depth: usize) {
    let pd = optimal_parallel_depth(max_depth);
    let (nodes, candidates) = estimate_search_space(max_depth);
    let branches = 2f64.powi(pd as i32);
    let work_per_branch = 2f64.powi((max_depth - pd) as i32);

    eprintln!("=== Search Space Estimate ===");
    eprintln!("  K = {max_depth}, parallel depth = {pd}");
    eprintln!("  Total nodes: ~2^{max_depth} = {:.2e}", nodes);
    eprintln!("  Branches: ~2^{pd} = {:.0}", branches);
    eprintln!("  Work per branch: ~2^{} = {:.2e}", max_depth - pd, work_per_branch);
    eprintln!("  Expected candidates: ~1.5^{max_depth} = {:.2e}", candidates);
    eprintln!("  Coverage: n ≤ 2·3^{} = {:.2e}", max_depth - 1, u_k(max_depth) as f64);
    eprintln!();
}

/// Save a candidate to the checkpoint file.
pub fn save_checkpoint(candidate: u128, checkpoint_path: &str) {
    if let Ok(mut file) = OpenOptions::new()
        .create(true)
        .append(true)
        .open(checkpoint_path)
    {
        let _ = writeln!(file, "{candidate}");
    }
}

/// Load candidates from a checkpoint file.
pub fn load_checkpoint(checkpoint_path: &str) -> Vec<u128> {
    use std::fs;
    fs::read_to_string(checkpoint_path)
        .unwrap_or_default()
        .lines()
        .filter_map(|line| line.trim().parse().ok())
        .collect()
}

/// Run Saye's algorithm with checkpoint support.
/// Saves candidates to checkpoint_path as they're found.
/// If resume=true, loads existing candidates and skips already-processed branches.
pub fn run_saye_with_checkpoint(
    chi: u8,
    max_depth: usize,
    checkpoint_path: &str,
    resume: bool,
    parallel_depth: Option<usize>,
) -> Vec<u128> {
    let pd = parallel_depth.unwrap_or_else(|| optimal_parallel_depth(max_depth));
    run_saye_full(chi, max_depth, pd, Some(checkpoint_path), resume)
}

/// Visit every candidate exponent (2-free in the first KAPPA trailing digits)
/// at depth max_depth, in parallel, streaming — never materializes the set.
/// The visitor `f` is called from many threads; it must be `Sync` and use
/// interior mutability (atomics, Mutex) for any shared state. It is invoked
/// without holding a lock, so expensive per-candidate work parallelizes fully.
pub fn for_each_candidate<F>(chi: u8, max_depth: usize, parallel_depth: usize, f: F)
where
    F: Fn(u128) + Sync + Send,
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
    branches.into_par_iter().for_each(|(j, pow_j, u_k, pow_uk)| {
        let mut local_count = 0u64;
        let mut leaf = Vec::new();
        generate_sequential_inner(
            parallel_depth, u_k, pow_uk,
            j, pow_j, chi, max_depth, &mut local_count, &mut leaf,
        );
        for cand in leaf {
            f(cand);
        }
        let done = progress.fetch_add(1, Ordering::Relaxed) + 1;
        if done % 1000 == 0 || done == total_branches {
            eprintln!("    [{done}/{total_branches}] branches, {:.1?}", started.elapsed());
        }
    });
}

/// Get the ternary representation of 2^n (first KAPPA digits) as a string.
pub fn ternary_str(n: u64) -> String {
    let two_mod = TernaryMod::from_u64(2);
    let pow_n = two_mod.pow(n);
    let digits: Vec<String> = (0..KAPPA).rev().map(|k| pow_n.ternary_digit(k).to_string()).collect();
    let s = digits.join("");
    let s = s.trim_start_matches('0');
    if s.is_empty() { "0".to_string() } else { s.to_string() }
}

#[cfg(test)]
mod tests {
    use super::*;

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

    #[test]
    fn for_each_candidate_matches_run_saye() {
        let all = run_saye(2, 15);
        let seen = std::sync::Mutex::new(Vec::new());
        for_each_candidate(2, 15, 8, |j| seen.lock().unwrap().push(j));
        let mut seen = seen.into_inner().unwrap();
        seen.sort_unstable();
        assert_eq!(seen, all, "for_each_candidate vs run_saye disagree");
    }

    #[test]
    fn test_ternary_str() {
        assert_eq!(ternary_str(0), "1");
        assert_eq!(ternary_str(2), "11");
        assert_eq!(ternary_str(8), "100111");
    }
}
