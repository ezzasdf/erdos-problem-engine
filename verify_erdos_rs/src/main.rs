mod ternary_mod;
mod saye;
mod leading;
mod two_sided;

use num_traits::identities::Zero;
use std::env;
use std::time::Instant;

fn main() {
    let args: Vec<String> = env::args().collect();

    if args.len() > 1 && args[1] == "--help" {
        println!("Usage:");
        println!("  verify_erdos                              Brute-force mode (n=9..1M)");
        println!("  verify_erdos <max_n>                      Brute-force mode (n=9..max_n)");
        println!("  verify_erdos --saye K [chi] [pd]          Saye mode (K=depth, chi=digit, pd=parallel_depth)");
        println!("  verify_erdos --estimate K                 Estimate search space for depth K");
        println!("  verify_erdos --saye K chi pd --checkpoint PATH  Save candidates to file");
        println!("  verify_erdos --saye K chi pd --resume PATH     Resume from checkpoint");
        println!("  verify_erdos --two-sided K [k_prime]           Two-sided pruning engine");
        println!();
        println!("Saye mode examples:");
        println!("  verify_erdos --saye 20                    K=20, auto parallel depth");
        println!("  verify_erdos --saye 38 2                  K=38, forbidden digit 2");
        println!("  verify_erdos --saye 40 2 20               K=40, parallel depth 20");
        println!("  verify_erdos --saye 40 2 20 --checkpoint /tmp/k40.txt");
        println!();
        println!("Coverage: K=40 covers n ≤ 2·3^39 ≈ 8.1×10^18");
        return;
    }

    if args.len() > 1 && args[1] == "--estimate" {
        let k: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(40);
        saye::print_estimate(k);
        return;
    }

    if args.len() > 1 && args[1] == "--saye" {
        // Saye's recursive algorithm mode
        // Parse positional args from --saye K [chi] [pd], skipping flags
        let positional: Vec<&String> = args.iter().skip(2)
            .filter(|a| !a.starts_with("--"))
            .collect();
        let max_depth: usize = positional.get(0).and_then(|s| s.parse().ok()).unwrap_or(15);
        let chi: u8 = positional.get(1).and_then(|s| s.parse().ok()).unwrap_or(2);
        let parallel_depth: Option<usize> = positional.get(2).and_then(|s| s.parse().ok());

        // Check for --checkpoint or --resume flags
        let checkpoint_path = args.iter().position(|a| a == "--checkpoint")
            .and_then(|i| args.get(i + 1).cloned());
        let resume_path = args.iter().position(|a| a == "--resume")
            .and_then(|i| args.get(i + 1).cloned());

        println!("=== Saye's Recursive Algorithm ===");
        println!("Forbidden digit: {chi}");
        println!("Max depth K = {max_depth}");
        println!("Covers n ≤ {} (= 2·3^{})", saye::u_k(max_depth), max_depth - 1);
        println!("Trailing digit precision: {} (mod 3^{})", ternary_mod::KAPPA, ternary_mod::KAPPA);
        if let Some(pd) = parallel_depth {
            println!("Parallel depth: {pd} (user-specified)");
        } else {
            println!("Parallel depth: {} (auto-optimized)", saye::optimal_parallel_depth(max_depth));
        }
        if let Some(ref path) = checkpoint_path {
            println!("Checkpoint file: {path}");
        }
        if let Some(ref path) = resume_path {
            println!("Resume from: {path}");
        }
        println!();

        let start = Instant::now();
        let candidates = match (checkpoint_path.as_deref(), resume_path.as_deref()) {
            (Some(cp), Some(_rp)) => saye::run_saye_with_checkpoint(chi, max_depth, cp, true, parallel_depth),
            (Some(cp), None) => saye::run_saye_with_checkpoint(chi, max_depth, cp, false, parallel_depth),
            (None, Some(rp)) => saye::run_saye_with_checkpoint(chi, max_depth, rp, true, parallel_depth),
            (None, None) => match parallel_depth {
                Some(pd) => saye::run_saye_with_parallel_depth(chi, max_depth, pd),
                None => saye::run_saye(chi, max_depth),
            },
        };
        let algo_time = start.elapsed();

        println!("  Found {} candidate(s) in {} trailing digits", candidates.len(), ternary_mod::KAPPA);
        println!("  Algo time: {:.2?}", algo_time);
        println!();

        // Cross-check: for n <= 1M, do full brute-force verification
        let cross_check_limit: u128 = 1_000_000;
        let mut fully_verified = Vec::new();
        let mut false_positives = Vec::new();

        println!("--- Cross-checking candidates with brute-force (n ≤ {cross_check_limit}) ---");
        let verify_start = Instant::now();

        for &n in &candidates {
            if n <= cross_check_limit {
                // Full brute-force check
                let two = num_bigint::BigUint::from(2u32);
                let three = num_bigint::BigUint::from(3u32);
                let val = two.pow(n as u32);
                let mut tmp = val;
                let mut has_chi = false;
                while !tmp.is_zero() {
                    if &tmp % &three == num_bigint::BigUint::from(chi) {
                        has_chi = true;
                        break;
                    }
                    tmp /= &three;
                }
                if !has_chi {
                    fully_verified.push(n);
                    let ts = saye::ternary_str(n as u64);
                    println!("  VERIFIED: n={n}: 2^{n} ternary = {ts}");
                } else {
                    false_positives.push(n);
                    let ts = saye::ternary_str(n as u64);
                    println!("  FALSE POSITIVE: n={n}: 2^{n} ternary = {ts} (has digit {chi} in full expansion)");
                }
            }
        }

        // For large candidates, just report them
        let large_candidates: Vec<u128> = candidates.iter().copied().filter(|&n| n > cross_check_limit).collect();
        if !large_candidates.is_empty() {
            println!();
            println!("--- Large candidates (54-digit check only, n > {cross_check_limit}) ---");
            for &n in large_candidates.iter().take(10) {
                let ts = saye::ternary_str(n as u64);
                println!("  n={n}: 2^{n} ternary (54 digits) = {ts}");
            }
            if large_candidates.len() > 10 {
                println!("  ... and {} more", large_candidates.len() - 10);
            }
        }

        let verify_time = verify_start.elapsed();
        let total_time = start.elapsed();

        println!();
        println!("=== Summary ===");
        println!("  Candidates from algorithm: {}", candidates.len());
        println!("  Fully verified (brute-force): {}", fully_verified.len());
        println!("  False positives (digit {chi} found beyond 54 digits): {}", false_positives.len());
        println!("  Large candidates (54-digit check only): {}", large_candidates.len());
        if fully_verified.is_empty() && false_positives.is_empty() {
            println!("  No counterexamples found — conjecture holds for n ≤ {}", saye::u_k(max_depth));
        } else if !fully_verified.is_empty() {
            println!("  Counterexamples found: {:?}", fully_verified);
        }
        println!("  Verification time: {:.2?}", verify_time);
        println!("  Total time: {:.2?}", total_time);

    } else if args.len() > 1 && args[1] == "--two-sided" {
        let k: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(38);
        let k_prime: usize = args.get(3).and_then(|s| s.parse().ok()).unwrap_or(70);
        let chi: u8 = 2;
        let parallel_depth = saye::optimal_parallel_depth(k);
        println!("=== Two-Sided Search (K={k}, k_prime={k_prime}) ===");
        println!("Coverage: n ≤ {}", saye::u_k(k));
        println!("Parallel depth: {parallel_depth}");
        let rep = two_sided::run_two_sided(k, k_prime, chi, parallel_depth);
        println!("{}", two_sided::report_line(&rep, k, k_prime, chi));
        return;
    } else {
        // Brute-force mode (default)
        let max_n: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1_000_000);

        println!("=== Brute-Force Verification ===");
        println!("Checking n from 9 to {max_n}");
        println!();

        let start = Instant::now();
        let mut counterexamples = Vec::new();
        let mut val: num_bigint::BigUint = num_bigint::BigUint::from(1u32) << 9;
        let two = num_bigint::BigUint::from(2u32);
        let three = num_bigint::BigUint::from(3u32);

        for n in 9..=max_n {
            let mut tmp = val.clone();
            let mut has_two = false;
            while !tmp.is_zero() {
                if &tmp % &three == num_bigint::BigUint::from(2u32) {
                    has_two = true;
                    break;
                }
                tmp /= &three;
            }
            if !has_two {
                counterexamples.push(n);
                println!("  COUNTEREXAMPLE: n={n}");
            }
            val *= &two;
        }

        let elapsed = start.elapsed();

        println!("\nResults:");
        println!("  Checked n from 9 to {max_n}");
        println!("  Counterexamples: {}", counterexamples.len());
        println!("  Time: {:.2?}", elapsed);
    }
}
