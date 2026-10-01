mod certified;
mod mantissa;
mod metrics;
mod stream;

use certified::escalate;
use mantissa::{Mantissa, DEFAULT_P, exact_f};
use metrics::window_metrics;
use num_bigint::BigUint;
use stream::Stream;
use std::env;
use std::fs::File;
use std::io::{BufWriter, Write};

/// Certified f(n), escalating when the first-2 is beyond the reportable window.
fn certified_f(m: &mut Mantissa) -> usize {
    loop {
        if let Some(f) = m.f_scan() {
            return f;
        }
        if (m.p as u64) >= m.len {
            return m.len as usize;
        }
        let (digits, len) = escalate(m.n, m.p * 4);
        *m = Mantissa::from_parts(m.n, m.p * 4, digits, len);
    }
}

/// Advance n -> n+1, escalating until the step is certified.
fn advance(m: &mut Mantissa) {
    loop {
        if m.step().is_ok() {
            return;
        }
        let (digits, len) = escalate(m.n, m.p * 4);
        *m = Mantissa::from_parts(m.n, m.p * 4, digits, len);
    }
}

fn first2_check(nmax: u64, p: usize) {
    let mut m = Mantissa::new(p);
    let mut s = Stream::new();
    for n in 0..=nmax {
        let fex = exact_f(&s.digits);
        let fm = certified_f(&mut m);
        assert_eq!(fm, fex, "f mismatch at n={n}");
        advance(&mut m);
        s.double();
        if n % 20_000 == 0 {
            eprintln!("check n={n} p={}", m.p);
        }
    }
    println!("first2-check ok through n={nmax} at p={p}");
}

fn first2_events(nmax: u64, out_path: &str, grid: &[usize]) {
    let lmax = *grid.iter().max().unwrap();
    let mut m = Mantissa::new(DEFAULT_P);
    let mut cnt = vec![0usize; lmax + 1];
    let mut ncnt = vec![0usize; lmax + 1];
    loop {
        let n = m.n;
        if n > nmax {
            break;
        }
        if n >= 9 {
            let f = certified_f(&mut m);
            let len = m.len as usize;
            for &l in grid {
                if l <= len {
                    ncnt[l] += 1;
                    if f >= l {
                        cnt[l] += 1;
                    }
                }
            }
        }
        advance(&mut m);
    }
    let mut w = BufWriter::new(File::create(out_path).expect("create csv"));
    writeln!(w, "L,N,P_f_ge_L").unwrap();
    for &l in grid {
        let p = cnt[l] as f64 / ncnt[l] as f64;
        writeln!(w, "{l},{},{p:.6}", ncnt[l]).unwrap();
    }
    println!("first2-events done through n={nmax}");
}

fn verify_records(path: &str) {
    let data = std::fs::read_to_string(path).expect("read csv");
    let mut lines = data.lines();
    let _header = lines.next();
    let mut verified = 0usize;
    for line in lines {
        let parts: Vec<&str> = line.split(',').collect();
        let n: u64 = parts[0].parse().unwrap();
        let f: usize = parts[1].parse().unwrap();
        let (digits, len) = escalate(n, DEFAULT_P);
        let mut m = Mantissa::from_parts(n, DEFAULT_P, digits, len);
        let fv = certified_f(&mut m);
        assert_eq!(fv, f, "record n={n} failed independent verification");
        verified += 1;
    }
    println!("verified {verified} records independently via 3^frac(n*alpha)");
}

fn first2(nmax: u64, out_path: &str) {
    let mut m = Mantissa::new(DEFAULT_P);
    let mut w = BufWriter::new(File::create(out_path).expect("create csv"));
    writeln!(
        w,
        "n,f,L,ratio,prefix,mantissa_precision,record_number,gap_from_previous_record"
    )
    .unwrap();
    let mut max_f = 0usize;
    let mut record_count = 0usize;
    let mut prev: Option<u64> = None;
    loop {
        let n = m.n;
        if n > nmax {
            break;
        }
        let f = certified_f(&mut m);
        if f > max_f {
            max_f = f;
            record_count += 1;
            let gap = n - prev.unwrap_or(0);
            let prefix: String = m.digits[..f].iter().map(|&d| (b'0' + d) as char).collect();
            let ratio = f as f64 / m.len as f64;
            writeln!(
                w,
                "{n},{f},{},{ratio:.10},{prefix},{},{record_count},{gap}",
                m.len, m.p
            )
            .unwrap();
            prev = Some(n);
        }
        advance(&mut m);
        if n % 10_000_000 == 0 {
            eprintln!("n={n} max_f={max_f} p={}", m.p);
        }
    }
    println!("== first-2 records: count={record_count} max_f={max_f} ==");
}

fn digit_at(digits: &[u8], pos: usize) -> u8 {
    if pos < digits.len() { digits[pos] } else { 0 }
}

fn analyze(nmax: usize, out_path: &str) {
    let mut s = Stream::new();
    let mut w = BufWriter::new(File::create(out_path).expect("create csv"));
    writeln!(
        w,
        "n,L,W,t_freq,t_long,t_free,t_first,m_freq,m_long,m_free,m_first,l_freq,l_long,l_free,l_first,t0,t1,m0,m1,l0"
    )
    .unwrap();

    let mut min_freq = [f64::MAX; 3];
    let mut min_freq_n = [0usize; 3];
    let mut max_run = [0usize; 3];
    let mut max_run_n = [0usize; 3];
    let mut all_free_count = [0usize; 3];

    for n in 9..=nmax {
        s.to_n(n);
        let digits = &s.digits;
        let l = digits.len();
        let wl = l / 3;
        let mid_end = (2 * l) / 3;
        let ws = [window_metrics(digits, 0, wl), window_metrics(digits, wl, mid_end),
                  window_metrics(digits, mid_end, l)];
        for (i, m) in ws.iter().enumerate() {
            if m.freq < min_freq[i] {
                min_freq[i] = m.freq;
                min_freq_n[i] = n;
            }
            if m.longest_free > max_run[i] {
                max_run[i] = m.longest_free;
                max_run_n[i] = n;
            }
            if m.all_free {
                all_free_count[i] += 1;
            }
        }
        writeln!(
            w,
            "{n},{l},{wl},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{}",
            ws[0].freq, ws[0].longest_free, ws[0].all_free,
            ws[0].first_two.map_or(-1, |p| p as i64),
            ws[1].freq, ws[1].longest_free, ws[1].all_free,
            ws[1].first_two.map_or(-1, |p| p as i64),
            ws[2].freq, ws[2].longest_free, ws[2].all_free,
            ws[2].first_two.map_or(-1, |p| p as i64),
            digit_at(digits, 0), digit_at(digits, 1), digit_at(digits, wl),
            digit_at(digits, wl + 1), digit_at(digits, mid_end),
        )
        .unwrap();
        if n % 100_000 == 0 {
            eprintln!("n={n}  L={l}");
        }
    }
    println!("== records ==");
    for (i, name) in ["trailing", "middle", "leading"].iter().enumerate() {
        println!(
            "{name}: min_freq={:.6} @n={}  max_2free_run={} @n={}  all_free_count={}",
            min_freq[i], min_freq_n[i], max_run[i], max_run_n[i], all_free_count[i]
        );
    }
}

fn verify(nmax: usize) {
    let two = BigUint::from(2u8);
    let modk = 3u64.pow(20); // independent low-order check on every n
    let mut s = Stream::new();
    let mut p = BigUint::from(1u8);
    let mut m: u64 = 1; // 2^n mod 3^20
    for n in 0..=nmax {
        // low-order independent check: stream digits [0,20) == base3 of (2^n mod 3^20)
        let mut low = Vec::new();
        let mut r = m;
        for _ in 0..20 {
            low.push((r % 3) as u8);
            r /= 3;
        }
        let k = s.digits.len().min(20);
        assert_eq!(&s.digits[..k], &low[..k], "low-digit mismatch at n={n}");

        // full independent check at checkpoints
        if n % 1000 == 0 {
            let base3 = p.to_str_radix(3);
            let rev: Vec<u8> = base3.bytes().rev().map(|b| (b - b'0') as u8).collect();
            assert_eq!(s.digits, rev, "full-digit mismatch at n={n}");
        }

        s.double();
        p *= &two;
        m = (2 * m) % modk;
    }
    println!("verify ok through n={nmax}");
}

fn events(nmax: usize, out_path: &str, grid: &[usize]) {
    let mut s = Stream::new();
    let mut w = BufWriter::new(File::create(out_path).expect("create csv"));
    writeln!(w, "L,K,N,P_A,P_B,P_AB,P_A_given_B,dev").unwrap();

    let kmax = *grid.iter().max().unwrap();
    let lmax = *grid.iter().max().unwrap();

    // per-(L,K) tallies over n with len >= max(L,K)
    let ng = grid.len();
    let mut ncnt = vec![vec![0usize; ng]; ng];
    let mut acnt = vec![vec![0usize; ng]; ng];
    let mut bcnt = vec![vec![0usize; ng]; ng];
    let mut abc = vec![vec![0usize; ng]; ng];

    for n in 9..=nmax {
        s.to_n(n);
        let digits = &s.digits;
        let len = digits.len();

        // trailing flags: no 2 in digits[0..K]
        let mut bflag = vec![true; kmax + 1];
        for k in 1..=kmax {
            if k <= len {
                bflag[k] = bflag[k - 1] && digits[k - 1] != 2;
            } else {
                bflag[k] = false; // undefined (len too short); won't be used
            }
        }
        // leading flags: no 2 in digits[len-L..len]
        let mut aflag = vec![true; lmax + 1];
        for l in 1..=lmax {
            if l <= len {
                let mut ok = true;
                for j in 0..l {
                    if digits[len - 1 - j] == 2 {
                        ok = false;
                        break;
                    }
                }
                aflag[l] = ok;
            } else {
                aflag[l] = false; // undefined
            }
        }

        for (i, &l) in grid.iter().enumerate() {
            if l > len {
                continue;
            }
            for (j, &k) in grid.iter().enumerate() {
                if k > len {
                    continue;
                }
                ncnt[i][j] += 1;
                if aflag[l] {
                    acnt[i][j] += 1;
                }
                if bflag[k] {
                    bcnt[i][j] += 1;
                }
                if aflag[l] && bflag[k] {
                    abc[i][j] += 1;
                }
            }
        }
        if n % 100_000 == 0 {
            eprintln!("events n={n}");
        }
    }

    for (i, &l) in grid.iter().enumerate() {
        for (j, &k) in grid.iter().enumerate() {
            let n = ncnt[i][j];
            let pa = acnt[i][j] as f64 / n as f64;
            let pb = bcnt[i][j] as f64 / n as f64;
            let pab = abc[i][j] as f64 / n as f64;
            let pagb = if bcnt[i][j] > 0 { abc[i][j] as f64 / bcnt[i][j] as f64 } else { 0.0 };
            let dev = pagb - pa;
            writeln!(w, "{l},{k},{n},{pa:.6},{pb:.6},{pab:.6},{pagb:.6},{dev:+.6}").unwrap();
        }
    }
    println!("== events summary ==");
    for (i, &l) in grid.iter().enumerate() {
        for (j, &k) in grid.iter().enumerate() {
            let n = ncnt[i][j];
            let pa = acnt[i][j] as f64 / n as f64;
            let pagb = if bcnt[i][j] > 0 { abc[i][j] as f64 / bcnt[i][j] as f64 } else { 0.0 };
            let dev = pagb - pa;
            println!("A_{l}|B_{k}: P(A)={pa:.4} P(A|B)={pagb:.4} (dev {dev:+.4}, N={n})");
        }
    }
}

fn main() {
    let args: Vec<String> = env::args().collect();
    match args.get(1).map(|s| s.as_str()) {
        Some("--analyze") => {
            let n: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(1_000_000);
            let out = args.get(3).cloned().unwrap_or_else(|| "results_m1.csv".to_string());
            analyze(n, &out);
        }
        Some("--events") => {
            let n: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(1_000_000);
            let out = args.get(3).cloned().unwrap_or_else(|| "events_m1.csv".to_string());
            let grid: Vec<usize> = args
                .get(4)
                .map(|g| g.split(',').filter_map(|x| x.parse().ok()).collect())
                .unwrap_or_else(|| vec![1, 2, 3, 4, 5, 6, 8, 10, 12, 16, 20, 24, 30]);
            events(n, &out, &grid);
        }
        Some("--verify") => {
            let n: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100_000);
            verify(n);
        }
        Some("--first2") => {
            let n: u64 = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(1_000_000_000);
            let out = args.get(3).cloned().unwrap_or_else(|| "first2_records.csv".to_string());
            first2(n, &out);
        }
        Some("--first2-check") => {
            let n: u64 = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100_000);
            let p: usize = args.get(3).and_then(|s| s.parse().ok()).unwrap_or(DEFAULT_P);
            first2_check(n, p);
        }
        Some("--first2-events") => {
            let n: u64 = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(1_000_000);
            let out = args.get(3).cloned().unwrap_or_else(|| "first2_events.csv".to_string());
            let grid: Vec<usize> = args
                .get(4)
                .map(|g| g.split(',').filter_map(|x| x.parse().ok()).collect())
                .unwrap_or_else(|| vec![1, 2, 3, 4, 5, 6, 8, 10, 12, 16, 20, 24, 30]);
            first2_events(n, &out, &grid);
        }
        Some("--first2-verify-records") => {
            let p = args.get(2).cloned().unwrap_or_else(|| "first2_records.csv".to_string());
            verify_records(&p);
        }
        _ => {
            println!("usage: verify_middle --analyze N out.csv | --events N out.csv L1,L2,.. | --verify NMAX | --first2 N out.csv | --first2-check NMAX [p] | --first2-events N out.csv L1,L2,.. | --first2-verify-records out.csv");
        }
    }
}