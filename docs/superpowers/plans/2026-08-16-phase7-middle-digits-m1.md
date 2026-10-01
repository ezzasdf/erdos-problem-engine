# Phase 7 M1: Middle-Digit Data Run — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Produce the first-ever dataset of middle-window ternary-digit statistics for `2ⁿ` (n ≤ 10⁶), cross-checked against independent implementations, as the validated core for Phases 7–9.

**Architecture:** Rust crate `verify_middle` implementing carry-chain streaming doubling of `2ⁿ` in base 3 (least-significant-first digit array), per-`n` window extraction + metrics, and a CSV writer. Two independent cross-checks (Rust `num-bigint` `pow`, Python `pow`) validate the digit stream. The Python script also computes the M2 independence test from the CSV.

**Tech Stack:** Rust (edition 2021, `num-bigint` for cross-check only), Python 3 (stdlib only, no numpy/scipy), Cargo. Existing pattern to mirror: `verify_erdos_rs` crate layout.

**Global Constraints**
- Repo root: `/media/playplatoon/New Volume/projects/erdos problem ternary expansion`
- No new third-party Python dependencies; Rust deps: `num-bigint` only.
- Windows (0-indexed, least-significant-first digit positions): trailing `[0, W)`, middle `[W, ⌊2L/3⌋)`, leading `[⌊2L/3⌋, L)`, where `L = len(digits)`, `W = L // 3`.
- Metrics per window: digit-2 frequency, longest 2-free run, all-2-free flag, absolute first-2 position.
- Results CSV must contain columns: `n,L,W,t_freq,t_long,t_free,t_first,m_freq,m_long,m_free,m_first,l_freq,l_long,l_free,l_first,t0,t1,m0,m1,l0`.
- Commit after each task (local git; push is deferred — do NOT attempt push).

---

### Task 1: Scaffold `verify_middle` crate + `Stream` (carry-chain doubling)

**Files:**
- Create: `verify_middle/Cargo.toml`
- Create: `verify_middle/src/stream.rs`
- Create: `verify_middle/src/main.rs` (minimal `fn main() {}` for now)
- Test: inline `#[cfg(test)]` in `verify_middle/src/stream.rs`

**Interfaces:**
- Consumes: nothing.
- Produces: `Stream` with `Stream::new() -> Self`, `Stream::double(&mut self)`, `Stream::to_n(&mut self, n: usize)`, `Stream::n: usize`, `Stream::digits: Vec<u8>` (least-significant-first base-3 digits of `2^n`).

- [ ] **Step 1: Write `Cargo.toml`**

```toml
[package]
name = "verify_middle"
version = "0.1.0"
edition = "2021"

[dependencies]
num-bigint = "0.4"
```

- [ ] **Step 2: Write the failing test** (`verify_middle/src/stream.rs`)

```rust
pub struct Stream {
    pub n: usize,
    pub digits: Vec<u8>,
}

impl Stream {
    pub fn new() -> Self {
        Stream { n: 0, digits: vec![1] }
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
```

- [ ] **Step 3: Run test to verify it fails**

Run: `cd verify_middle && cargo test`
Expected: FAIL — `Stream::double` does not exist.

- [ ] **Step 4: Implement `double` and `to_n`**

Add to the `impl Stream` block:

```rust
    /// Double the stored number (2^n -> 2^(n+1)) by transforming every
    /// digit with the base-3 carry: s = 2*d + c, digit = s % 3, carry = s / 3.
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

    /// Bring the stream to 2^n (n >= self.n).
    pub fn to_n(&mut self, n: usize) {
        while self.n < n {
            self.double();
        }
    }
```

- [ ] **Step 5: Run tests to verify they pass**

Run: `cd verify_middle && cargo test`
Expected: PASS (1 test).

- [ ] **Step 6: Commit**

```bash
git add verify_middle/Cargo.toml verify_middle/src/stream.rs verify_middle/src/main.rs
git commit -m "feat: carry-chain base-3 doubling Stream for 2^n"
```

---

### Task 2: `window_metrics`

**Files:**
- Create: `verify_middle/src/metrics.rs`
- Modify: `verify_middle/src/main.rs` (add `mod metrics;`)
- Test: inline `#[cfg(test)]` in `verify_middle/src/metrics.rs`

**Interfaces:**
- Consumes: nothing from Task 1 (works on any `&[u8]`).
- Produces: `WindowMetrics { freq: f64, longest_free: usize, all_free: bool, first_two: Option<usize> }` and `window_metrics(digits: &[u8], a: usize, b: usize) -> WindowMetrics`.

- [ ] **Step 1: Write the failing test** (`verify_middle/src/metrics.rs`)

```rust
pub struct WindowMetrics {
    pub freq: f64,
    pub longest_free: usize,
    pub all_free: bool,
    pub first_two: Option<usize>,
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
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cd verify_middle && cargo test`
Expected: FAIL — `window_metrics` not defined.

- [ ] **Step 3: Implement `window_metrics`**

```rust
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
```

- [ ] **Step 4: Run tests to verify they pass**

Run: `cd verify_middle && cargo test`
Expected: PASS (2 tests).

- [ ] **Step 5: Commit**

```bash
git add verify_middle/src/metrics.rs verify_middle/src/main.rs
git commit -m "feat: window digit-2 metrics (freq, longest run, all-free, first-2)"
```

---

### Task 3: Analyzer CLI writing the results CSV

**Files:**
- Modify: `verify_middle/src/main.rs` (full CLI)
- Test: run the analyzer on a small range and inspect output

**Interfaces:**
- Consumes: `Stream` (Task 1), `window_metrics` (Task 2).
- Produces: CLI `verify_middle --analyze N out.csv` writing rows `n,L,W,<t>*,<m>*,<l>* ,t0,t1,m0,m1,l0`; prints records summary to stdout.

- [ ] **Step 1: Implement the CLI** (`verify_middle/src/main.rs`)

```rust
mod metrics;
mod stream;

use metrics::{window_metrics, WindowMetrics};
use stream::Stream;
use std::env;
use std::fs::File;
use std::io::{BufWriter, Write};

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

fn main() {
    let args: Vec<String> = env::args().collect();
    match args.get(1).map(|s| s.as_str()) {
        Some("--analyze") => {
            let n: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(1_000_000);
            let out = args.get(3).cloned().unwrap_or_else(|| "results_m1.csv".to_string());
            analyze(n, &out);
        }
        _ => {
            println!("usage: verify_middle --analyze N out.csv  |  --verify NMAX");
        }
    }
}
```

- [ ] **Step 2: Build and run on a small range**

Run: `cd verify_middle && cargo build --release`
Run: `./target/release/verify_middle --analyze 20000 /tmp/middle_small.csv`
Expected: completes; `/tmp/middle_small.csv` has 19,992 rows (n=9..20000), correct header, plausible values (`t_free`,`m_free`,`l_free` mostly `false`).

- [ ] **Step 3: Spot-check correctness of the CSV** (`python3 - <<'EOF'`)

```python
import csv, math
rows = list(csv.DictReader(open('/tmp/middle_small.csv')))
for r in rows[:3] + rows[-3:]:
    n = int(r['n']); L = int(r['L'])
    assert L == math.floor(n * math.log(2) / math.log(3)) + 1, (n, L)
print("L(n) formula ok;", len(rows), "rows")
```
Expected: prints `L(n) formula ok; 19992 rows` with no assertion error.

- [ ] **Step 4: Commit**

```bash
git add verify_middle/src/main.rs
git commit -m "feat: analyzer CLI writing middle-digit metrics CSV"
```

---

### Task 4: Rust independent cross-check via `num-bigint`

**Files:**
- Modify: `verify_middle/src/main.rs` (add `--verify NMAX` mode)
- Test: run `--verify 100000`

**Interfaces:**
- Consumes: `Stream` (Task 1).
- Produces: CLI mode `--verify NMAX` that compares stream digits against `2^n` computed with `num-bigint::BigUint::pow`, panicking on mismatch.

- [ ] **Step 1: Add `--verify` mode** to `main.rs`

```rust
use num_bigint::BigUint;

fn verify(nmax: usize) {
    let two = BigUint::from(2u8);
    let three = BigUint::from(3u8);
    let mut s = Stream::new();
    for n in 0..=nmax {
        let p = two.pow(n as u32);
        let mut t = p;
        let mut digits = Vec::new();
        if t == BigUint::from(0u8) {
            digits.push(0);
        }
        while t > BigUint::from(0u8) {
            let d = (&t % &three).to_u8_digits().first().copied().unwrap_or(0);
            digits.push(d);
            t /= &three;
        }
        assert_eq!(s.digits, digits, "digit mismatch at n={n}");
        s.double();
    }
    println!("verify ok through n={nmax}");
}
```

Wire it into `main`:

```rust
        Some("--verify") => {
            let n: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100_000);
            verify(n);
        }
```

- [ ] **Step 2: Run the cross-check**

Run: `cd verify_middle && cargo run --release -- --verify 100000`
Expected: prints `verify ok through n=100000` (no panic).

- [ ] **Step 3: Commit**

```bash
git add verify_middle/src/main.rs
git commit -m "test: cross-check Stream digits against num-bigint pow"
```

---

### Task 5: Full 10⁶ run + independent Python cross-check

**Files:**
- Create: `verify_middle/crosscheck.py`
- Modify: `verify_middle/src/main.rs` (only if timing gate fails — see Step 4)

**Interfaces:**
- Consumes: the digit stream from `Stream` (validated in Task 4).
- Produces: `verify_middle/results_m1.csv`; `crosscheck.py` verifies stream digits against `pow(2,n)` in Python for n ≤ 10⁵.

- [ ] **Step 1: Write `crosscheck.py`** (independent Python verification)

```python
import sys


def stream_digits(max_n: int) -> None:
    """Independent streaming base-3 doubling (reference impl), checked vs pow."""
    digits = [1]
    for n in range(0, max_n + 1):
        # 2^n = digits (least-significant first)
        assert digits == _base3(pow(2, n)), f"mismatch at n={n}"
        c = 0
        for i in range(len(digits)):
            s = 2 * digits[i] + c
            digits[i] = s % 3
            c = s // 3
        if c:
            digits.append(c)
    print(f"python cross-check ok through n={max_n}")


def _base3(m: int) -> list:
    v = []
    while m > 0:
        v.append(m % 3)
        m //= 3
    return v


if __name__ == "__main__":
    stream_digits(int(sys.argv[1]) if len(sys.argv) > 1 else 100_000)
```

- [ ] **Step 2: Run the Python cross-check**

Run: `python3 verify_middle/crosscheck.py 100000`
Expected: prints `python cross-check ok through n=100000`.

- [ ] **Step 3: Run the full 10⁶ analysis**

Run: `cd verify_middle && ./target/release/verify_middle --analyze 1000000 ../verify_middle/results_m1.csv`
(Target path: repo-root `verify_middle/results_m1.csv`.)
Expected: finishes with a records summary; CSV has 999,992 data rows; per-step progress to stderr.

- [ ] **Step 4: Timing gate decision**

If the `--analyze 1000000` wall time is under ~15 min, keep the algorithm as-is and record the time in the commit body. If over ~15 min, add a one-line change to `Stream::double` that early-exits when the carry is 0 **only after every remaining digit is 0** — do NOT early-exit (all digits transform), so if it is slow, instead record the time and defer optimization to Phase 8. Document the measured time in `FINDINGS.md` (Task 7).

- [ ] **Step 5: Commit**

```bash
git add verify_middle/crosscheck.py verify_middle/results_m1.csv
git commit -m "data: full middle-digit run to n=10^6, cross-checked via pow"
```

---

### Task 6: M2 independence test

**Files:**
- Create: `verify_middle/independence.py`
- Test: run on a small CSV, then on the full one

**Interfaces:**
- Consumes: `verify_middle/results_m1.csv` (columns `t0,t1,m0,m1,l0`, `*_freq`).
- Produces: `verify_middle/independence_summary.md`.

- [ ] **Step 1: Write `independence.py`** (stdlib only)

```python
import csv
import math
import sys


def read_rows(path):
    with open(path) as f:
        return list(csv.DictReader(f))


def cross_tab(rows, ca, cb):
    tab = [[0] * 3 for _ in range(3)]
    for r in rows:
        tab[int(r[ca])][int(r[cb])] += 1
    return tab


def chi_square(tab):
    total = sum(map(sum, tab))
    if total == 0:
        return 0.0
    row = [sum(row) for row in tab]
    col = [sum(tab[i][j] for i in range(3)) for j in range(3)]
    stat = 0.0
    for i in range(3):
        for j in range(3):
            e = row[i] * col[j] / total
            if e > 0:
                stat += (tab[i][j] - e) ** 2 / e
    return stat  # ~0 means independent; large means dependent


def spearman(xs, ys):
    def rank(v):
        order = sorted(range(len(v)), key=lambda i: v[i])
        r = [0.0] * len(v)
        i = 0
        while i < len(v):
            j = i
            while j + 1 < len(v) and v[order[j + 1]] == v[order[i]]:
                j += 1
            avg = (i + j) / 2.0 + 1
            for k in range(i, j + 1):
                r[order[k]] = avg
            i = j + 1
        return r

    rx, ry = rank(xs), rank(ys)
    n = len(xs)
    mx = sum(rx) / n
    my = sum(ry) / n
    cov = sum((rx[i] - mx) * (ry[i] - my) for i in range(n))
    vx = math.sqrt(sum((rx[i] - mx) ** 2 for i in range(n)))
    vy = math.sqrt(sum((ry[i] - my) ** 2 for i in range(n)))
    return cov / (vx * vy) if vx * vy > 0 else 0.0


def main(path):
    rows = read_rows(path)
    pairs = [("t0", "m0"), ("t1", "m0"), ("m0", "l0")]
    out = []
    out.append("# M2 Independence Test\n")
    out.append(f"Rows analyzed: {len(rows)}\n")
    for ca, cb in pairs:
        tab = cross_tab(rows, ca, cb)
        out.append(f"## cross-tab {ca} x {cb}\n")
        out.append("| |0|1|2|\n|---|---|---|---|\n")
        for i in range(3):
            out.append(f"|{i}|{tab[i][0]}|{tab[i][1]}|{tab[i][2]}|\n")
        out.append(f"chi-square = {chi_square(tab):.1f} (independent ~ 0)\n")
    fr = [("t_freq", "m_freq"), ("l_freq", "m_freq"), ("l_freq", "t_freq")]
    for ca, cb in fr:
        xs = [float(r[ca]) for r in rows]
        ys = [float(r[cb]) for r in rows]
        out.append(f"Spearman({ca}, {cb}) = {spearman(xs, ys):.4f}\n")
    with open(path.rsplit("/", 1)[0] + "/independence_summary.md", "w") as f:
        f.writelines(out)
    print("independence summary written")


if __name__ == "__main__":
    main(sys.argv[1])
```

- [ ] **Step 2: Test on a small CSV**

Run: `python3 verify_middle/independence.py /tmp/middle_small.csv`
Expected: prints `independence summary written`; `/tmp/independence_summary.md` contains the tables. Sanity: `Spearman(t_freq, m_freq)` is finite and in `[-1, 1]`.

- [ ] **Step 3: Run on the full CSV**

Run: `python3 verify_middle/independence.py verify_middle/results_m1.csv`
Expected: `verify_middle/independence_summary.md` produced from 999,992 rows.

- [ ] **Step 4: Commit**

```bash
git add verify_middle/independence.py verify_middle/independence_summary.md
git commit -m "data: M2 independence test (cross-tabs, chi-square, Spearman)"
```

---

### Task 7: `FINDINGS.md` (M4 initial findings + new conjecture)

**Files:**
- Create: `verify_middle/FINDINGS.md`

**Interfaces:**
- Consumes: `results_m1.csv` records, `independence_summary.md`.

- [ ] **Step 1: Write `FINDINGS.md`** with real numbers from the run

Include (fill in from the actual run output — do NOT invent):
- records table: per window (trailing/middle/leading): min frequency + its n, max 2-free run + its n, count of all-2-free windows;
- the three-window frequency comparison (which window is most 2-poor);
- the independence-test headline numbers (Spearman values; chi-square of the `t0 x m0` cross-tab);
- the L(n) formula check result and the measured wall time of the 10⁶ run;
- **one new conjecture** derived from the data (e.g. a conjectured growth rate for the record max-2-free-run in the middle window, or a lower bound on middle-window frequency).

- [ ] **Step 2: Commit**

```bash
git add verify_middle/FINDINGS.md
git commit -m "docs: Phase 7 M1 findings and new conjecture"
```

---

## Out of Scope (later plans)

- **M3 (Lean formalization of the base-3 doubling transducer)** — a separate plan; will target `ErdosTernary/ErdosTernary/MiddleDigits.lean` after this data plan lands.
- **Phase 8** (`f(n)` first-occurrence statistics) and **Phase 9** (two-sided search) — per ROADMAP.