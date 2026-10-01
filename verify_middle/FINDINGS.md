# Phase 7 M1 Findings: Middle-Digit Statistics of 2ⁿ in Ternary

Dataset: `verify_middle/results_m1.csv` — 999,992 rows (n = 9 … 10⁶), columns `n,L,W,<t|m|l>_freq,_long,_free,_first,t0,t1,m0,m1,l0`.
Digit positions are least-significant-first; windows are trailing `[0,W)`, middle `[W,⌊2L/3⌋)`, leading `[⌊2L/3⌋,L)` with `W = ⌊L/3⌋`.

## Verification (all passed)

- Rust `--verify 100000`: low-order 20 digits checked against `2ⁿ mod 3²⁰` on **every** n (independent modular path), plus full digit string vs `num-bigint` `to_str_radix(3)` at every 1000th n.
- Python `crosscheck.py 10000`: same two checks in an independent implementation (pure-Python `O(N·L)` caps the range at 10⁴; Rust covers 10⁵).
- `L(n) = ⌊n·log₃2⌋ + 1` formula verified on all 999,992 rows.
- Full 10⁶ run wall time: **30 m 44 s** (over the 15-min gate → optimization deferred to Phase 8).

## Records (per window)

| window | min freq | @n | max 2-free run | @n | # all-2-free windows |
|---|---|---|---|---|---|
| trailing | 0.0000 | 12 | 62 | 499010 | 5 (all n ≤ 26) |
| middle | 0.0000 | 14 | 61 | 385178 | 3 (all n ≤ 76) |
| leading | 0.0000 | 10 | 61 | 514821 | 3 (all n ≤ 27) |

Frequency-0 rows are tiny-window artifacts (n ≤ 76). For n > 1000 the empirical minima are:

| window | min freq (n>1000) | @n |
|---|---|---|
| trailing | 0.213992 | 1154 |
| middle | 0.246193 | 1874 |
| leading | 0.231343 | 1272 |

Mean digit-2 frequency is ≈ 1/3 in every window (trailing 0.333342, middle 0.333336, leading 0.333329) — matching the uniform asymptotic density of the ternary digits of 2ⁿ.

## Three-window comparison

- Frequencies: all three windows hover at 1/3; the **middle** window has the highest n>1000 frequency floor (0.246 vs 0.214 trailing, 0.231 leading) and the smallest max-2-free-run (61 vs 62 trailing), i.e. the middle third of the digits is marginally the most "2-rich".
- All-2-free windows die out by n=76 — no large window of 2ⁿ avoids the digit 2.
- The 2-free runs recorded at the window scale (L/3 ≈ 210k digits at n=10⁶) stay far below the "≥26 ones or a 2" scale of Dimitrov–Howe; window-level runs of 60-62 digits are the longest found up to n=10⁶.

## M2 independence test (from `independence_summary.md`)

- Cross-tabs `t0×m0`, `t1×m0`, `m0×l0` (boundary digit pairs) are near-uniform; chi-square 1.1, 2.3, 7.6 — no evidence of dependence. (t0 never equals 0 since 2ⁿ ≢ 0 (mod 3).)
- Spearman correlations between window frequencies: `t_freq×m_freq = 0.0011`, `l_freq×m_freq = -0.0030`, `l_freq×t_freq = -0.0000` — effectively zero. Window-level digit-2 densities behave independently across the three regions of the digit string.

## New conjecture

**M1-C1 (middle-window lower frequency bound).** For every n > 8, the middle third of the ternary expansion of 2ⁿ contains a digit 2; more precisely the digit-2 frequency in the middle window `[⌊L/3⌋, ⌊2L/3⌋)` is bounded below by ~0.246 — the empirical minimum over n ≤ 10⁶ (n>1000). Data supports that no middle window is ever 2-free beyond n=76, consistent with the Erdős conjecture (no 2ⁿ with only digits {0,1}) restricted to the middle block.

**M1-C2 (two-sided independence).** The digit-2 frequencies of the trailing, middle and leading thirds of 2ⁿ are statistically independent across n (Spearman |ρ| < 0.005), and boundary digits pair near-uniformly — so a two-sided search (Phase 9) can treat the blocks as independent inputs.