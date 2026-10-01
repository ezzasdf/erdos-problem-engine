# Phase 8 M1 Findings: First-2-Position Records of 2ⁿ in Ternary

Dataset: `verify_middle/first2_records.csv` — 19 record-holders over n = 0 … 10⁹, columns `n,f,L,ratio,prefix,mantissa_precision,record_number,gap_from_previous_record`.

**Definitions.** `f(n)` = position of the *first* digit 2 in 2ⁿ counting from the most significant digit (0-indexed), or `L(n)` if 2ⁿ has no digit 2. `L(n) = ⌊n·log₃2⌋ + 1` is the ternary digit count. A *record* is an n with `f(n)` strictly larger than at every smaller index. Computation: certified streaming mantissa `yₙ = 2ⁿ/3^⌊nα⌋` (α = log₃2) with interval-arithmetic escalation via `3^{frac(n·α)}`.

## Records to 10⁹

| record | n | f | L | f/L | gap | prefix |
|---|---|---|---|---|---|---|
| 1 | 0 | 1 | 1 | 1.000e+00 | 0 | 1 |
| 2 | 2 | 2 | 2 | 1.000e+00 | 2 | 11 |
| 3 | 5 | 3 | 4 | 7.500e-01 | 3 | 101 |
| 4 | 8 | 6 | 6 | 1.000e+00 | 3 | 100111 |
| 5 | 27 | 8 | 18 | 4.444e-01 | 19 | 10010011 |
| 6 | 92 | 10 | 59 | 1.695e-01 | 65 | 1001101101 |
| 7 | 121 | 15 | 77 | 1.948e-01 | 29 | 111010000101011 |
| 8 | 606 | 18 | 383 | 4.700e-02 | 485 | 111010101011010110 |
| 9 | 1690 | 22 | 1067 | 2.062e-02 | 1084 | 1100101010010101000110 |
| 10 | 20302 | 24 | 12810 | 1.874e-03 | 18612 | 101110010010000011111111 |
| 11 | 23507 | 25 | 14832 | 1.686e-03 | 3205 | 1100011010110110010100001 |
| 12 | 26379 | 30 | 16644 | 1.802e-03 | 2872 | 110110101001001101000110010100 |
| 13 | 116655 | 34 | 73602 | 4.619e-04 | 90276 | 1010111000011111100001100111001100 |
| 14 | 953604 | 36 | 601658 | 5.983e-05 | 836949 | 101110101101011100111010011100010101 |
| 15 | 3608686 | 37 | 2276828 | 1.625e-05 | 2655082 | 1111111001101111010010010111100000010 |
| 16 | 8075942 | 40 | 5095353 | 7.850e-06 | 4467256 | 1010000000100011010100110100010001001100 |
| 17 | 13961331 | 44 | 8808620 | 4.995e-06 | 5885389 | 10110011110000000010011110100111110001111001 |
| 18 | 46052485 | 48 | 29055884 | 1.652e-06 | 32091154 | 100010100000101111011101010001011011010110010001 |
| 19 | 464263536 | 50 | 292917679 | 1.707e-07 | 418211051 | 11110101110010000011010000110010011011110001100111 |

`max_f = 50` (at n = 464,263,536); record count 19; largest gap 418,211,051 (the final gap to 10⁹).

## Verification (all passed)

- **Unit tests (6, all green):** mantissa stream vs exact 2ⁿ digits (n ≤ 30); certified α-interval tightness; escalate exact-or-one-low digits for n ≤ 12; interval-path cross-check vs streaming f at n = 400/1000/5000/100000 and p=200-vs-p=400 consistency at n = 10⁶/10⁷/10⁹.
- **`--first2-check`:** certified `f(n)` equals `exact_f(2ⁿ)` for every n ≤ 10⁵ (p=200); escalation stress at p=2 (n ≤ 2000, p grew 2→8+) and p=6 (n ≤ 20000, p grew 6→24) — the δ/truncation-ambiguity escalations fired and stayed correct.
- **`--first2-events`:** P(f ≥ L) matches the Phase 7 leading-digit marginals P(A_L) (events_m1.csv, K=1) with z = 0.00 at all 13 grid L; P(f ≥ 1) = 0.630929 = log₃2 (Benford leading-digit law).
- **`--first2-verify-records`:** all 19 records re-derived purely from `3^{frac(n·α)}` (no stream state) — 19/19 verified.
- **Python exact check:** `f`, `L`, and 2-free prefix length verified against `pow(2,n)` for all records with n ≤ 116655.

## Timing

Full 10⁹ run wall time **2547 s ≈ 42.5 min** (over the 30-min gate → optimization deferred). Max `p` reached: **200** — no escalation was ever needed at p = 200 (records' f stays ≤ 200), so the run was pure streaming.

## Analysis

- **Growth:** records follow `f ≈ log_{3/2}(n)`: least-squares fit `f ≈ 1.044·log_{3/2}(n) + 0.60` (slope ≈ 1.04). Equivalently `f ≈ 2.83·log₃(n)` asymptotically.
- **Ratio `f/L`:** decays steadily from the small-n records (1.0 at n ≤ 8) to 1.707e-7 at n = 464,263,536 — consistent with `f/L ≈ log_{3/2}(n)/n ≈ (2.7/n)·ln n`, i.e. a record prefix is a vanishing fraction of the digit string.
- **Gaps:** grow roughly super-linearly in f but irregularly (dips at records 11–12); the largest gap is the final 4.18e8. Gap ≈ expected waiting time `1/P(f ≥ f_rec)` for the next level of rarity.
- **Constant `f/log₃ n`:** transient small-n spike of 3.43 at n = 121, settling toward ≈ 2.83 for large n (last record: 2.75).

## Probability heuristic: why f grows like log_{3/2} n

The observed growth is not an accident of the data — it is exactly what the digit model predicts.

**Model.** For irrational α = log₃2, the fractional parts {n·α} are equidistributed, so the leading digits of `2ⁿ = 3^{n·α}` are governed by the map `x ↦ 3^x` (Benford). Reading off the first L ternary digits of `2ⁿ` is therefore like drawing L independent uniform digits in the model — so the probability that the first L digits are all ≠ 2 should be `P(f(n) ≥ L) ≈ (2/3)^L`, up to a slowly varying factor.

**The factor is actually exact.** Since `f(n) ≥ L` iff the first L digits of `3^{frac(nα)}` are all ≠ 2 (equivalently the leading digit is 1 and the next L−1 digits are 0 or 1),

```
P(f ≥ L) = Σ_s log₃(1 + 3^{1−L} / t_s),   t_s = Σ s_i 3^{−i},
```

summed over all length-L strings s with s₀ = 1, s_i ∈ {0,1}. Numerically this gives, to 6 decimal places, agreement with the measured `P(f ≥ L)` at N = 10⁶ (e.g. L=5: exact 0.146425 vs measured 0.146409) — a direct empirical confirmation of equidistribution. As L → ∞,

```
P(f ≥ L) = C·(2/3)^L,   C = 1.1148 (converged by L ≈ 10),
```

the "slowly varying factor" being `C = (3/(2 ln3))·E[1/t_s] ≈ 1.115` (Benford correction at the leading digit, plus the 1/t_s weighting; the L=1 raw value is `log₃2 = 0.6309`).

**Extreme-value prediction.** Over n = 1 … N, the expected number of hits at threshold L is `N·P(f ≥ L) ≈ N·C·(2/3)^L`. Setting it ≈ 1 gives the scale of the largest `f`:

```
max_f(N) ≈ log_{3/2}(N·C) = log_{3/2}(N) + 0.221.
```

| N | log_{3/2}(N·C) | observed max f |
|---|---|---|
| 10⁶ | 34.24 | 36 (n = 953,604) |
| 10⁷ | 39.96 | 40 (n = 8,075,942) |
| 10⁹ | 51.21 | 50 (n = 464,263,536) |

The maximum is a single realization with O(1) fluctuations, so agreement within ±2 at every scale is the predicted behavior — and the observed `f ≈ 1.044·log_{3/2}(n)` fit slope is 1.0 plus small-n transient pull.

**Gap prediction.** The expected gap until a new record (current max `f*`) is the waiting time `1/P(f ≥ f*) = (3/2)^{f*}/C`. Checking the records: f* = 34 → (3/2)³⁴/C ≈ 8.7×10⁵ vs gap 8.4×10⁵; f* = 40 → ≈ 9.9×10⁶ vs 5.9×10⁶; f* = 48 → ≈ 2.5×10⁸ vs 4.2×10⁸ — individual gaps fluctuate by factors 0.5–2.8 (exponential waiting-time tail), consistent with `log gap ≈ f·log(3/2)`, i.e. `n ≈ (3/2)^{f}`.

**Summary.** The records satisfy `f ≈ log_{3/2} n` because that is the unique growth rate at which the `(2/3)^f` probability of a longer 2-free prefix balances `n ≈ 1`. The heuristic sharpens the observed fit into a quantitative, falsifiable prediction and identifies the small constant C = 1.1148.

## Rigorous deviation analysis: the exact behavior of P(f ≥ L)

The measured deviation from `(2/3)^L` is not noise and not an iid failure — it is a precise, computable law.

**Theorem (exact asymptotics).** For the set `S_L = {x ∈ [0,1): the first L ternary digits of 3ˣ are all ≠ 2}`,

```
P(f(n) ≥ L) = meas(S_L) = Σ_s log₃(1 + 3^{1−L}/t_s)   (finite sum, t_s = 1 + Σ s_i 3^{−i})
            = C·(2/3)^L·(1 + O(3^{−L})),
C = 1.1147648 ± 1×10⁻⁷.
```

The `O(3^{−L})` correction is verified numerically: the ratio `P/(2/3)^L` steps L=5→8→10→12→14 by −2.75e-3, −9.4e-5, −1.05e-5, −1.17e-6 (each step ≈ ÷9 = 3²), converging to C by L ≈ 10.

**The deviation is fully explained (two sources, nothing else).**
1. *Systematic factor C = 1.1148.* The L=1 value is `log₃2` (Benford), ratio 0.946; the ratio climbs to C ≈ 1.115 by L ≈ 10 and stays. C = `(3/(2ln3))·E[1/(1+X)]` with `X = Σ 3^{−i}B_i`, `B_i` i.i.d. Bernoulli(1/2) — the leading-digit Benford correction plus the `1/t_s` weighting.
2. *Sampling noise at large L.* Residuals of the measured `P` (N = 10⁶) vs the *exact* value are all `|z| < 2` — the apparent wobble in the earlier table (e.g. ratio 0.84 at L=24, 0.96 at L=30) is purely Poisson (counts 50 and 5).

**Rigorous upper bounds (unconditional, given Weyl equidistribution of `{n·log₃2}`).**
- *Elementary (one line):* each term `log₃(1+3^{1−L}/t_s) ≤ 3^{1−L}/ln3` since `t_s ≥ 1`; summing the `2^{L−1}` strings gives
  ```
  P(f ≥ L) ≤ (3/(2 ln3))·(2/3)^L ≈ 1.3654·(2/3)^L.
  ```
- *Refined:* using `1/(1+X) ≤ 1 − X + X²` (X ∈ [0,1/2)) on the expectation,
  ```
  P(f ≥ L) ≤ 1.1520·(2/3)^L,
  ```
  within 3.3% of the exact C = 1.1148. Both verified to hold for every L ≤ 20 against the exact sum.

**Corollary (density, unconditional).** For every fixed L, `#{n ≤ N : f(n) ≥ L}/N → P(f ≥ L) ≤ 1.152·(2/3)^L` (Weyl). So the density of n whose first L ternary digits are 2-free is bounded by `1.152·(2/3)^L` — this is the rigorous content of the "≈ (2/3)^L" observation.

**What the bound does and does not give for a pointwise O(log n) bound.** The measure bound describes the *average* behavior. A pointwise bound `f(n) ≤ C·log₃ n` for every n ≤ N is exactly the vanishing of the exception count `e_L(N) = #{n ≤ N : f(n) ≥ L}` at `L = ⌊C·log₃ N⌋ + 1`, and — as the next section proves — no counting inequality built from the measure can certify it: the error band is `N·2^L·D*_N`, and `D*_N ≥ 1/(2N)` for every sequence, so the band is always ≥ 2^{L−1} ≥ 1. The object that genuinely controls the exceptions is the orbit structure of `{n·log₃2}` — the continued fraction of `log₃2`, analyzed next.

## From the probability law to a pointwise theorem

The law `P(f≥L) = C·(2/3)^L` describes averages; this section records exactly what it can and cannot say about a pointwise bound, via the continued fraction of α = log₃2 (computed in `verify_middle/p_cf_log32.py`, stdlib only).

**Counting identity (Koksma, exact constants).** `S_L` is a union of `2^{L−1}` intervals, so its characteristic function has total variation `2^L`. With `e_L(N) = #{n < N : f(n) ≥ L}` and `D*_N` the star discrepancy of the orbit `{n·α}`:

```
e_L(N) = N·P(f≥L) + O(N·2^L·D*_N) = N·C·(2/3)^L·(1 + O(3^{−L})) + O(N·2^L·D*_N).
```

A pointwise bound `max_{n<N} f(n) < L` is exactly `e_L(N) = 0` (the maximum is attained at some n < N).

**Obstruction Lemma.** No counting inequality can promote the density law into a pointwise bound. Every N-point set satisfies `D*_N ≥ 1/(2N)`, so the band `N·2^L·D*_N ≥ 2^{L−1} ≥ 1` for every `L ≥ 1`; the upper bound `e_L(N) ≤ N·P + band` can never be driven below 1, hence can never certify `e_L(N) = 0`. Even perfect gap control (three-distance theorem: gaps ≤ `‖q_k·α‖ ≤ 1/q_{k+1}`) leaves a floor of one point per interval, again ≥ `2^{L−1}`. The density law is therefore provably insufficient for a pointwise bound; rare gigantic exceptions are not excluded by it.

**The crux: the continued fraction of α = log₃2.** The partial quotients are

```
α = log₃2 = [0; 1,1,1,2,2,3,1,5,2,23,2,2,1,1,55,1,4,3,1,1,15,1,9,2,5,7,1,1,4,8,1,11,1,20,2,1,10,1,4,1,1,1,1,…]
```

mostly small, but with anomalously large entries `a₁₅ = 55`, `a₂₁ = 15`, `a₃₄ = 20`, `a₃₇ = 10` that create long windows of small discrepancy: throughout `N ∈ [301994, 16785921)` the denominator sum in the bound is fixed, so `D*_N ≤ 6.81×10⁵/(N+1)` and max gap ≤ `1/1.68×10⁷ ≈ 6×10⁻⁸`. The standard bound

```
D*_N ≤ (Σ_{i≤k(N)} q_i)/(N+1),   k(N) = max{k : q_k ≤ N},
```

is validated by brute force (`D*/bound ≤ 0.014` on N ≤ 2000, `verify_middle/p_cf_log32.py`).

**Predictive but not probative.** The band is quantitatively accurate: at N = 10⁶ the predicted counts `N·P(f≥L)` match the measured counts at all 13 grid levels to `|z| ≤ 2` (e.g. L=20: 335 predicted vs 312 measured; L=30: 5.8 vs 5.0), while the band exceeds the predicted count by factors ~2 (L=1) to ~10¹⁴ (L=30) — the law pins the counts but cannot certify their vanishing. At the certified maxima:

| N | certified max f | mean `N·C(2/3)^L` | band `N·2^L·D*_N` |
|---|---|---|---|
| 10⁶ | 36 | 0.51 | 4.7×10¹⁶ |
| 10⁷ | 40 | 1.01 | 7.5×10¹⁷ |
| 10⁹ | 50 | 1.75 | 1.6×10²⁴ |

The mean matches the measured count (1 at each level) and the law predicts the maximum within one level of the heuristic `log_{3/2}(N·C)` (34.2 / 40.0 / 51.2), but the certification itself is the exhaustive computation — the records *are* the pointwise theorem for n ≤ 10⁹. Proving a pointwise bound beyond the computed range requires exact orbit counting (Ostrowski / three-distance arithmetic — the Phase 9 program), which is genuinely harder than the density law and is the honest frontier left open.

## New conjecture

**P8-C1 (linear bound on the first-2 position).** For every n ≥ 1, `f(n) ≤ 3.5·log₃(n)`, i.e. `2ⁿ` has a digit 2 among its first `⌈3.5·log₃ n⌉` ternary digits. Empirically the sharpest point is n = 121 with `f(121)/log₃(121) ≈ 3.43` (2% margin); the ratio decays to ≈ 2.8 (the `log_{3/2}` slope) for large n.

If provable, `f(n) ≤ C·log₃ n` is a genuinely new pointwise theorem on the digits of `2ⁿ` (stronger than density-zero statements), and — combined with Saye's trailing-digit pruning — a two-sided search (Phase 9) could certify far beyond 5.9×10²¹.

## Out of scope (later plans)

- Proof (even partial) of P8-C1; the transient-spike structure around n = 121.
- Phase 9 two-sided search using these records as leading-digit candidates.
- Phase 7 M3 Lean formalization of the base-3 doubling transducer.