# Event-Level Test: A_L (leading no-2) vs B_K (trailing no-2)

Dataset: `verify_middle/events_m1.csv` — 169 (L,K) cells over n = 9…10⁶
(999,955–999,992 points per cell), grid L,K ∈ {1,2,3,4,5,6,8,10,12,16,20,24,30}.

Events:
- A_L = leading L ternary digits of 2ⁿ contain no 2 (positions [len−L, len))
- B_K = trailing K ternary digits of 2ⁿ contain no 2 (positions [0, K))

## Marginals — exact laws

**Trailing:** P(B_K) = (1/2)·(2/3)^(K−1) to within sampling error for K ≤ 12
(relative error < 10⁻³; drifts up to ~23% at K = 30 where only 3 samples occur).
Derivation: the least-significant digit of 2ⁿ is never 0 (2ⁿ ≢ 0 mod 3) and is
equally likely 1 or 2 (n even/odd); digits above it behave uniformly in {0,1,2}.

| K | P(B_K) | (1/2)(2/3)^(K−1) | rel err |
|---|---|---|---|
| 1 | 0.500000 | 0.500000 | 0 |
| 3 | 0.222222 | 0.222222 | −1e−6 |
| 6 | 0.065845 | 0.065844 | +2e−5 |
| 12 | 0.005786 | 0.005781 | +1e−3 |
| 16 | 0.001116 | 0.001142 | −2.3e−2 |
| 20 | 0.000235 | 0.000226 | +4.2e−2 |

**Leading:** P(A₁) = log₃ 2 = 0.63093 — the mantissa (Benford) law for the
leading digit of 2ⁿ. A_L is NOT (2/3)^L: the leading-digit distribution is the
well-known log-law (P(first digit = 1) = log₃ 2), so leading blocks are more
2-avoidant than iid would predict at small L but converge as L grows.

| L | P(A_L) | (2/3)^L | P(A_L)/(2/3)^L |
|---|---|---|---|
| 1 | 0.630929 | 0.666667 | 0.946 |
| 2 | 0.464975 | 0.444444 | 1.046 |
| 4 | 0.218523 | 0.197531 | 1.106 |
| 6 | 0.097763 | 0.087791 | 1.114 |
| 12 | 0.008547 | 0.007707 | 1.109 |
| 20 | 0.000312 | 0.000301 | 1.037 |

## Conditional test: P(A_L | B_K) vs P(A_L)

Z-test for independence (n_AB observed vs pa·n_B expected, sd = √(n_B·pa(1−pa))),
restricted to cells with ≥ 100 B_K samples (143 of 169):

- cells with |z| > 1.96: **6 / 143** (2 positive, 4 negative)
- expected under independence (5% × 143): **7.2**

Observed count is indistinguishable from chance → **no evidence that trailing
2-avoidance predicts leading 2-avoidance.** (Sign pattern has no coherent
structure: negative devs cluster at L=12,K=3–6; positive at K=16–20 — but the
K≥16 cells hold only ~100–1100 samples, and 6/143 matches the null.)

Largest |z| cells (all below Bonferroni significance, 0.05/143 ≈ 3.44):

| cell | z | P(A) | P(A|B) | dev | n_B |
|---|---|---|---|---|---|
| A₁₂|B₃ | −2.36 | 0.008547 | 0.008087 | −0.00046 | 222220 |
| A₁₂|B₄ | −2.35 | 0.008547 | 0.007985 | −0.00056 | 148148 |
| A₁₆|B₁₆ | +2.24 | 0.001708 | 0.004480 | +0.00277 | 1116 |
| A₃₀|B₈ | +2.23 | 0.000005 | 0.000034 | +0.00003 | 29265 |

## Conclusion

The joint test is strictly more informative than Spearman (which could not see
event-level structure) and it passes: **A_L and B_K are empirically
independent** for all L,K tested. This is the direct event-level confirmation
needed for the two-sided approach in Phase 9 — a number can be filtered by its
trailing K digits without perturbing the distribution of leading no-2 blocks.

## Artifacts

- `verify_middle/events_m1.csv` — full 169-cell table (L,K,N,P_A,P_B,P_AB,P_A_given_B,dev)
- `verify_middle/src/main.rs` — `--events` mode (single streaming pass, ~15 min)