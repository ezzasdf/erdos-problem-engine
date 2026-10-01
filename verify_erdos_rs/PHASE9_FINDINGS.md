# Phase 9 Findings — Two-Sided Search (Saye + leading-digit check)

Date: 2026-08-17
Spec: `docs/superpowers/specs/2026-08-17-two-sided-search-design.md`
Plan: `docs/superpowers/plans/2026-08-17-phase9-two-sided-search.md`

## Completeness argument

For any `n ≤ B = 2·3^{K−1}`:

1. If `2ⁿ` has a 2 among its **trailing 54** ternary digits → verified (Saye's tree prunes these; only the 2-free-trailing candidates survive).
2. Otherwise `n` is a Saye candidate. The **first K′ = 70 leading digits** of `2ⁿ = 3^{frac(n·log₃2)}` are computed by certified interval arithmetic (`leading_digits_have_two`, BigInt, `k_prime` start precision `k_prime+4`, prefix-span test over `digits(ylo_p)..digits(yhi_p)`). A certified 2 there → verified (`eliminated`).
3. Candidates 2-free in **both** blocks are `deep`. `deep == {0,2,8}` plus brute-force `n ≤ 10⁶` closes the small-n block-overlap gap (n ≲ (K′+54)/log₃2 ≈ 197): every `n ≤ B` is then verified.

The leading check is certified: `Some(true)` only when a 2 is rigorously present in the first `k_prime` digits (the whole interval span shares a prefix containing a 2); `Some(false)` only when all first `k_prime` digits are rigorously ≠ 2; `None` only on unresolved ambiguity (treated as deep, counted separately). Escalation doubles precision to p ≤ 512.

## Validation ladder

Engine: `--two-sided K 70`, chi = 2, auto parallel depth. 4-core machine (load-contended).

| K | coverage n ≤ 2·3^{K−1} | candidates | eliminated | deep | ambiguous | elapsed |
|---|------------------------|-----------:|-----------:|:-----|:----------|--------|
| 10 | 39,366 | 3 | 0 | {0,2,8} | 0 | 0.82 ms |
| 15 | 9,565,938 | 3 | 0 | {0,2,8} | 0 | 14.9 ms |
| 20 | 2,324,522,934 | 4 | 1 | {0,2,8} | 0 | 204 ms |
| 25 | 564,859,072,962 | 130 | 127 | {0,2,8} | 0 | 4.68 s |
| 30 | 137,260,754,729,766 | 31,894 | 31,891 | {0,2,8} | 0 | 186 s |
| 35 | 33,354,363,399,333,138 | 7,747,002 | 7,746,999 | {0,2,8} | 0 | 6167 s |
| 38 | 9.0×10¹⁷ | 209,257,404 | 209,257,401 | {0,2,8} | 0 | 52,568 s |

Expected candidate counts (Phase 1 parity): K=25 → 130 (exact ✓), K=30 → 31,894 (exact ✓), K=35 → ≈7.75M (ours 7,747,002; ROADMAP rounds to 7.75M, plan's "7,749,016" is an approx label), K=38 → ≈209.3M (ours 209,257,404; ROADMAP rounds to 209.3M).

## Brute-force small-n note

`verify_erdos 1000000` (2026-08-17): **0 counterexamples** for n = 9..10⁶, 2336.6 s. Combined with the three deep solutions n < 9 (2⁰=1, 2²=4, 2⁸=256), every n ≤ 10⁶ has a 2 in its ternary expansion — closes the small-n block-overlap gap (n ≲ (K′+54)/log₃2 ≈ 197).

## Timing reality (amended gates)

4 cores, load-contended (~2 cores effective). Saye traversal dominates: ≈2^K nodes × ~100–130 ms/branch at parallel depth (K=25 4.8 s, K=30 186 s, K=35 6167 s, K=38 52,568 s). Leading check ≈0.4 ms/candidate (~6–12 h at K=38's 209.3M). Plan gates amended (see plan Amendment section); K=42+ deferred unless a faster machine or fixed-point rewrite is available.

## K=38 cross-check result (validated)

`--two-sided 38 70` (2026-08-17 → 2026-08-18): candidates 209,257,404, eliminated 209,257,401, deep = {0, 2, 8}, ambiguous 0, elapsed 52,568 s (14.6 h, background run).

Completeness: every candidate n ≤ 2·3^37 = 9.0×10¹⁷ with 2-free trailing 54 digits provably has a 2 in its first 70 leading digits (certified interval arithmetic, prefix-span test), except the three solutions {0,2,8}; together with brute-force n ≤ 10⁶ (0 counterexamples) and the deep-set check, **every n ≤ 9.0×10¹⁷ is verified** — an independent re-derivation of Saye's 5.9×10²¹ verification restricted to this range, without relying on Saye's code or results.