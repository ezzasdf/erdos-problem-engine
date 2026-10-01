# Spec: Phase 9 — β < log₃2 Heuristic + Rigor Analysis

Date: 2026-08-20
Status: Approved (design) — pending implementation plan
Part of: ROADMAP Phase 9 line: "Best-effort β < log₃2 bound heuristic / partial proof, feeding NarkiewiczBound"

## Objective

Produce a best-effort heuristic demonstrating that the Narkiewicz counting bound
`N(x) ≤ 4·x^α` (α = log₃2 ≈ 0.6309) can be improved to an effective exponent
`β_eff < α`, by combining the trailing-digit fiber partition (Narkiewicz machinery,
already formalized in Lean) with the leading-digit 2-free law (Phase 8). The
result is **heuristic + rigor analysis**: it establishes the inequality on the
tested grid under the stated Weyl/equidistribution bound, and it explicitly does
**not** claim a global pointwise β < α theorem.

## Background

- `N(x) = #{n ≤ x : memCantorNat (2^n)}`; proven bound `N(x) ≤ 4·x^α`,
  α = log₃2 ≈ 0.6309 (`NarkiewiczBound.lean`, `narkiewicz_real_bound`).
- Fiber partition (Task 2c.3): `N(x) ≤ 2^k·(x/u_k + 1)` with `u_k = 2·3^(k-1)`
  the order of 2 mod 3^k (proven in `Narkiewicz.lean`).
- Phase 8 leading-digit law: `P(f ≥ L) = C·(2/3)^L` with exact finite sum
  `P(f ≥ L) = Σ_s log₃(1 + 3^{1-L}/t_s)` (s runs over length-L strings with
  s₀ = 1, s_i ∈ {0,1}), and a rigorous upper bound `P(f ≥ L) ≤ 1.152·(2/3)^L`
  (given Weyl equidistribution of `{n·log₃2}`; unconditional corollary of Phase 8,
  `PHASE8_FINDINGS.md` line 108/119).
- Independence of trailing/middle/leading digit blocks is empirically supported
  (M1-C2, Spearman |ρ| < 0.005) but is NOT used as a rigorous factor in this
  deliverable; only the trailing-fiber × leading-digit combination is used.

## Core computation

For each (x, k, K) on a grid:

```
B(x, k, K) = 2^k · (x/u_k + 1) · P_rig(K)     with  u_k = 2·3^(k-1)
```

The `+1` is retained exactly — no asymptotic simplification of `x/u_k + 1`.

`P_rig(K)` is computed in **two variants**:
- **exact**: the finite sum `Σ_s log₃(1 + 3^{1-K}/t_s)` over all `2^(K-1)`
  strings s with s₀ = 1, s_i ∈ {0,1}. Computed exactly for **K ≤ 20**
  (max 2^19 = 524,288 terms per K — tractable). For **K > 20** the exact sum is
  replaced by the convergent `C·(2/3)^K` with C = 1.1147647951 (converged by
  L ≈ 10 per Phase 8); this policy is documented in the findings doc and is
  auditable in the script.
- **rigorous**: `1.152·(2/3)^K` (the unconditional Phase 8 upper bound) for all K.

`β_eff(x) = ln(min_{k,K} B(x,k,K)) / ln(x)` for each x on a geometric grid
(up to ~10¹⁸). `k` ranges over the integer window
`k ∈ [max(1, ⌊log₃ x⌋ − 8), ⌊log₃ x⌋ + 8]` (both sides of the fiber balance point
`x/u_k ≈ 1`, honoring integer constraints); `K = 1..30`. The window is fixed and
documented so the optimizer cannot silently miss the optimum.

## Outputs

1. **Console** (carefully qualified, no overclaim):

   ```
   RIGOROUS-BOUND CHECK:
   β_eff < α on tested grid: PASS

   STATUS:
   This establishes the inequality for the evaluated grid under
   the stated Weyl/equidistribution bound.
   It does NOT establish a global pointwise β < α theorem.
   ```

   (The check asserts `β_eff_rigorous < α` for every x on the grid; if it fails,
   prints FAIL with the failing x values.)

2. **CSV** — one row per x, audit columns (so the optimizer is inspectable):

   ```
   x, beta_eff_exact, beta_eff_rigorous, alpha, alpha_minus_beta_exact,
   alpha_minus_beta_rigorous, k_opt_exact, K_opt_exact, k_opt_rigorous,
   K_opt_rigorous, B_exact, B_rigorous
   ```

3. **Findings doc** `verify_middle/PHASE9_BETA_FINDINGS.md`:
   - Framing (exact wording): *"Heuristic scaling: each additional certified
     leading digit contributes approximately a factor 2/3, suggesting an exponent
     reduction of roughly (1−α) per leading digit under the chosen scaling — the
     actual β_eff is computed by `beta_bound.py` from the complete expression
     (including the +1, integer constraints, and the allowed k,K,x relationship)."*
   - Exact vs rigorous `P(f≥K)` table.
   - Computed `β_eff(x)` table (the empirical result, not a closed-form claim).
   - Obstruction Lemma caveat: no pointwise bound follows (band ≥ 2^(L−1) ≥ 1);
     continued fraction of log₃2 (`p_cf_log32.py`) bounds discrepancy D*_N.
   - "What is proven vs heuristic" table.

4. **ROADMAP**: mark the Phase 9 β line DONE, with the qualified result summary.

## Success gates

- Script runs clean with Python stdlib (decimal), exit 0.
- PASS check: `β_eff_rigorous < α` on the tested grid.
- CSV written with all 12 columns; optimizers auditable (k,K not at boundary
  artifacts; documented K-cap policy).
- Findings doc records both exact and rigorous variants and the qualification.

## Out of scope

- Lean changes (`NarkiewiczBound.lean` untouched; `narkiewicz_real_bound` stays).
- No new Rust computation (K=40 record continues in background).
- No use of the middle-block independence factor (M1-C2) in the bound.
- No claim of a global pointwise β < α theorem.

## Constraints

- Python stdlib only (decimal for the exact sum; fallback to `C·(2/3)^K` tail
  documented if K too large).
- One commit per task, plan-driven execution with review.

## References

- `ErdosTernary/ErdosTernary/NarkiewiczBound.lean` (fiber bound, real bound).
- `ErdosTernary/ErdosTernary/Narkiewicz.lean` (`u`, `pow_mod_injective`).
- `verify_middle/PHASE8_FINDINGS.md` (leading-digit law, C, 1.152 bound,
  Obstruction Lemma).
- `verify_middle/p_cf_log32.py` (continued fraction of log₃2, discrepancy).
- `verify_middle/refine_conjectures.py` (script style reference).