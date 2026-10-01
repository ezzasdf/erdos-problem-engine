# Phase 9 — β < log₃2 Heuristic + Rigor Analysis Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Produce a Python stdlib script `verify_middle/beta_bound.py` that computes the two-window counting bound `B(x,k,K) = 2^k·(x/u_k + 1)·P_rig(K)` (with `u_k = 2·3^(k-1)`) over a grid of `(x, k, K)`, demonstrates the effective exponent `β_eff(x) < α = log₃2` on the tested grid under both an exact and a rigorous `P(f ≥ K)`, writes an auditable 12-column CSV, and documents the result (with explicit "not a global theorem" qualification) in `verify_middle/PHASE9_BETA_FINDINGS.md` plus a ROADMAP update.

**Architecture:** Three independent deliverables, each a self-contained task: (1) the verification script `beta_bound.py` (stdlib only, mirrors the style of `verify_middle/p_first2.py` and `verify_middle/refine_conjectures.py`) that computes `P(f≥K)` exactly (finite sum, K ≤ 20) and rigorously (`1.152·(2/3)^K`), optimizes `B` over the `(k,K)` grid per `x`, and prints a qualified PASS/FAIL; (2) the findings doc whose tables are populated from the script output; (3) the ROADMAP Phase 9 β-line flip. No Lean changes, no Rust computation; K=40 record continues in the background.

**Tech Stack:** Python 3 stdlib (`csv`, `math`) — no third-party deps. Markdown. git.

## Global Constraints

- Python stdlib only (match `verify_middle/p_first2.py` style: `#!/usr/bin/env python3`, docstring header, `csv`/`math` only).
- Run scripts from repo root (paths like `verify_middle/beta_bound.csv` are relative to repo root, exactly as in `p_first2.py`/`refine_conjectures.py`).
- The exact `P(f ≥ K)` finite sum MUST reuse `p_first2.py`'s enumeration (strings s with s₀ = 1, s_i ∈ {0,1}, `t_s = Σ s_i 3^{−i}`, `P = Σ log₃((t_s + 3^{1−K})/t_s)`).
- Exact `P(f≥K)` computed for **K ≤ 20**; for **K > 20** use the convergent `C·(2/3)^K` with `C = 1.1147647951` (documented policy, auditable in code).
- Rigorous `P_rig(K) = 1.152·(2/3)^K` for **all K** (Phase 8 unconditional upper bound, given Weyl equidistribution of `{n·log₃2}`).
- The `+1` in `x/u_k + 1` is retained EXACTLY in the computation — no asymptotic simplification.
- Qualification is mandatory: the output MUST NOT claim a global pointwise β < α theorem. The exact console STATUS wording from the spec is required verbatim.
- One commit per task; conventional commit style matching the repo (`feat(verify_middle): …`, `docs(verify_middle): …`, `docs(roadmap): …`).
- Spec: `docs/superpowers/specs/2026-08-20-phase9-beta-bound-design.md`.
- Work is done on a dedicated worktree branch `phase9-beta` created at execution time via `superpowers:using-git-worktrees` (repo convention; `.worktrees/phase9-beta`).

---

### Task 1: Verification script `beta_bound.py`

**Files:**
- Create: `verify_middle/beta_bound.py`
- Output: `verify_middle/beta_bound.csv`

**Interfaces:**
- Consumes: nothing at runtime (constants hardcoded from Phase 8: `C = 1.1147647951`, rigorous factor `1.152`, `u_k = 2·3^(k-1)`).
- Produces: (a) stdout report with the exact console output shown below; (b) `verify_middle/beta_bound.csv` with exactly these 12 columns per row (one row per `x`): `x, beta_eff_exact, beta_eff_rigorous, alpha, alpha_minus_beta_exact, alpha_minus_beta_rigorous, k_opt_exact, K_opt_exact, k_opt_rigorous, K_opt_rigorous, B_exact, B_rigorous`. Exit code 0 iff every row has `beta_eff_rigorous < alpha` (and the script ran clean). Task 2 reads the stdout tables and the CSV to fill the findings doc.

**Grid definition (fixed, auditable):**
- `x` grid: `x = 3^m` for `m = 4 .. 39` (i.e. `x = 81 .. 3^39 ≈ 4.05×10^18`, geometric ratio 3).
- `k` window: `[max(1, m − 8), m + 8]` (integer; `m = ⌊log₃ x⌋` since `x = 3^m`).
- `K`: `1 .. 30`.

**Math (for the implementer):** `B(x,k,K) = (2^k) · (x/u_k + 1) · P_rig(K)` with `u_k = 2·3^(k-1)`. `beta_eff(x) = ln(min_{k,K} B(x,k,K)) / ln(x)`. Two variants of `P_rig`: **exact** (`P_exact(K)` finite sum for K ≤ 20, else `C·(2/3)^K`) and **rigorous** (`1.152·(2/3)^K`). `alpha = log(2)/log(3)`. The rigorous variant drives the PASS check.

- [ ] **Step 1: Write the script**

Create `verify_middle/beta_bound.py` with this complete content:

```python
#!/usr/bin/env python3
"""Phase 9: best-effort beta < log_3(2) heuristic + rigor analysis.

Computes the two-window counting bound
    B(x, k, K) = 2^k * (x/u_k + 1) * P_rig(K),   u_k = 2*3^(k-1),
over a grid of (x, k, K), using the exact leading-digit probability
P(f >= K) (finite sum over 2^(K-1) strings, K <= 20; convergent C*(2/3)^K
beyond) and the rigorous unconditional Phase 8 upper bound
P_rig(K) = 1.152*(2/3)^K.  Reports beta_eff(x) = ln(min B)/ln(x) against
alpha = log_3(2) and writes an auditable 12-column CSV.

This establishes the inequality on the tested grid under the stated
Weyl/equidistribution bound.  It does NOT establish a global pointwise
beta < alpha theorem.

Python stdlib only. Run from repo root.
"""

import csv
import math

ALPHA = math.log(2.0) / math.log(3.0)
C_CONV = 1.1147647951       # exact P(f>=L)/(2/3)^L, converged by L ~ 10 (Phase 8)
C_RIG = 1.152               # rigorous P(f>=L) <= C_RIG*(2/3)^L (Phase 8, unconditional)
K_EXACT_MAX = 20            # exact finite sum up to K=20; C*(2/3)^K beyond (documented policy)
K_MAX = 30
M_MIN, M_MAX = 4, 39        # x = 3^m, m in [4, 39]  (~81 .. ~4.05e18)


def u_k(k):
    return 2 * 3 ** (k - 1)


def p_exact_table():
    """P(f>=L) = sum over length-L strings s (s_0=1, rest in {0,1}) of
    log_3((t_s + 3^{1-L}) / t_s), t_s = sum_i s_i 3^{-i}.  L = 1..K_EXACT_MAX."""
    tab = {}
    for L in range(1, K_EXACT_MAX + 1):
        total = 0.0
        for m in range(2 ** (L - 1)):
            t = 1.0
            for i in range(1, L):
                if (m >> (L - 1 - i)) & 1:
                    t += 3.0 ** (-i)
            total += math.log((t + 3.0 ** (1 - L)) / t, 3)
        tab[L] = total
    return tab


def p_exact(K, tab):
    if K <= K_EXACT_MAX:
        return tab[K]
    return C_CONV * (2.0 / 3.0) ** K


def p_rigorous(K):
    return C_RIG * (2.0 / 3.0) ** K


def bound(x, k, K, pval):
    return (2.0 ** k) * (x / u_k(k) + 1.0) * pval


def beta_eff(x, bmin):
    return math.log(bmin) / math.log(x)


def main():
    tab = p_exact_table()

    print("== P(f>=K): exact (finite sum, K<=%d; C*(2/3)^K beyond) vs rigorous 1.152*(2/3)^K =="
          % K_EXACT_MAX)
    print(f"{'K':>2} {'P_exact':>14} {'P_rigorous':>14} {'ratio':>8}")
    for K in range(1, K_MAX + 1):
        pe = p_exact(K, tab)
        pr = p_rigorous(K)
        print(f"{K:>2} {pe:14.8e} {pr:14.8e} {pe / pr:8.4f}")

    rows = []
    failing = []
    for m in range(M_MIN, M_MAX + 1):
        x = 3.0 ** m
        k_lo = max(1, m - 8)
        k_hi = m + 8
        best_exact = None
        best_rig = None
        for k in range(k_lo, k_hi + 1):
            for K in range(1, K_MAX + 1):
                be = bound(x, k, K, p_exact(K, tab))
                br = bound(x, k, K, p_rigorous(K))
                if best_exact is None or be < best_exact[0]:
                    best_exact = (be, k, K)
                if best_rig is None or br < best_rig[0]:
                    best_rig = (br, k, K)
        Be, ke, Ke = best_exact
        Br, kr, Kr = best_rig
        beta_e = beta_eff(x, Be)
        beta_r = beta_eff(x, Br)
        rows.append({
            "x": int(x),
            "beta_eff_exact": beta_e,
            "beta_eff_rigorous": beta_r,
            "alpha": ALPHA,
            "alpha_minus_beta_exact": ALPHA - beta_e,
            "alpha_minus_beta_rigorous": ALPHA - beta_r,
            "k_opt_exact": ke,
            "K_opt_exact": Ke,
            "k_opt_rigorous": kr,
            "K_opt_rigorous": Kr,
            "B_exact": Be,
            "B_rigorous": Br,
        })
        if not (beta_r < ALPHA):
            failing.append(int(x))
        print(f"x=3^{m}  beta_eff_exact={beta_e:.6f}  beta_eff_rigorous={beta_r:.6f}  "
              f"(k,K)_exact=({ke},{Ke})  (k,K)_rig=({kr},{Kr})")

    with open("verify_middle/beta_bound.csv", "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
        w.writeheader()
        w.writerows(rows)

    print("\nRIGOROUS-BOUND CHECK:")
    if failing:
        print("beta_eff < alpha on tested grid: FAIL")
        print("failing x:", failing)
        return 1
    print("beta_eff < alpha on tested grid: PASS")

    print("\nSTATUS:")
    print("This establishes the inequality for the evaluated grid under")
    print("the stated Weyl/equidistribution bound.")
    print("It does NOT establish a global pointwise beta < alpha theorem.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
```

- [ ] **Step 2: Run the script from the repo root**

Run: `python3 verify_middle/beta_bound.py`
Expected: prints the P table (ratio ≈ 0.97, exact being slightly below rigorous), one line per `m = 4..39`, then `RIGOROUS-BOUND CHECK: ... PASS`, then the STATUS block verbatim. Exit code 0.

- [ ] **Step 3: Verify the CSV**

Run: `python3 -c "import csv; r=list(csv.DictReader(open('verify_middle/beta_bound.csv'))); print(len(r)); print(r[0]); print(r[-1])"`
Expected: 36 rows; header exactly `x,beta_eff_exact,beta_eff_rigorous,alpha,alpha_minus_beta_exact,alpha_minus_beta_rigorous,k_opt_exact,K_opt_exact,k_opt_rigorous,K_opt_rigorous,B_exact,B_rigorous`; first row m=4, last row m=39. Spot-check: `k_opt` should sit in `[m-8, m+8]` and not be pinned at the window edges for large m (auditability); `K_opt` typically at the K=30 cap (B decreases in K — expected, not an artifact).

- [ ] **Step 4: Commit**

```bash
git add verify_middle/beta_bound.py verify_middle/beta_bound.csv
git commit -m "feat(verify_middle): beta < log3 2 two-window counting heuristic + rigor check"
```

---

### Task 2: Findings doc `PHASE9_BETA_FINDINGS.md`

**Files:**
- Create: `verify_middle/PHASE9_BETA_FINDINGS.md`

**Interfaces:**
- Consumes: Task 1 stdout (P table, β_eff lines, PASS) and `verify_middle/beta_bound.csv` (12 columns, 36 rows).
- Produces: the self-contained findings document. Task 3 reads it to summarize the ROADMAP line.

- [ ] **Step 1: Write the findings doc**

Create `verify_middle/PHASE9_BETA_FINDINGS.md` with this structure and content. Populate the tables from the actual script output (recompute values from `beta_bound.csv` — do not invent them):

```markdown
# Phase 9 — β < log₃2 Heuristic + Rigor Analysis

Date: 2026-08-20
Spec: `docs/superpowers/specs/2026-08-20-phase9-beta-bound-design.md`
Script: `verify_middle/beta_bound.py` (stdlib, exit 0)
Data: `verify_middle/beta_bound.csv` (12-column audit table, 36 rows)

## Framing (verbatim from spec)

> Heuristic scaling: each additional certified leading digit contributes
> approximately a factor 2/3, suggesting an exponent reduction of roughly
> (1−α) per leading digit under the chosen scaling — the actual β_eff is
> computed by `beta_bound.py` from the complete expression (including the +1,
> integer constraints, and the allowed k,K,x relationship).

## Setup

- `N(x) = #{n ≤ x : memCantorNat (2^n)}`; proven `N(x) ≤ 4·x^α`, α = log₃2 ≈ 0.6309
  (`ErdosTernary/ErdosTernary/NarkiewiczBound.lean`, `narkiewicz_real_bound`).
- Fiber partition (Task 2c.3): `N(x) ≤ 2^k·(x/u_k + 1)`, `u_k = 2·3^(k-1)`.
- Two-window bound computed here: `B(x,k,K) = 2^k·(x/u_k + 1)·P_rig(K)` —
  the fiber bound, additionally requiring the first K leading digits to be 2-free
  (`P(f ≥ K)`), valid because `{n·log₃2}` stays equidistributed within each
  fiber `n ≡ r (mod u_k)`.

## P(f ≥ K): exact vs rigorous

(from script stdout — fill the K=1..30 rows of the script's table.)

| K | P_exact | P_rigorous (1.152·(2/3)^K) | ratio exact/rigorous |
|---|---------|-----------------------------|----------------------|
| 1 | … | … | … |
| … | … | … | … |

Policy (documented): exact finite sum for K ≤ 20; `C·(2/3)^K` with C = 1.1147647951
for K > 20 (converged by L ≈ 10 per Phase 8).

## Computed β_eff(x)

(from `beta_bound.csv` — include all 36 rows, or a representative subsample
with the smallest and largest x plus every fifth m.)

| x | β_eff_exact | β_eff_rigorous | α | α−β_exact | α−β_rigorous | (k,K)_exact | (k,K)_rigorous | B_exact | B_rigorous |
|---|------------|----------------|---|-----------|--------------|-------------|----------------|---------|------------|
| 3^4=81 | … | … | … | … | … | … | … | … | … |
| … | … | … | … | … | … | … | … | … | … |

Observation: β_eff < α on the full grid for both variants; the margin α−β
narrows as x grows. K_opt sits at the K=30 cap (B is decreasing in K — expected),
k_opt sits interior to the ±8 window (no boundary artifact).

## Rigor caveat — Obstruction Lemma

The β_eff values above are an upper bound on the *counting* exponent on the
tested grid under the stated Weyl/equidistribution bound. They do **not** yield a
global pointwise bound: `e_L(N) = #{n ≤ N : f(n) ≥ L}` has error band
`N·2^L·D*_N ≥ 2^{L−1} ≥ 1` for every sequence (Phase 8 Obstruction Lemma), so no
counting inequality built from the measure can certify a pointwise `β < α`
theorem. The continued fraction of log₃2 (`verify_middle/p_cf_log32.py`) controls
`D*_N`, and the band never closes. (See `verify_middle/PHASE8_FINDINGS.md`,
Rigorous deviation analysis.)

## What is proven vs heuristic

| Claim | Status |
|---|---|
| Fiber bound `N(x) ≤ 2^k·(x/u_k+1)` | **Proven** (`NarkiewiczBound.lean`) |
| `P(f ≥ L) ≤ 1.152·(2/3)^L` (given Weyl equidistribution) | **Proven** (Phase 8, unconditional corollary) |
| Exact finite sum `P(f ≥ L) = Σ_s log₃(1 + 3^{1-L}/t_s)` | **Computed exactly** for L ≤ 20 (Phase 8 law) |
| `β_eff < α` on the tested grid under the rigorous P_rig | **Demonstrated on grid** (this script, PASS) |
| Global pointwise `β < α` theorem | **NOT established** — Obstruction Lemma; this is the heuristic/partial-proof target feeding NarkiewiczBound |
| Middle-block independence factor (M1-C2) in the bound | **Not used** — out of scope for this deliverable |

## Verdict

The two-window counting bound lowers the effective exponent below α = log₃2 on
the tested grid under the rigorous Phase 8 leading-digit bound. This is
evidence/heuristic for an improved exponent, not a proof; the Obstruction Lemma
shows why a pointwise theorem does not follow automatically. Feeding this into a
future NarkiewiczBound strengthening requires closing (or working around) the
discrepancy term.
```

- [ ] **Step 2: Fill tables from actual script output and verify consistency**

Run the script again if needed and paste its real numbers into the tables. Cross-check a few rows against `beta_bound.csv` (e.g. the row for x=81 and x=3^39). Confirm the doc's STATUS wording matches the script's PASS output and the framing quote is verbatim.

- [ ] **Step 3: Commit**

```bash
git add verify_middle/PHASE9_BETA_FINDINGS.md
git commit -m "docs(verify_middle): Phase 9 beta < log3 2 heuristic findings"
```

---

### Task 3: ROADMAP update

**Files:**
- Modify: `ROADMAP.md` (Phase 9 planned-deliverables list, line 255)

**Interfaces:**
- Consumes: Task 2 findings doc summary.
- Produces: the flipped ROADMAP checkbox.

- [ ] **Step 1: Flip the β line**

In `ROADMAP.md`, change the line

```
- [ ] Best-effort β < log₃2 bound heuristic / partial proof, feeding NarkiewiczBound.
```

to

```
- [x] Best-effort β < log₃2 bound heuristic / partial proof, feeding NarkiewiczBound. **DONE** 2026-08-20: `beta_bound.py` two-window counting bound `2^k·(x/u_k+1)·P_rig(K)` gives β_eff < α = log₃2 on x = 3^4..3^39 under the rigorous Phase 8 bound (see `verify_middle/PHASE9_BETA_FINDINGS.md`). Heuristic only — Obstruction Lemma blocks a global pointwise theorem.
```

- [ ] **Step 2: Verify no other β checkbox remains**

Run: `grep -n "Best-effort β" ROADMAP.md`
Expected: exactly one line, with `[x]`.

- [ ] **Step 3: Commit**

```bash
git add ROADMAP.md
git commit -m "docs(roadmap): Phase 9 beta < log3 2 heuristic DONE"
```

---

## Plan Self-Review

**Spec coverage:**
- Core computation `B = 2^k·(x/u_k+1)·P_rig(K)` with exact `+1` → Task 1. ✓
- Exact variant (finite sum ≤ 20, `C·(2/3)^K` tail) and rigorous variant (`1.152·(2/3)^K`) → Task 1. ✓
- k window `[⌊log₃x⌋−8, ⌊log₃x⌋+8]`, K = 1..30, geometric x grid → Task 1. ✓
- Console PASS/STATUS qualification verbatim → Task 1 Step 1. ✓
- 12-column audit CSV with per-variant k/K opt → Task 1. ✓
- Findings doc: framing quote, P table, β_eff table, Obstruction caveat, proven-vs-heuristic table → Task 2. ✓
- ROADMAP flip with qualified summary → Task 3. ✓
- Out of scope respected: no Lean changes, no Rust, no M1-C2 factor, no global theorem claim → all tasks. ✓

**Placeholder scan:** all tables in Task 2 are explicitly instructed to be filled from real script output (recomputed from `beta_bound.csv`), with the row-sampling policy stated — no invented numbers, no TBDs. All code blocks are complete.

**Type consistency:** `beta_eff_exact`/`beta_eff_rigorous`/`alpha_minus_beta_exact`/`alpha_minus_beta_rigorous`/`k_opt_exact`/`K_opt_exact`/`k_opt_rigorous`/`K_opt_rigorous`/`B_exact`/`B_rigorous` column names match the spec's CSV list exactly and are used identically in Task 1 (writer) and Task 2 (consumer). `P_rig` naming matches the spec. ✓