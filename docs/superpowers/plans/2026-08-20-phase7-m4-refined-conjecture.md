# Phase 7 M4 — Refined Conjecture Document Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Produce `verify_middle/REFINED_CONJECTURES.md` — a consolidated, precisely-stated refined conjecture with explicit proved/empirical/conjectural labeling — plus a stdlib Python script that re-derives every stated constant from the existing CSVs, and flip the ROADMAP M4 checkbox.

**Architecture:** Three independent deliverables, each a self-contained task: (1) the verification script `refine_conjectures.py` that recomputes all constants from `results_m1.csv` and `first2_records.csv` and PASS/FAIL-checks them; (2) the research document whose Evidence section is populated from the script output; (3) the ROADMAP update. No new computation beyond reading the two CSVs; K=40 continues running in the background.

**Tech Stack:** Python 3 stdlib (`csv`, `math`, `statistics`) — no third-party deps. Markdown. git.

## Global Constraints

- Python stdlib only (match `verify_middle/p_cf_log32.py` style: `#!/usr/bin/env python3`, docstring header, `csv`/`math`/`statistics`).
- Run scripts from repo root (`verify_middle/results_m1.csv`, `verify_middle/first2_records.csv` paths are relative to repo root, exactly as in `p_cf_log32.py`).
- The epistemic labels are mandatory: `n > 1000` / `0.246` and `f(n) ≤ 3.5·log₃ n` are **conjectural extrapolations, not proved results**. Never phrase them as theorems.
- Datasets already exist and are verified — do NOT regenerate them.
- One commit per task; conventional commit style; commit messages match repo style (`feat(verify): …`, `docs(lean): …` → here `feat(verify_middle): …`, `docs(verify_middle): …`).
- Spec: `docs/superpowers/specs/2026-08-20-phase7-m4-refined-conjecture-design.md`.

---

### Task 1: Verification script `refine_conjectures.py`

**Files:**
- Create: `verify_middle/refine_conjectures.py`

**Interfaces:**
- Consumes: `verify_middle/results_m1.csv` (columns `n,L,W,t_freq,…,m_freq,m_long,m_free,…,l_freq,…`, booleans as `'true'`/`'false'` strings) and `verify_middle/first2_records.csv` (columns `n,f,L,ratio,prefix,mantissa_precision,record_number,gap_from_previous_record`).
- Produces: stdout verification report with one PASS/FAIL line per check; exit code 0 iff all checks pass. Task 2 reads this output to fill the Evidence tables.

**Checks and expected values:**

| # | Check | Source | Expected |
|---|---|---|---|
| 1 | min middle-window digit-2 freq over n>1000 | `m_freq` | `0.24619289340101522` at n=1874 |
| 2 | n with 2-free middle window (`m_free=='true'`) | `m_free` | `{14, 24, 76}` |
| 3 | longest 2-free run in middle window | `m_long` | `61` at n=385178 |
| 4 | max f/log₃ n over records | `f`, `n` | `3.4361768249349467` at n=121 |
| 5 | least-squares fit f ≈ a·log_{3/2} n + b (records with n>0) | `f`, `n` | `|a − 1.04| < 0.02`, report b |
| 6 | record table consistency: ratio=f/L, f strictly increasing, gap=n−prev_n | `n,f,L,ratio,gap_from_previous_record` | all hold |

- [ ] **Step 1: Write the script with all checks**

Create `verify_middle/refine_conjectures.py` with this structure:

```python
#!/usr/bin/env python3
"""Phase 7 M4: re-derive every constant in REFINED_CONJECTURES.md.

Reads the two existing, verified datasets and checks each stated constant:
the middle-window digit-2 frequency floor, the set of 2-free middle windows,
the longest 2-free middle run, the first-2-position record statistics, and the
log_{3/2} growth fit.  Every constant here is an EMPIRICAL measurement (or a
conjectural extrapolation labeled as such in REFINED_CONJECTURES.md) -- none of
these are proved results.  Python stdlib only. Run from repo root.
"""

import csv
import math
import statistics

M_FLOOR_EXPECTED = 0.24619289340101522
M_FLOOR_ARG_N = 1874
M_FREE_EXPECTED = {14, 24, 76}
M_LONG_EXPECTED = 61
M_LONG_ARG_N = 385178
RATIO_MAX_EXPECTED = 3.4361768249349467
RATIO_MAX_ARG_N = 121


def load_m1():
    with open("verify_middle/results_m1.csv") as f:
        return list(csv.DictReader(f))


def load_records():
    with open("verify_middle/first2_records.csv") as f:
        return list(csv.DictReader(f))


def check(name, cond, detail=""):
    print(f"{'PASS' if cond else 'FAIL'}  {name}{'  -- ' + detail if detail else ''}")
    return cond


def middle_floor(rows):
    best = None
    for r in rows:
        n = int(r["n"])
        if n <= 1000:
            continue
        freq = float(r["m_freq"])
        if best is None or freq < best[0]:
            best = (freq, n)
    return best


def main():
    rows = load_m1()
    records = load_records()
    results = []

    floor_val, floor_n = middle_floor(rows)
    results.append(check("middle-window freq floor = 0.24619289340101522",
                         math.isclose(floor_val, M_FLOOR_EXPECTED, rel_tol=1e-12) and floor_n == M_FLOOR_ARG_N,
                         f"got {floor_val} at n={floor_n}"))

    free = {int(r["n"]) for r in rows if r["m_free"] == "true"}
    results.append(check("2-free middle windows = {14,24,76}",
                         free == M_FREE_EXPECTED, f"got {sorted(free)}"))

    longest, arg = max((int(r["m_long"]), int(r["n"])) for r in rows)
    results.append(check("longest middle 2-free run = 61 at n=385178",
                         longest == M_LONG_EXPECTED and arg == M_LONG_ARG_N,
                         f"got {longest} at n={arg}"))

    ratios = [(int(r["f"]) / math.log(int(r["n"]), 3), int(r["n"])) for r in records if int(r["n"]) > 1]
    rmax, rarg = max(ratios)
    results.append(check("max f/log3(n) = 3.4361768249349467 at n=121",
                         math.isclose(rmax, RATIO_MAX_EXPECTED, rel_tol=1e-12) and rarg == RATIO_MAX_ARG_N,
                         f"got {rmax} at n={rarg}"))

    sel = [(int(r["n"]), int(r["f"])) for r in records if int(r["n"]) > 0]
    xs = [math.log(n, 1.5) for n, _ in sel]
    ys = [f for _, f in sel]
    mx, my = statistics.mean(xs), statistics.mean(ys)
    a = sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / sum((x - mx) ** 2 for x in xs)
    b = my - a * mx
    results.append(check("log_{3/2} growth fit slope a ~ 1.04",
                         abs(a - 1.04) < 0.02, f"got a={a:.3f}, b={b:.3f}"))

    fs = [int(r["f"]) for r in records]
    mono = all(fs[i] < fs[i + 1] for i in range(len(fs) - 1))
    ratio_ok = all(math.isclose(float(r["ratio"]), int(r["f"]) / int(r["L"]), rel_tol=1e-9) for r in records)
    gaps = [int(r["n"]) for r in records]
    gap_ok = all(gaps[i] - gaps[i - 1] == int(records[i]["gap_from_previous_record"]) for i in range(1, len(records)))
    results.append(check("record table consistent (f inc, ratio=f/L, gaps)",
                         mono and ratio_ok and gap_ok))

    print("\nAll checks passed." if all(results) else "\nSome checks FAILED.")
    raise SystemExit(0 if all(results) else 1)


if __name__ == "__main__":
    main()
```

- [ ] **Step 2: Run it and verify all checks PASS**

Run: `python3 verify_middle/refine_conjectures.py`
Expected: every line `PASS`, final `All checks passed.`, exit code 0.

- [ ] **Step 3: Commit**

```bash
git add verify_middle/refine_conjectures.py
git commit -m "feat(verify_middle): M4 constant re-derivation script"
```

---

### Task 2: Research document `REFINED_CONJECTURES.md`

**Files:**
- Create: `verify_middle/REFINED_CONJECTURES.md`

**Interfaces:**
- Consumes: output of `refine_conjectures.py` (Task 1) for the Evidence section; the two datasets; existing findings (`verify_middle/FINDINGS.md`, `verify_middle/PHASE8_FINDINGS.md`).
- Produces: the consolidated conjecture document referenced by the ROADMAP (Task 3).

- [ ] **Step 1: Write the document**

Create `verify_middle/REFINED_CONJECTURES.md` with exactly these sections:

1. **Status table** — three categories **Proved / Empirical / Conjectural**, with the definitions from the spec §1 (Proved = rigorous argument, e.g. the exact `P(f ≥ L)` law and counting-identity bounds from Phase 8; Empirical = measured exactly over the stated range; Conjectural = extrapolated, falsifiable by one counterexample).
2. **M4-C (middle-window digit-2 lower bound; conjectural)** — statement: *For every `n > 8`, the middle third `[⌊L/3⌋, ⌊2L/3⌋)` of the ternary expansion of `2ⁿ` contains a digit 2; more precisely, the digit-2 frequency in that window is ≥ 0.246 for `n > 1000`.* Followed by the mandatory boxed caveat:
   > The threshold `n > 1000` and the constant `0.246` are **conjectural extrapolations** from the existing dataset (`n ≤ 10⁶`, `verify_middle/results_m1.csv`). They are **not proved results.** The measured facts are: the only n with a 2-free middle window over `9 ≤ n ≤ 10⁶` are `n ∈ {14, 24, 76}`, and the minimum middle-window digit-2 frequency over `1000 < n ≤ 10⁶` is `0.246192893` at `n = 1874`.
3. **M4-C2 (two-sided independence; empirical + conjectural)** — Spearman |ρ| < 0.005 over n ≤ 10⁶, boundary digits pair near-uniformly; explicitly state: measured (empirical) over n ≤ 10⁶, extrapolation to all n is conjectural.
4. **M4-C3 (first-2-position linear bound; conjectural)** — statement: *For every n ≥ 1, `f(n) ≤ 3.5·log₃ n`.* State throughout: *a conjecture supported by all tested data (n ≤ 10⁹), not a theorem*. Sharpest tested point n=121, `f/log₃ n ≈ 3.437`; ratio decays toward ≈ 2.8; records obey `f ≈ log_{3/2} n` (least-squares `a ≈ 1.04`).
5. **Evidence** — tables generated from the Task-1 script output (run it, paste the exact values): floor + argmin, 2-free set, longest run, all 19 records, `f/log₃ n` max, growth fit. Each table captioned **"Empirical — measured over n ≤ 10⁶"** or **"n ≤ 10⁹"; not proved.** Do not paste a bare dump; format the numbers as clean Markdown tables. State under the table: *numbers generated by `python3 verify_middle/refine_conjectures.py`; rerun to refresh.*
6. **Falsification criteria** — M4-C: any n>76 with a 2-free middle window, or any n>1000 with freq < 0.246; M4-C2: significant dependence between any window-frequency pair; M4-C3: any n with `f(n) > 3.5·log₃ n`. One counterexample refutes; proved results immune.
7. **Relation to Erdős / Phase 9** — middle-window bound proves the full conjecture for n>8 if shown; two-sided search treats blocks as independent (M4-C2 justifies over the measured range); first-2 bound would combine with Saye's trailing pruning to certify far beyond 5.9×10²¹ (from PHASE8_FINDINGS §"New conjecture").

Definitions section at top: `L(n) = ⌊n·log₃2⌋ + 1`; `W = ⌊L/3⌋`; window ranges (LSB-first); `f(n)` (first-2 position from MSB, 0-indexed, `L(n)` if none).

- [ ] **Step 2: Verify the document**

Run: `python3 verify_middle/refine_conjectures.py` (must still PASS), then grep the doc for the label requirement:
`rg -n "not a theorem|not proved" verify_middle/REFINED_CONJECTURES.md`
Expected: at least two matches (the M4-C caveat and the M4-C3 statement). Ensure no line claims either bound as proved.

- [ ] **Step 3: Commit**

```bash
git add verify_middle/REFINED_CONJECTURES.md
git commit -m "docs(verify_middle): Phase 7 M4 refined conjecture document"
```

---

### Task 3: ROADMAP update

**Files:**
- Modify: `ROADMAP.md` (the M4 line, currently `- [ ] **M4 (refined conjecture):** e.g. middle-window lower bound + record growth-rate conjecture (partial in `FINDINGS.md` M1-C1/M1-C2).`)

**Interfaces:**
- Consumes: Tasks 1–2 (script + document exist and pass).
- Produces: ROADMAP reflecting M4 as done.

- [ ] **Step 1: Flip the M4 checkbox and update the summary**

Replace the M4 line in `ROADMAP.md` with:

```markdown
- [x] **M4 (refined conjecture):** consolidated in `verify_middle/REFINED_CONJECTURES.md` — M4-C middle-window digit-2 lower bound (conjectural: freq ≥ 0.246 for n>1000, only 2-free middle windows {14,24,76}); M4-C2 two-sided independence; M4-C3 first-2-position bound `f(n) ≤ 3.5·log₃ n` (conjectural, not a theorem). Constants re-derivable via `python3 verify_middle/refine_conjectures.py`.
```

- [ ] **Step 2: Verify**

Run: `python3 verify_middle/refine_conjectures.py` — all PASS. Confirm the checkbox line is flipped and the doc path is correct.

- [ ] **Step 3: Commit**

```bash
git add ROADMAP.md
git commit -m "docs: flip Phase 7 M4 checkbox in ROADMAP"
```

---

## Self-Review

**Spec coverage:** §1 status table → Task 2 §1; §2 M4-C + caveat → Task 2 §2 (caveat verbatim); §3 M4-C2/M4-C3 → Task 2 §3–4; §4 evidence tables → Task 2 §5 (fed by Task 1); §5 falsification → Task 2 §6; §6 relation → Task 2 §7; Deliverable 2 (script) → Task 1 with all six checks; Deliverable 3 (ROADMAP) → Task 3. All spec sections mapped.

**Placeholder scan:** every step contains full code or explicit text content; no TBD/TODO.

**Type consistency:** `m_freq`, `m_free`, `m_long`, `f`, `L`, `n`, `ratio`, `gap_from_previous_record` column names match both the CSV headers and the script usage; `REFINED_CONJECTURES.md` referenced identically in Tasks 2–3; the caveat wording is a single source of truth (spec + Task 2 §2, copied verbatim).