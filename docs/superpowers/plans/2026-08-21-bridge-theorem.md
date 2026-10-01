# Phase 12: Leading/Trailing Orbit Intersection (Bridge Theorem) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Collect per-candidate signatures (n mod u_K, {n·α}, leading prefix, trailing suffix) for all survivors in A_L ∩ B_K, then search for correlations that could become a bridge theorem.

**Architecture:** Python script for data collection at small K (≤ 15), using interval arithmetic for the leading check. Correlation analysis on the collected data. Bridge conjecture formulation from the patterns found.

**Tech Stack:** Python 3, stdlib only (math, csv, collections, itertools). Reuses concepts from `padic_orbit_analysis.py` and the Rust engine's leading check.

## Global Constraints

- Python 3, no external dependencies
- K max for Python data collection: 15 (u_15 = 2·3^14 ≈ 9.5M — feasible)
- L values to test: 10, 20, 30, 40, 50, 60, 70
- Output: CSV data files + findings markdown
- One conventional commit per task

---

### Task 1: Leading-Digit Check in Python

**Files:**
- Create: `verify_middle/bridge_analysis.py`

**Interfaces:**
- Produces: `leading_prefix(n, L) -> str`, `has_digit_2_in_prefix(n, L) -> bool`

- [ ] **Step 1: Create the script with core functions**

```python
#!/usr/bin/env python3
"""Phase 12: Leading/Trailing Orbit Intersection — Bridge Theorem Analysis.

Collects per-candidate signatures for A_L ∩ B_K survivors and searches
for correlations between leading and trailing ternary digits of 2^n.
"""

import csv
import math
from typing import List, Tuple, Set, Dict


# --- Constants ---

ALPHA = math.log(2) / math.log(3)  # log_3(2), approximate


def u_k(k: int) -> int:
    """Period of 2^n mod 3^k: u_k = 2 * 3^(k-1)."""
    return 2 * (3 ** (k - 1))


def fractional_part(n: int, precision_bits: int = 128) -> float:
    """Compute {n * alpha} using high-precision floating point.

    For K ≤ 15, standard float64 gives ~15 decimal digits of precision,
    which is sufficient for extracting the first 70 ternary digits.
    """
    return (n * ALPHA) % 1.0


def leading_prefix(n: int, L: int) -> str:
    """Compute the first L ternary digits of 2^n.

    Uses the identity: the first L ternary digits of 2^n are the first L
    digits of 3^{{n * alpha}} in base 3.

    Returns a string of '0' and '1' (the digit '2' means the prefix contains a 2).
    """
    frac = fractional_part(n)
    # Compute 3^frac via repeated squaring in floating point
    # For L ≤ 70 digits, we need 3^frac to ~L * log10(3) ≈ L * 0.477 decimal digits
    # float64 gives ~15 digits, sufficient for L ≤ 30
    # For L > 30, use the mpmath-free approach: iterate base-3 long division
    val = 3.0 ** frac  # 1.0 <= val < 3.0
    digits = []
    for _ in range(L):
        val *= 3.0
        d = int(val)
        digits.append(str(d))
        val -= d
    return ''.join(digits)


def has_digit_2_in_prefix(n: int, L: int) -> bool:
    """Check if the first L ternary digits of 2^n contain a 2."""
    return '2' in leading_prefix(n, L)


def ternary_digits_full(n: int) -> str:
    """Compute the full ternary expansion of n (MSB first)."""
    if n == 0:
        return '0'
    digits = []
    while n > 0:
        digits.append(str(n % 3))
        n //= 3
    return ''.join(reversed(digits))


def trailing_suffix(n: int, K: int) -> str:
    """Compute the last K ternary digits of 2^n (as a string).

    Uses pow(2, n, 3**K) for efficiency.
    """
    val = pow(2, n, 3 ** K)
    return ternary_digits_full(val).zfill(K)


def is_cantor_full(n: int) -> bool:
    """Check if 2^n has ALL ternary digits in {0, 1} (full expansion)."""
    val = 2 ** n
    while val > 0:
        if val % 3 == 2:
            return False
        val //= 3
    return True
```

- [ ] **Step 2: Verify basic functions**

Run: `python3 -c "from verify_middle.bridge_analysis import *; print(leading_prefix(0, 10)); print(leading_prefix(2, 10)); print(leading_prefix(8, 10)); print(trailing_suffix(0, 5)); print(trailing_suffix(8, 5))"`

Expected:
- 2^0 = 1: leading prefix should start with '1' (1 = 1.000... in base 3)
- 2^2 = 4 = 11_3: leading prefix should start with '11'
- 2^8 = 256 = 100101_3: leading prefix should start with '100101'
- trailing_suffix(0, 5) = '00001' (2^0 = 1)
- trailing_suffix(8, 5) = '10100' (256 = 100101_3, last 5 digits = 00101)

- [ ] **Step 3: Verify leading check matches Rust for known cases**

Run: `python3 -c "from verify_middle.bridge_analysis import *; [print(f'n={n}: prefix={leading_prefix(n, 20)[:20]}, has_2={has_digit_2_in_prefix(n, 20)}') for n in [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]"`

Cross-check against the Rust engine's known results: n=0,2,8 should be trailing-2-free; leading check should show digit 2 for most n > 8.

- [ ] **Step 4: Commit**

```bash
git add verify_middle/bridge_analysis.py
git commit -m "feat: bridge analysis — leading-digit check in Python"
```

---

### Task 2: Data Collection for A_L ∩ B_K

**Files:**
- Modify: `verify_middle/bridge_analysis.py`

**Interfaces:**
- Consumes: `leading_prefix()`, `trailing_suffix()`, `u_k()` from Task 1
- Produces: `collect_signatures(K, L_values) -> List[dict]`

- [ ] **Step 1: Add data collection function**

```python
def collect_signatures(K: int, L_values: List[int]) -> List[dict]:
    """Collect signatures for all n in A_L ∩ B_K.

    For each n in [0, u_K):
    1. Check B_K(n): trailing K digits of 2^n avoid digit 2
    2. For each L in L_values, check A_L(n): first L digits avoid digit 2
    3. Record signature for survivors

    Returns list of dicts with keys:
    n, n_mod_uk, frac, leading_prefixes (dict L->prefix), trailing_suffix, survives_leading (dict L->bool)
    """
    period = u_k(K)
    results = []

    for n in range(period):
        # Trailing check: B_K(n)
        suffix = trailing_suffix(n, K)
        if '2' in suffix:
            continue  # not in B_K

        # Leading check for each L
        leading = {}
        survives_leading = {}
        for L in L_values:
            prefix = leading_prefix(n, L)
            leading[L] = prefix
            survives_leading[L] = '2' not in prefix

        frac = fractional_part(n)

        results.append({
            'n': n,
            'n_mod_uk': n % period,
            'frac': frac,
            'trailing_suffix': suffix,
            'leading_prefixes': leading,
            'survives_leading': survives_leading,
        })

    return results


def export_csv(signatures: List[dict], L_values: List[int], filepath: str):
    """Export signatures to CSV."""
    fieldnames = ['n', 'n_mod_uk', 'frac', 'trailing_suffix']
    for L in L_values:
        fieldnames.append(f'prefix_L{L}')
        fieldnames.append(f'survives_L{L}')

    with open(filepath, 'w', newline='') as f:
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()
        for sig in signatures:
            row = {
                'n': sig['n'],
                'n_mod_uk': sig['n_mod_uk'],
                'frac': f"{sig['frac']:.15f}",
                'trailing_suffix': sig['trailing_suffix'],
            }
            for L in L_values:
                row[f'prefix_L{L}'] = sig['leading_prefixes'][L]
                row[f'survives_L{L}'] = sig['survives_leading'][L]
            writer.writerow(row)
```

- [ ] **Step 2: Test data collection at K=5 (small)**

Run: `python3 -c "from verify_middle.bridge_analysis import *; sigs = collect_signatures(5, [10, 20]); print(f'K=5: {len(sigs)} B_K survivors'); [print(f'  n={s[\"n\"]}: frac={s[\"frac\"]:.4f}, L10={s[\"survives_leading\"][10]}, L20={s[\"survives_leading\"][20]}') for s in sigs[:10]]"`

Expected: K=5 has |N_5| = 16 survivors (from Phase 11). Should show all 16 with their leading check results.

- [ ] **Step 3: Commit**

```bash
git add verify_middle/bridge_analysis.py
git commit -m "feat: bridge analysis — data collection for A_L ∩ B_K"
```

---

### Task 3: Run Full Data Collection

**Files:**
- Modify: `verify_middle/bridge_analysis.py` (add main block)

**Interfaces:**
- Consumes: `collect_signatures()`, `export_csv()` from Task 2

- [ ] **Step 1: Add main block**

```python
if __name__ == "__main__":
    L_VALUES = [10, 20, 30, 40, 50, 60, 70]

    for K in [5, 8, 10, 12, 15]:
        print(f"Collecting signatures for K={K} (u_K={u_k(K)})...")
        sigs = collect_signatures(K, L_VALUES)
        print(f"  B_K survivors: {len(sigs)}")

        # Count how many survive each leading check
        for L in L_VALUES:
            count = sum(1 for s in sigs if s['survives_leading'][L])
            print(f"  A_L ∩ B_K (L={L}): {count}")

        # Export
        filepath = f"verify_middle/bridge_data_K{K}.csv"
        export_csv(sigs, L_values, filepath)
        print(f"  Exported to {filepath}")
        print()
```

- [ ] **Step 2: Run full collection**

Run: `cd /media/playplatoon/New Volume/projects/erdos\ problem\ ternary\ expansion && python3 verify_middle/bridge_analysis.py 2>&1`

This will take a while for K=15 (u_15 ≈ 9.5M iterations). Capture the output.

- [ ] **Step 3: Verify CSV output**

Run: `head -20 verify_middle/bridge_data_K5.csv && wc -l verify_middle/bridge_data_K*.csv`

Expected: K=5 should have ~16 rows, K=10 should have ~512 rows, K=15 should have ~16384 rows.

- [ ] **Step 4: Commit**

```bash
git add verify_middle/bridge_analysis.py verify_middle/bridge_data_K*.csv
git commit -m "feat: bridge analysis — full data collection K=5..15"
```

---

### Task 4: Correlation Analysis

**Files:**
- Modify: `verify_middle/bridge_analysis.py` (add analysis functions)

**Interfaces:**
- Consumes: CSV data from Task 3
- Produces: Analysis output, correlation statistics

- [ ] **Step 1: Add analysis functions**

```python
def load_signatures(filepath: str) -> List[dict]:
    """Load signatures from CSV."""
    with open(filepath, 'r') as f:
        reader = csv.DictReader(f)
        return list(reader)


def analyze_correlations(K: int, L_values: List[int]):
    """Analyze correlations between leading and trailing sides.

    For each (L, K) pair:
    1. Fractional part distribution: do B_K-survivors cluster in {n·α}?
    2. Residue class distribution: do A_L-survivors cluster in n mod u_K?
    3. Independence test: are leading and trailing independent?
    """
    filepath = f"verify_middle/bridge_data_K{K}.csv"
    sigs = load_signatures(filepath)

    print(f"\n=== K={K} ({len(sigs)} B_K survivors, u_K={u_k(K)}) ===")

    # Fractional part distribution
    fracs = [float(s['frac']) for s in sigs]
    print(f"  {{n·α}} range: [{min(fracs):.6f}, {max(fracs):.6f}]")
    print(f"  {{n·α}} mean: {sum(fracs)/len(fracs):.6f}")

    # For each L, check if survivors cluster
    for L in L_values:
        survivors = [s for s in sigs if s[f'survives_L{L}'] == 'True']
        nonsurvivors = [s for s in sigs if s[f'survives_L{L}'] == 'False']

        if survivors:
            surv_fracs = [float(s['frac']) for s in survivors]
            print(f"  L={L}: {len(survivors)} survive, {{n·α}} mean={sum(surv_fracs)/len(surv_fracs):.6f}, "
                  f"range=[{min(surv_fracs):.6f}, {max(surv_fracs):.6f}]")
        else:
            print(f"  L={L}: 0 survive")

    # Residue class analysis
    print(f"\n  Residue class distribution (n mod u_K):")
    from collections import Counter
    residues = Counter(s['n_mod_uk'] for s in sigs)
    print(f"  Unique residues: {len(residues)} / {u_k(K)}")
    print(f"  Top 5: {residues.most_common(5)}")
```

- [ ] **Step 2: Run correlation analysis**

Run: `python3 -c "from verify_middle.bridge_analysis import *; [analyze_correlations(K, [10, 20, 30, 40, 50, 60, 70]) for K in [5, 8, 10]]"`

Capture the output — this is the core analysis.

- [ ] **Step 3: Commit**

```bash
git add verify_middle/bridge_analysis.py
git commit -m "feat: bridge analysis — correlation analysis"
```

---

### Task 5: Findings Document and Bridge Conjecture

**Files:**
- Create: `verify_middle/BRIDGE_FINDINGS.md`

**Interfaces:**
- Consumes: all analysis from Tasks 1-4

- [ ] **Step 1: Write findings document**

Based on the analysis output, write `verify_middle/BRIDGE_FINDINGS.md` with:

1. **Data summary:** table of |B_K|, |A_L ∩ B_K| for each (K, L)
2. **Fractional part distribution:** do B_K-survivors cluster in {n·α}?
3. **Residue class distribution:** do A_L-survivors cluster in n mod u_K?
4. **Independence test:** are leading and trailing sides independent?
5. **Bridge conjecture:** a precise statement about the leading/trailing interaction
6. **Assessment:** can this become an infinite proof?

- [ ] **Step 2: Commit**

```bash
git add verify_middle/BRIDGE_FINDINGS.md
git commit -m "feat: bridge analysis — findings document and conjecture"
```
