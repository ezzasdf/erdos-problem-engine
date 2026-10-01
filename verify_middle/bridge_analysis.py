#!/usr/bin/env python3
"""Phase 12: Leading/Trailing Orbit Intersection — Bridge Theorem Analysis.

Collects per-candidate signatures for A_L ∩ B_K survivors and searches
for correlations between leading and trailing ternary digits of 2^n.
"""

import csv
import math
from decimal import Decimal, getcontext
from typing import List, Tuple, Set, Dict


# --- Constants ---

# Use Decimal for high-precision leading-digit extraction
getcontext().prec = 200  # 200 decimal digits — sufficient for L <= 70

ALPHA = Decimal(2).ln() / Decimal(3).ln()  # log_3(2) as Decimal


def u_k(k: int) -> int:
    """Period of 2^n mod 3^k: u_k = 2 * 3^(k-1)."""
    return 2 * (3 ** (k - 1))


def fractional_part(n: int) -> Decimal:
    """Compute {n * alpha} using Decimal arithmetic."""
    return (Decimal(n) * ALPHA) % 1


def leading_prefix(n: int, L: int) -> str:
    """Compute the first L ternary digits of 2^n.

    Uses the identity: the first L ternary digits of 2^n are the first L
    digits of 3^{{n * alpha}} in base 3.

    Returns a string of '0', '1', '2'.
    """
    # For small n, compute 2^n directly (fast, exact)
    if n <= 60:
        val = 2 ** n
        digits = []
        while val > 0:
            digits.append(str(val % 3))
            val //= 3
        base3 = ''.join(reversed(digits))
        return base3[:L]

    # For large n, use 3^frac with high precision
    getcontext().prec = 400
    frac = fractional_part(n)
    three = Decimal(3)
    val = three ** frac  # 1.0 <= val < 3.0
    d0 = int(val)
    if d0 >= 3:
        d0 = 2
    val -= d0
    digits = [str(d0)]
    for _ in range(L - 1):
        val *= three
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


def collect_signatures(K: int, L_values: List[int]) -> List[dict]:
    """Collect signatures for all n in A_L ∩ B_K.

    For each n in [0, u_K):
    1. Check B_K(n): trailing K digits of 2^n avoid digit 2
    2. For each L in L_values, check A_L(n): first L digits avoid digit 2
    3. Record signature for survivors

    Returns list of dicts with keys:
    n, n_mod_uk, frac, trailing_suffix, leading_prefixes, survives_leading
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


if __name__ == "__main__":
    import sys

    if len(sys.argv) > 1 and sys.argv[1] == '--analyze':
        # Correlation analysis mode
        from collections import Counter

        L_VALUES = [10, 20, 30, 40, 50, 60, 70]

        for K in [5, 8, 10, 12, 15]:
            filepath = f"verify_middle/bridge_data_K{K}.csv"
            with open(filepath, 'r') as f:
                reader = csv.DictReader(f)
                sigs = list(reader)

            period = u_k(K)
            print(f"\n=== K={K} ({len(sigs)} B_K survivors, u_K={period}) ===")

            # Fractional part distribution
            fracs = [float(s['frac']) for s in sigs]
            print(f"  {{n·α}} range: [{min(fracs):.6f}, {max(fracs):.6f}]")
            print(f"  {{n·α}} mean: {sum(fracs)/len(fracs):.6f}")

            # For each L, check if survivors cluster
            for L in L_VALUES:
                survivors = [s for s in sigs if s[f'survives_L{L}'] == 'True']
                nonsurvivors = [s for s in sigs if s[f'survives_L{L}'] == 'False']

                if survivors:
                    surv_fracs = [float(s['frac']) for s in survivors]
                    print(f"  L={L}: {len(survivors):3d} survive, "
                          f"{{n·α}} mean={sum(surv_fracs)/len(surv_fracs):.6f}, "
                          f"range=[{min(surv_fracs):.6f}, {max(surv_fracs):.6f}]")
                else:
                    print(f"  L={L}: 0 survive")

            # Residue class analysis
            print(f"\n  Residue class distribution (n mod u_K):")
            residues = Counter(s['n_mod_uk'] for s in sigs)
            print(f"  Unique residues: {len(residues)} / {period}")

            # Check if survivors cluster in specific residues
            for L in [10, 20, 70]:
                survivors = [s for s in sigs if s[f'survives_L{L}'] == 'True']
                if survivors:
                    surv_residues = Counter(s['n_mod_uk'] for s in survivors)
                    print(f"  L={L} survivors: residues = {dict(surv_residues.most_common(10))}")

            # Independence test: does knowing B_K change the distribution of {n·α}?
            print(f"\n  Independence analysis:")
            all_fracs = [float(s['frac']) for s in sigs]
            for L in [10, 20, 70]:
                survivors = [s for s in sigs if s[f'survives_L{L}'] == 'True']
                nonsurvivors = [s for s in sigs if s[f'survives_L{L}'] == 'False']
                if survivors and nonsurvivors:
                    surv_mean = sum(float(s['frac']) for s in survivors) / len(survivors)
                    nonsurv_mean = sum(float(s['frac']) for s in nonsurvivors) / len(nonsurvivors)
                    print(f"  L={L}: survivors mean frac={surv_mean:.6f}, "
                          f"nonsurvivors mean frac={nonsurv_mean:.6f}, "
                          f"diff={abs(surv_mean - nonsurv_mean):.6f}")

    else:
        # Data collection mode
        L_VALUES = [10, 20, 30, 40, 50, 60, 70]

        for K in [5, 8, 10, 12, 15]:
            print(f"Collecting signatures for K={K} (u_K={u_k(K)})...")
            sigs = collect_signatures(K, L_VALUES)
            print(f"  B_K survivors: {len(sigs)}")

            for L in L_VALUES:
                count = sum(1 for s in sigs if s['survives_leading'][L])
                print(f"  A_L ∩ B_K (L={L}): {count}")

            filepath = f"verify_middle/bridge_data_K{K}.csv"
            export_csv(sigs, L_VALUES, filepath)
            print(f"  Exported to {filepath}")
            print()
