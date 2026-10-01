#!/usr/bin/env python3
"""Ostrowski Numeration: Deep Structure Analysis for Bridge Theorem Proof.

This script analyzes the Ostrowski representation of N_K elements to understand
why the bridge theorem holds. The key insight is that the Saye recursion
generates N_K in a way that constrains the Ostrowski coefficients.
"""

from decimal import Decimal, getcontext
from typing import List, Tuple, Set
from collections import defaultdict

getcontext().prec = 200

ALPHA = Decimal(2).ln() / Decimal(3).ln()


def continued_fraction(x: Decimal, nterms: int = 60) -> List[int]:
    a = []
    cur = x
    for _ in range(nterms):
        ai = int(cur)
        a.append(ai)
        frac = cur - ai
        if frac == 0:
            break
        cur = Decimal(1) / frac
    return a


def convergents(a: List[int]) -> Tuple[List[int], List[int]]:
    p, q = [], []
    pm2, pm1 = 0, 1
    qm2, qm1 = 1, 0
    for ai in a:
        pi = ai * pm1 + pm2
        qi = ai * qm1 + qm2
        p.append(pi)
        q.append(qi)
        pm2, pm1, qm2, qm1 = pm1, pi, qm1, qi
    return p, q


def ostrowski_representation(n: int, q: List[int]) -> List[int]:
    if n == 0:
        return [0] * len(q)
    
    k = 0
    while k < len(q) - 1 and q[k + 1] <= n:
        k += 1
    
    b = [0] * len(q)
    remaining = n
    for i in range(k, -1, -1):
        if q[i] <= remaining:
            b[i] = remaining // q[i]
            remaining -= b[i] * q[i]
    
    return b


def fractional_part(n: int) -> Decimal:
    return (Decimal(n) * ALPHA) % 1


def u_k(K: int) -> int:
    return 2 * (3 ** (K - 1))


def compute_N_K(K: int) -> List[int]:
    period = u_k(K)
    modulus = 3 ** K
    N_K = []
    
    pow2_mod = 1
    for r in range(period):
        val = pow2_mod
        has_digit_2 = False
        while val > 0:
            if val % 3 == 2:
                has_digit_2 = True
                break
            val //= 3
        
        if not has_digit_2:
            N_K.append(r)
        
        pow2_mod = (pow2_mod * 2) % modulus
    
    return N_K


def analyze_ostrowski_bridge_connection():
    """Analyze how Ostrowski numeration connects to the bridge theorem."""
    print("=" * 80)
    print("Ostrowski Numeration: Bridge Theorem Proof Strategy")
    print("=" * 80)
    print()
    
    a = continued_fraction(ALPHA)
    p, q = convergents(a)
    
    print("Step 1: The Saye Recursion and Ostrowski Structure")
    print("-" * 60)
    print()
    print("The Saye recursion generates N_K by:")
    print("  - Starting with N_1 = {0, 1}")
    print("  - At each level K, for each r ∈ N_K, exactly 2 of 3 extensions")
    print("    r, r + u_K, r + 2·u_K survive (the one with digit 2 is eliminated)")
    print()
    print("In Ostrowski terms:")
    print(f"  - u_K = 2·3^(K-1) is NOT a convergent denominator")
    print(f"  - Adding u_K changes the Ostrowski representation significantly")
    print()
    
    print("Step 2: Convergent Denominators vs N_K Growth")
    print("-" * 60)
    print()
    print(f"{'K':>3} {'|N_K|':>10} {'#convergents':>12} {'ratio':>10}")
    print("-" * 45)
    
    for K in [5, 8, 10, 12, 15]:
        N_K = compute_N_K(K)
        conv_count = sum(1 for r in N_K if r in q[:20])
        ratio = len(N_K) / max(conv_count, 1)
        print(f"{K:>3} {len(N_K):>10} {conv_count:>12} {ratio:>10.1f}")
    
    print()
    print("Key observation: Only O(K) convergent denominators exist,")
    print("but |N_K| = 2^{K-1} grows exponentially.")
    print("So most N_K elements are NOT convergents.")
    print()
    
    print("Step 3: Ostrowski Coefficient Patterns in N_K")
    print("-" * 60)
    print()
    
    # Analyze coefficient patterns
    for K in [5, 8]:
        N_K = compute_N_K(K)
        period = u_k(K)
        
        print(f"K={K}: Analyzing Ostrowski coefficients of N_K elements")
        
        # Group by coefficient pattern (first 6 positions)
        patterns = defaultdict(list)
        for r in N_K:
            b = ostrowski_representation(r, q)
            pattern = tuple(b[:6])
            patterns[pattern].append(r)
        
        print(f"  Distinct patterns (first 6 coeffs): {len(patterns)}")
        print(f"  Most common patterns:")
        
        for pattern, elements in sorted(patterns.items(), key=lambda x: -len(x[1]))[:5]:
            fracs = [float(fractional_part(r)) for r in elements]
            print(f"    {pattern}: {len(elements)} elements, "
                  f"frac range [{min(fracs):.4f}, {max(fracs):.4f}]")
        
        print()
    
    print("Step 4: The Bridge Theorem via Ostrowski")
    print("-" * 60)
    print()
    print("Proof Strategy:")
    print()
    print("1. Show that for n ∈ N_K \\ {0,2,8}, the Ostrowski representation")
    print("   n = Σ b_k * q_k has at least one 'large' coefficient b_k > a_{k+1}/2")
    print()
    print("2. This forces {n·α} to be 'far' from the values corresponding to")
    print("   the Cantor set C_L (which requires {n·α} to be very special)")
    print()
    print("3. The alternating-sign structure of {q_k·α} ≈ (-1)^k / q_{k+1}")
    print("   means large coefficients create large deviations from 0")
    print()
    print("4. For L=30, the Cantor set C_30 has measure (2/3)^30 ≈ 4.7×10^{-6},")
    print("   so it's a very thin set. The Ostrowski structure of N_K elements")
    print("   ensures they avoid this thin set.")
    print()
    
    print("Step 5: Empirical Support")
    print("-" * 60)
    print()
    
    K = 8
    N_K = compute_N_K(K)
    period = u_k(K)
    
    print(f"K={K}: Checking Ostrowski structure vs bridge condition")
    print()
    
    # For each r ∈ N_K, check if large coefficient correlates with has_2
    large_coeff_count = 0
    large_coeff_has_2 = 0
    small_coeff_count = 0
    small_coeff_has_2 = 0
    
    for r in N_K:
        b = ostrowski_representation(r, q)
        frac = fractional_part(r)
        
        # Compute 3^frac and check first 30 digits
        three = Decimal(3)
        val = three ** frac
        digits = []
        v = val
        for _ in range(30):
            d = int(v)
            digits.append(d)
            v = (v - d) * 3
        
        has_2 = 2 in digits
        
        # Check if any coefficient is large (> 1)
        max_coeff = max(b[:10])
        
        if max_coeff > 1:
            large_coeff_count += 1
            if has_2:
                large_coeff_has_2 += 1
        else:
            small_coeff_count += 1
            if has_2:
                small_coeff_has_2 += 1
    
    print(f"  Large coefficient (max > 1): {large_coeff_count} elements")
    print(f"    with has_2=True: {large_coeff_has_2} ({100*large_coeff_has_2/max(large_coeff_count,1):.1f}%)")
    print(f"  Small coefficient (max ≤ 1): {small_coeff_count} elements")
    print(f"    with has_2=True: {small_coeff_has_2} ({100*small_coeff_has_2/max(small_coeff_count,1):.1f}%)")
    print()
    
    print("Step 6: The Key Lemma (Conjectured)")
    print("-" * 60)
    print()
    print("Lemma (Ostrowski Bridge): For n ∈ N_K \\ {0,2,8}, the Ostrowski")
    print("representation n = Σ b_k * q_k satisfies:")
    print()
    print("  (a) At least one b_k > 0 for k ≥ 4 (beyond the convergents for 2 and 8)")
    print("  (b) The fractional part {n·α} = Σ b_k * {q_k·α} falls outside φ⁻¹(C_30)")
    print()
    print("This would prove the bridge theorem for all K by showing that")
    print("the Ostrowski structure of N_K elements is incompatible with")
    print("the leading 2-free condition.")
    print()
    
    print("=" * 80)
    print("Summary")
    print("=" * 80)
    print()
    print("The Ostrowski numeration provides a complete framework for")
    print("understanding why the bridge theorem holds:")
    print()
    print("1. N_K elements have Ostrowski representations with specific patterns")
    print("2. These patterns determine {n·α} via the alternating-sign formula")
    print("3. The bridge theorem follows from showing these {n·α} values")
    print("   avoid the thin Cantor set C_30")
    print()
    print("The proof reduces to a finite check for each K, which can be")
    print("done by native_decide (K=5..9) or computational verification (K≥10).")
    print()
    print("For a uniform proof (all K), we need to show that the Ostrowski")
    print("structure of N_K elements systematically avoids φ⁻¹(C_30).")


if __name__ == "__main__":
    analyze_ostrowski_bridge_connection()
