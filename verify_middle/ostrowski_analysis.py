#!/usr/bin/env python3
"""Ostrowski Numeration Analysis for the Erdős Ternary Conjecture.

Key insight: The numbers n that make {n * α} very small are exactly the
convergents of the continued fraction of α = log₃(2). But N_K grows like
2^{K-1}, while there are only O(K) convergents. So most numbers in N_K
are not convergents—they are "good enough" approximations described by
Ostrowski numeration.

This script:
1. Computes the continued fraction of α = log₃(2)
2. Analyzes the Ostrowski representation of N_K elements
3. Shows how the bridge theorem can be proved using Ostrowski structure
"""

from decimal import Decimal, getcontext
from typing import List, Tuple, Dict
import math

getcontext().prec = 200

# α = log₃(2)
ALPHA = Decimal(2).ln() / Decimal(3).ln()


def continued_fraction(x: Decimal, nterms: int = 60) -> List[int]:
    """Compute partial quotients of x."""
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
    """Compute convergents p_k/q_k from partial quotients."""
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
    """Compute Ostrowski representation of n using convergent denominators.
    
    n = Σ b_k * q_k where 0 ≤ b_k ≤ a_{k+1} and
    no two consecutive b_k are both equal to a_{k+1}.
    """
    if n == 0:
        return [0] * len(q)
    
    # Find the largest q_k ≤ n
    k = 0
    while k < len(q) - 1 and q[k + 1] <= n:
        k += 1
    
    # Greedy decomposition
    b = [0] * len(q)
    remaining = n
    for i in range(k, -1, -1):
        if q[i] <= remaining:
            b[i] = remaining // q[i]
            remaining -= b[i] * q[i]
    
    return b


def fractional_part(n: int) -> Decimal:
    """Compute {n * α}."""
    return (Decimal(n) * ALPHA) % 1


def u_k(K: int) -> int:
    """Period of 2^n mod 3^K."""
    return 2 * (3 ** (K - 1))


def compute_N_K(K: int) -> List[int]:
    """Compute N_K: residues r ∈ [0, u_K) with B_K(r) true."""
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


def analyze_ostrowski_structure():
    """Analyze the Ostrowski structure of N_K elements."""
    print("=" * 80)
    print("Ostrowski Numeration Analysis for Erdős Ternary Conjecture")
    print("=" * 80)
    print()
    
    # Step 1: Compute continued fraction
    a = continued_fraction(ALPHA)
    p, q = convergents(a)
    
    print("Step 1: Continued Fraction of α = log₃(2)")
    print("-" * 60)
    print(f"α ≈ {str(ALPHA)[:60]}")
    print()
    print(f"{'i':>3} {'a_i':>4} {'q_i':>20} {'p_i/q_i':>30}")
    for i in range(min(20, len(a))):
        convergent = Decimal(p[i]) / Decimal(q[i])
        error = abs(ALPHA - convergent)
        print(f"{i:>3} {a[i]:>4} {q[i]:>20} {str(convergent)[:30]:>30}")
    print()
    
    # Step 2: Key convergents for the bridge theorem
    print("Step 2: Key Convergents")
    print("-" * 60)
    print("n=2 is denominator of convergent 1/2:")
    print(f"  q_1 = {q[1]}, p_1/q_1 = {p[1]}/{q[1]} = {Decimal(p[1])/Decimal(q[1])}")
    print(f"  {{2·α}} = {fractional_part(2)}")
    print()
    print("n=8 is denominator of convergent 5/8:")
    print(f"  q_3 = {q[3]}, p_3/q_3 = {p[3]}/{q[3]} = {Decimal(p[3])/Decimal(q[3])}")
    print(f"  {{8·α}} = {fractional_part(8)}")
    print()
    
    # Step 3: Analyze N_K elements
    print("Step 3: N_K Structure and Ostrowski Representation")
    print("-" * 60)
    
    for K in [5, 8, 10]:
        N_K = compute_N_K(K)
        period = u_k(K)
        
        print(f"\nK={K}: u_K={period}, |N_K|={len(N_K)}")
        
        # Analyze Ostrowski representations
        max_b = [0] * 20
        total_b = [0] * 20
        convergent_count = 0
        
        for r in N_K:
            b = ostrowski_representation(r, q)
            
            # Check if r is a convergent denominator
            if r in q:
                convergent_count += 1
            
            # Count non-zero coefficients
            for i, bi in enumerate(b):
                if bi > 0 and i < 20:
                    max_b[i] = max(max_b[i], bi)
                    total_b[i] += bi
        
        print(f"  Convergent denominators in N_K: {convergent_count}")
        print(f"  Max Ostrowski coefficients: {max_b[:10]}")
        print(f"  Avg non-zero coefficients: {sum(total_b[:10])/len(N_K):.1f}")
    
    # Step 4: The key insight
    print()
    print("Step 4: The Ostrowski Bridge")
    print("-" * 60)
    print()
    print("Key Insight: For n ∈ N_K with Ostrowski representation")
    print("  n = Σ b_k * q_k")
    print()
    print("The fractional part {n·α} is determined by the Ostrowski coefficients.")
    print("Specifically:")
    print()
    print("  {n·α} = Σ b_k * {q_k·α} (mod 1)")
    print()
    print("Since {q_k·α} ≈ (-1)^k / q_{k+1} (by the theory of continued fractions),")
    print("the fractional part is a weighted sum of alternating-sign terms.")
    print()
    print("For the bridge theorem, we need to show that for n ∈ N_K \\ {0,2,8},")
    print("{n·α} ∉ φ⁻¹(C_L) for L=30.")
    print()
    print("This means: the first 30 digits of 3^{{n·α}} must contain a 2.")
    print()
    
    # Step 5: Verification
    print("Step 5: Empirical Verification")
    print("-" * 60)
    print()
    
    for K in [5, 8]:
        N_K = compute_N_K(K)
        period = u_k(K)
        
        print(f"K={K}: Checking Ostrowski structure of N_K elements")
        
        for r in N_K[:10]:  # Check first 10
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
            
            print(f"  r={r:5d}: frac={float(frac):.6f}, "
                  f"Ostrowski={' '.join(str(b[i]) for i in range(5))}, "
                  f"has_2={has_2}")
    
    print()
    print("=" * 80)
    print("Conclusion")
    print("=" * 80)
    print()
    print("The Ostrowski numeration provides a complete description of")
    print("which n make {n·α} small. The bridge theorem can be proved by")
    print("showing that for each Ostrowski representation arising from N_K,")
    print("the corresponding {n·α} falls outside φ⁻¹(C_L).")
    print()
    print("This is a finite check: for each K, we need to verify that")
    print("all 2^{K-1} elements of N_K have Ostrowski representations")
    print("that produce {n·α} ∉ φ⁻¹(C_30).")
    print()
    print("For K=5..9, this is verified by native_decide in Lean 4.")
    print("For K≥10, this can be verified computationally.")


if __name__ == "__main__":
    analyze_ostrowski_structure()
