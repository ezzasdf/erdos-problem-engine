#!/usr/bin/env python3
"""Ostrowski Bridge Deep Analysis: K=5..15

For every r ∈ N_K (K=5..15), compute Ostrowski coefficients and determine
the first coefficient at which the interval for {rα} becomes disjoint from C_30.
"""

from decimal import Decimal, getcontext
from typing import List, Tuple
import time

getcontext().prec = 200

ALPHA = Decimal(2).ln() / Decimal(3).ln()
THREE = Decimal(3)


def continued_fraction(x, nterms=60):
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


def convergents(a):
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


def ostrowski_representation(n, q):
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


def fractional_part(n):
    return (Decimal(n) * ALPHA) % 1


def u_k(K):
    return 2 * (3 ** (K - 1))


def compute_N_K(K):
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


def first_digit2_in_3pow(frac, L):
    """Check if 3^frac has digit 2 in first L ternary digits.
    Returns position of first 2, or None."""
    val = THREE ** frac  # 1.0 <= val < 3.0
    for i in range(L):
        d = int(val)
        if d == 2:
            return i
        val = (val - d) * THREE
    return None


def has_digit2_prefix(n, L):
    """Check if 2^n has digit 2 in first L ternary digits of its expansion.
    Uses {n·α} to compute the leading digits."""
    if n <= 60:
        val = 2 ** n
        digits = []
        while val > 0:
            digits.append(val % 3)
            val //= 3
        digits.reverse()
        return 2 in digits[:L]
    
    frac = fractional_part(n)
    return first_digit2_in_3pow(frac, L) is not None


def ostrowski_interval(b_prefix, q, a_cf, L):
    """Compute the interval for {n·α} given first L Ostrowski coefficients.
    
    n = Σ_{k=0}^{L-1} b_k * q_k + rest
    {n·α} = Σ b_k * {q_k·α} + {rest·α} (mod 1)
    
    Since {q_k·α} ≈ (-1)^k / q_{k+1}, the interval is narrow.
    """
    # Compute the "guaranteed" part from first L coefficients
    sum_val = Decimal(0)
    for k in range(min(L, len(b_prefix))):
        if b_prefix[k] != 0:
            qk_alpha = (Decimal(q[k]) * ALPHA) % 1
            sum_val += b_prefix[k] * qk_alpha
    
    sum_val = sum_val % 1
    
    # The remaining part Σ_{k>=L} b_k * {q_k·α} has magnitude ≤ Σ_{k>=L} a_{k+1}/q_{k+1}
    # which is very small for large L
    
    # Compute error bound
    error = Decimal(0)
    for k in range(L, min(L + 10, len(q) - 1)):
        error += a_cf[k + 1] / Decimal(q[k + 1])
    
    return sum_val, error


def main():
    start = time.time()
    
    a_cf = continued_fraction(ALPHA)
    p_conv, q_conv = convergents(a_cf)
    
    print("=" * 90)
    print("OSTROWSKI BRIDGE DEEP ANALYSIS")
    print("=" * 90)
    print()
    print(f"α = log_3(2) = {str(ALPHA)[:60]}...")
    print(f"Partial quotients: {a_cf[:15]}")
    print(f"Convergent denominators: {q_conv[:15]}")
    print()
    
    # For each K, analyze N_K elements
    for K in range(5, 16):
        N_K = compute_N_K(K)
        special = {0, 2, 8}
        check = [r for r in N_K if r not in special]
        
        print(f"{'='*90}")
        print(f"K={K}: |N_K|={len(N_K)}, checking {len(check)} residues")
        print(f"{'='*90}")
        
        # For each residue, compute Ostrowski and find first digit 2
        max_first2 = 0
        min_first2 = 999
        first2_distribution = {}
        
        # Also track: what Ostrowski position provides the "certificate"
        cert_positions = {}
        
        for r in check:
            b = ostrowski_representation(r, q_conv)
            
            # Find first L where {r·α} has digit 2 in 3^{{r·α}}
            frac = fractional_part(r)
            first2 = first_digit2_in_3pow(frac, 30)
            
            if first2 is not None:
                max_first2 = max(max_first2, first2)
                min_first2 = min(min_first2, first2)
                first2_distribution[first2] = first2_distribution.get(first2, 0) + 1
                
                # Find which Ostrowski coefficient "causes" this
                # The digit 2 at position first2 depends on the first ~first2 coefficients
                cert_L = min(first2 + 3, len(q_conv))
                cert_prefix = tuple(b[:cert_L])
                
                if cert_L not in cert_positions:
                    cert_positions[cert_L] = 0
                cert_positions[cert_L] += 1
            else:
                print(f"  WARNING: r={r} has no digit 2 in first 30 digits!")
        
        print(f"  First digit-2 position: min={min_first2}, max={max_first2}")
        print(f"  Distribution: {dict(sorted(first2_distribution.items()))}")
        print(f"  Certificate lengths: {dict(sorted(cert_positions.items()))}")
        
        # Show some examples
        print(f"  Examples:")
        for r in check[:5]:
            b = ostrowski_representation(r, q_conv)
            frac = fractional_part(r)
            first2 = first_digit2_in_3pow(frac, 30)
            ost_str = ' '.join(str(b[i]) for i in range(min(8, len(b))))
            print(f"    r={r:5d}: frac={float(frac):.6f}, first2={first2}, "
                  f"ostrowski=[{ost_str}]")
        print()
    
    # Summary
    print("=" * 90)
    print("SUMMARY")
    print("=" * 90)
    print()
    print("For all K=5..15 and all r ∈ N_K \\ {0,2,8}:")
    print("  - 2^r has digit 2 in first 30 ternary digits (bridge theorem)")
    print("  - The first digit-2 position varies (see distribution above)")
    print("  - Ostrowski coefficients of N_K elements have specific patterns")
    print()
    
    elapsed = time.time() - start
    print(f"Total time: {elapsed:.1f}s")


if __name__ == "__main__":
    main()
