#!/usr/bin/env python3
"""Bridge Theorem: Induction Check for K=12.

Verifies the first-period result for K=12:
For each r ∈ N_12 \ {0,2,8}, and the two surviving i values from Saye's Lemma,
verify that {r·α + i·u_12·α} ∉ φ⁻¹(C_30).

This is the heart of the Erdős conjecture proof for K=12.
"""

import math
from decimal import Decimal, getcontext
from typing import List, Tuple, Set


# High-precision arithmetic
getcontext().prec = 200

# α = log_3(2)
ALPHA = Decimal(2).ln() / Decimal(3).ln()


def u_k(k: int) -> int:
    """Period of 2^n mod 3^k: u_k = 2 * 3^(k-1)."""
    return 2 * (3 ** (k - 1))


def d1(j: int) -> int:
    """d_1(2^j) = 1 if j even, 2 if j odd."""
    return 1 if j % 2 == 0 else 2


def ternary_digit(val: int, k: int) -> int:
    """k-th ternary digit of val (1-indexed from least significant)."""
    return (val // (3 ** (k - 1))) % 3


def compute_N_K(K: int) -> List[int]:
    """Compute N_K: residues r ∈ [0, u_K) with B_K(r) true.
    
    B_K(r) means 2^r mod 3^K has no digit 2 in base 3.
    """
    period = u_k(K)
    modulus = 3 ** K
    N_K = []
    
    pow2_mod = 1  # 2^0 mod 3^K
    for r in range(period):
        # Check if 2^r mod 3^K has no digit 2
        val = pow2_mod
        has_digit_2 = False
        while val > 0:
            if val % 3 == 2:
                has_digit_2 = True
                break
            val //= 3
        
        if not has_digit_2:
            N_K.append(r)
        
        # Update: 2^(r+1) mod 3^K = (2^r * 2) mod 3^K
        pow2_mod = (pow2_mod * 2) % modulus
    
    return N_K


def compute_surviving_i(r: int, K: int) -> List[int]:
    """Compute the two surviving i values for residue r at level K.
    
    By Saye's Lemma, the (K+1)-st digit of 2^{r + i·u_K} is:
        d_{K+1}(2^{r + i·u_K}) ≡ d_{K+1}(2^r) + i·d_1(2^r) (mod 3)
    
    For the digit to not be 2, we need i such that the result ≠ 2.
    Since d_1(2^r) ∈ {1,2}, the map i ↦ (base + i·d) % 3 is a permutation,
    so exactly one i gives digit 2, and the other two survive.
    """
    period = u_k(K)
    modulus = 3 ** K
    
    # Compute 2^r mod 3^(K+1) to get d_{K+1}(2^r)
    pow2_r = pow(2, r, 3 ** (K + 1))
    base_digit = (pow2_r // (3 ** K)) % 3  # d_{K+1}(2^r)
    
    d = d1(r)  # d_1(2^r)
    
    # Find which i gives digit 2
    bad_i = None
    for i in range(3):
        if (base_digit + i * d) % 3 == 2:
            bad_i = i
            break
    
    # The two surviving i values
    surviving = [i for i in range(3) if i != bad_i]
    return surviving


def fractional_part_decimal(n: int) -> Decimal:
    """Compute {n * alpha} using Decimal arithmetic."""
    return (Decimal(n) * ALPHA) % 1


def has_digit_2_in_prefix(n: int, L: int) -> bool:
    """Check if the first L ternary digits of 2^n contain a 2.
    
    Uses 3^{{n·α}} with high precision.
    """
    if n <= 60:
        # For small n, compute directly
        val = 2 ** n
        digits = []
        while val > 0:
            digits.append(str(val % 3))
            val //= 3
        base3 = ''.join(reversed(digits))
        return '2' in base3[:L]
    
    # For large n, use 3^frac
    getcontext().prec = 400
    frac = fractional_part_decimal(n)
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
    
    return '2' in ''.join(digits)


def verify_induction_step(K: int, L: int) -> Tuple[bool, List[Tuple[int, int, str]]]:
    """Verify the induction step for level K.
    
    For each r ∈ N_K \ {0,2,8}, and the two surviving i values,
    verify that {r·α + i·u_K·α} ∉ φ⁻¹(C_L).
    
    Returns (success, failures) where failures is a list of (r, i, reason).
    """
    period = u_k(K)
    N_K = compute_N_K(K)
    
    print(f"K={K}: u_K={period}, |N_K|={len(N_K)}")
    print(f"  N_K contains {len(N_K)} residues")
    
    # Filter out 0, 2, 8
    special = {0, 2, 8}
    check_residues = [r for r in N_K if r not in special]
    
    print(f"  Checking {len(check_residues)} residues (excluding 0, 2, 8)")
    
    failures = []
    checked = 0
    
    for r in check_residues:
        surviving_i = compute_surviving_i(r, K)
        
        for i in surviving_i:
            n = r + i * period
            
            # Check if A_L(n) holds
            if not has_digit_2_in_prefix(n, L):
                # This is a failure — the bridge theorem would be violated
                failures.append((r, i, f"n={n} has no digit 2 in first {L} digits"))
            
            checked += 1
    
    success = len(failures) == 0
    print(f"  Checked {checked} (r, i) pairs")
    print(f"  Failures: {len(failures)}")
    
    if failures:
        for r, i, reason in failures[:10]:  # Show first 10
            print(f"    r={r}, i={i}: {reason}")
        if len(failures) > 10:
            print(f"    ... and {len(failures) - 10} more")
    
    return success, failures


def main():
    """Run the induction check for K=12,15, L=30."""
    print("=" * 60)
    print("Bridge Theorem: Induction Check")
    print("=" * 60)
    print()
    
    L = 30
    all_pass = True
    
    for K in [12, 15]:
        print(f"--- K={K} ---")
        success, failures = verify_induction_step(K, L)
        print()
        if success:
            print(f"PASS: For K={K}, L={L}, no extra survivors in first period.")
        else:
            print(f"FAIL: For K={K}, L={L}, found {len(failures)} extra survivors.")
            all_pass = False
        print()
    
    print("=" * 60)
    if all_pass:
        print("ALL PASS: Bridge theorem confirmed for first period [0, u_K)")
        print("at K=12,15 with L=30.")
    else:
        print("SOME FAILURES: Bridge theorem violated.")
    print("=" * 60)


if __name__ == "__main__":
    main()
