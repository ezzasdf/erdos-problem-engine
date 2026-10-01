#!/usr/bin/env python3
"""
Verify the j>=38, K>=26 gap in no_births_after_K7.

For each (j, K) pair with j>=38, K>=26 and Q(j)+18 < uK(K),
check whether hasTrailingDigit2(2^(Q(j)+l) mod 3^K, K) = true
for all l in {0, ..., 18}.

If ALL mass-1 candidates have trailing digit 2, then no_births_after_K7
is vacuously true (no mass-1 elements exist in computeNK K for j>=38).

Also checks: for the problematic case where r >= uK(K-1), whether
there exists a DIFFERENT witness p in computeNK(K-1).
"""

import math

# Partial quotients of log_3(2) from log32_cf
log32_cf = [0, 1, 1, 1, 2, 2, 3, 1, 5, 2, 23, 2, 2, 1, 1, 55]

def Al32(k):
    if k < len(log32_cf):
        return max(1, log32_cf[k])
    return 1

def compute_Q(max_j):
    """Compute Q(j) for j=0..max_j using the recurrence."""
    Q = [0] * (max_j + 1)
    Q[0] = 1
    if max_j >= 1:
        Q[1] = 1
    for k in range(max_j - 1):
        j = k + 2
        Q[j] = Al32(j) * Q[j-1] + Q[j-2]
    return Q

def uK(K):
    return 2 * 3 ** (K - 1)

def has_trailing_digit_2(val, K):
    """Check if val has digit 2 in its last K ternary digits."""
    for i in range(K):
        if (val // (3 ** i)) % 3 == 2:
            return True
    return False

def pow2mod(exp, mod):
    """Compute 2^exp mod mod using fast modular exponentiation."""
    result = 1
    base = 2 % mod
    while exp > 0:
        if exp % 2 == 1:
            result = (result * base) % mod
        base = (base * base) % mod
        exp //= 2
    return result

def verify_gap():
    # Compute Q values up to j=80 (enough for K up to ~50)
    max_j = 80
    Q = compute_Q(max_j)
    
    print("=== Q values (j=35..50) ===")
    for j in range(35, min(51, max_j+1)):
        print(f"  Q({j}) = {Q[j]}")
    
    print(f"\nuK(25) = {uK(25)}")
    print(f"uK(26) = {uK(26)}")
    print(f"uK(27) = {uK(27)}")
    print()
    
    # For each K >= 26, find the range of j >= 38 where Q(j)+18 < uK(K)
    for K in range(26, 35):
        ukK = uK(K)
        ukKm1 = uK(K-1)
        
        # Find j range: j >= 38 and Q(j)+18 < uK(K)
        jmin = 38
        jmax = None
        for j in range(jmin, max_j+1):
            if Q[j] + 18 >= ukK:
                jmax = j - 1
                break
        if jmax is None:
            jmax = max_j
        
        if jmin > jmax:
            print(f"K={K}: No j>=38 with Q(j)+18 < uK({K})={ukK}")
            continue
        
        print(f"=== K={K}, uK({K})={ukK}, uK({K-1})={ukKm1} ===")
        print(f"  j range: [{jmin}, {jmax}]")
        
        # Check each (j, l) pair
        all_have_digit2 = True
        any_r_ge_ukKm1 = False
        count_no_digit2 = 0
        count_total = 0
        
        for j in range(jmin, jmax + 1):
            for l in range(19):
                r = Q[j] + l
                if r >= ukK:
                    continue
                count_total += 1
                
                modulus = 3 ** K
                val = pow2mod(r, modulus)
                htd = has_trailing_digit_2(val, K)
                
                if not htd:
                    all_have_digit2 = False
                    count_no_digit2 += 1
                    print(f"  ** NO digit 2: j={j}, l={l}, r={r}, 2^r mod 3^{K} = {val}")
                    # Show ternary digits
                    digits = []
                    v = val
                    for _ in range(K):
                        digits.append(v % 3)
                        v //= 3
                    print(f"     Ternary digits (LSB first): {digits}")
                
                if r >= ukKm1:
                    any_r_ge_ukKm1 = True
        
        if all_have_digit2:
            print(f"  ALL {count_total} candidates have digit 2. Gap is VACUOUSLY TRUE.")
        else:
            print(f"  {count_no_digit2}/{count_total} candidates MISSING digit 2.")
        
        if any_r_ge_ukKm1:
            print(f"  ** Some r >= uK(K-1)={ukKm1} -- witness p=r FAILS.")
        print()
    
    # Summary: for j>=38, what's the threshold K?
    print("\n=== Threshold analysis ===")
    for j in range(38, min(60, max_j+1)):
        for K in range(26, 40):
            if Q[j] + 18 < uK(K):
                r_ge = Q[j] + 18 >= uK(K-1) if K > 26 else False
                if r_ge:
                    print(f"  j={j}, K={K}: Q(j)+18={Q[j]+18} >= uK({K-1})={uK(K-1)} -- PROBLEMATIC (r may exceed uK(K-1))")
                break

if __name__ == "__main__":
    verify_gap()
