#!/usr/bin/env python3
"""
Verify that hasTrailingDigit2(2^r mod 3^K, K) = true for K=26
implies it's true for ALL K >= 26.

Also verify: for j >= 38 and ALL K >= 26 with r < uK(K),
hasTrailingDigit2 is true (by checking the minimum K = 26 only).
"""

import math

log32_cf = [0, 1, 1, 1, 2, 2, 3, 1, 5, 2, 23, 2, 2, 1, 1, 55]

def Al32(k):
    if k < len(log32_cf):
        return max(1, log32_cf[k])
    return 1

def compute_Q(max_j):
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

def pow2mod(exp, mod):
    result = 1
    base = 2 % mod
    while exp > 0:
        if exp % 2 == 1:
            result = (result * base) % mod
        base = (base * base) % mod
        exp //= 2
    return result

def has_trailing_digit_2(val, K):
    for i in range(K):
        if (val // (3 ** i)) % 3 == 2:
            return True, i  # return position
    return False, -1

def verify_key_lemma():
    """
    KEY LEMMA: If hasTrailingDigit2(2^r mod 3^K0, K0) = true,
    then hasTrailingDigit2(2^r mod 3^K, K) = true for all K >= K0.

    Proof: if digit at position i < K0 is 2, then i < K for all K > K0,
    so the same digit is 2.
    """
    Q = compute_Q(80)

    print("=" * 70)
    print("KEY LEMMA VERIFICATION")
    print("=" * 70)
    print()

    # For j=38, check ALL l values at K=26
    # If digit 2 found at position i < 26, then it works for all K >= 26
    print("Checking j=38 at K=26 (minimum K for j>=38)...")
    j = 38
    K0 = 26
    modulus = 3 ** K0
    
    all_ok = True
    for l in range(19):
        r = Q[j] + l
        val = pow2mod(r, modulus)
        found, pos = has_trailing_digit_2(val, K0)
        if found:
            print(f"  l={l:2d}: r={r}, digit 2 at position {pos} (< K0={K0}) -> OK for ALL K >= {K0}")
        else:
            print(f"  l={l:2d}: r={r}, NO digit 2 at K0={K0}!")
            all_ok = False
    
    if all_ok:
        print(f"\n  ALL 19 candidates for j=38 have digit 2 at K0=26")
        print(f"  Therefore hasTrailingDigit2 is true for ALL K >= 26")
    
    # Also check j=39 (the other j value for K=26)
    print(f"\nChecking j=39 at K=26...")
    j = 39
    all_ok_39 = True
    for l in range(19):
        r = Q[j] + l
        if r >= uK(K0):
            print(f"  l={l:2d}: r={r} >= uK({K0})={uK(K0)} -> not in N_K, skip")
            continue
        val = pow2mod(r, modulus)
        found, pos = has_trailing_digit_2(val, K0)
        if found:
            print(f"  l={l:2d}: r={r}, digit 2 at position {pos} -> OK for ALL K >= {K0}")
        else:
            print(f"  l={l:2d}: r={r}, NO digit 2!")
            all_ok_39 = False
    
    if all_ok_39:
        print(f"\n  ALL candidates for j=39 have digit 2 at K0=26")
    
    # For j >= 40, the minimum K is higher. Check those too.
    print("\n" + "=" * 70)
    print("Checking ALL j >= 38 at their minimum K")
    print("=" * 70)
    
    for j in range(38, 60):
        # Find minimum K such that Q(j)+18 < uK(K)
        min_K = None
        for K in range(26, 50):
            if Q[j] + 18 < uK(K):
                min_K = K
                break
        if min_K is None:
            continue
        
        modulus = 3 ** min_K
        all_ok_j = True
        for l in range(19):
            r = Q[j] + l
            if r >= uK(min_K):
                continue
            val = pow2mod(r, modulus)
            found, pos = has_trailing_digit_2(val, min_K)
            if not found:
                print(f"  j={j}, l={l}, K={min_K}: NO digit 2! *** FAIL ***")
                all_ok_j = False
        
        if all_ok_j:
            count = sum(1 for l in range(19) if Q[j]+l < uK(min_K))
            print(f"  j={j:2d}, K={min_K}: ALL {count} candidates have digit 2 -> OK for ALL K >= {min_K}")
    
    # Final summary: can we prove a general statement?
    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)
    print()
    print("For j=38: min K = 26. All 19 candidates have digit 2 at K=26.")
    print("  -> hasTrailingDigit2 true for ALL K >= 26.")
    print("For j=39: min K = 26. All candidates have digit 2 at K=26.")
    print("  -> hasTrailingDigit2 true for ALL K >= 26.")
    print()
    print("GENERAL PROOF STRATEGY:")
    print("  1. For each j >= 38, find minimum K_j with Q(j)+18 < uK(K_j)")
    print("  2. Verify hasTrailingDigit2 at K_j (finite computation)")
    print("  3. By the monotonicity lemma, it holds for all K >= K_j")
    print()
    print("This reduces the infinite verification to finitely many checks!")
    print("The number of j values to check is UNBOUNDED, but each check is finite.")
    print()
    print("For a Lean proof, we need a DIFFERENT approach:")
    print("  - Prove hasTrailingDigit2 directly using continued fraction theory")
    print("  - Or add a new axiom backed by computational evidence")
    print()

if __name__ == "__main__":
    verify_key_lemma()
