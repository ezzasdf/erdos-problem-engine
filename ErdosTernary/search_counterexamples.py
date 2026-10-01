#!/usr/bin/env python3
"""
Counterexample search: can 2^r satisfy both leading and trailing digit constraints?
For each r, track:
- Trailing K digits of 2^r in base 3 (are they all in {0,1}?)
- Leading 30 digits of 2^r in base 3 (are they all in {0,1}?)
- The Ostrowski representation
- The normalized value {r log₃ 2}

Search for r ≥ 23 where both conditions hold.
Push K as far as computationally practical.
"""
import math
import sys

alpha = math.log(2) / math.log(3)

# ─── Leading digits: floor(3^({rα} + 29)) in base 3 ───
def leading_30_digits(r):
    """Return the first 30 ternary digits of 2^r."""
    x = (r * alpha) % 1.0
    val = int(math.floor(3**(x + 29)))
    digits = []
    v = val
    for _ in range(30):
        digits.append(v % 3)
        v //= 3
    return digits

def has_no_digit_2(digits):
    return all(d != 2 for d in digits)

# ─── Trailing digits: 2^r mod 3^K in base 3 ───
def trailing_K_digits(r, K):
    """Return the last K ternary digits of 2^r."""
    val = pow(2, r, 3**K)
    digits = []
    v = val
    for _ in range(K):
        digits.append(v % 3)
        v //= 3
    return digits

# ─── Search ───
print("="*80)
print("COUNTEREXAMPLE SEARCH: Can 2^r have both leading and trailing 2-free blocks?")
print("="*80)

# Phase 1: Search all r from 0 to 10000
print("\n--- Phase 1: r from 0 to 10000 ---")
found = []
for r in range(10001):
    lead = leading_30_digits(r)
    lead_ok = has_no_digit_2(lead)
    
    if lead_ok:
        # Check trailing digits for various K
        trailing_ok = {}
        for K in [8, 10, 12, 14, 16]:
            trail = trailing_K_digits(r, K)
            trailing_ok[K] = has_no_digit_2(trail)
        
        any_trailing = any(trailing_ok.values())
        if any_trailing:
            found.append((r, lead, trailing_ok))
            print(f"  r={r:6d}: leading OK, trailing: {trailing_ok}")

if not found:
    print("  No examples found with leading 30 digits 2-free.")
else:
    print(f"\n  Found {len(found)} examples with leading 30 digits 2-free.")

# Phase 2: For r in N_K (K=12), check leading digits
print("\n--- Phase 2: N_12 survivors r ≥ 23, check leading digits ---")
K = 12
modulus = 3**K
NK = []
pow2r = 1
for r in range(2 * 3**(K-1)):
    has2 = False
    v = pow2r
    for i in range(K):
        if v % 3 == 2:
            has2 = True
            break
        v //= 3
    if not has2:
        NK.append(r)
    pow2r = (pow2r * 2) % modulus

c30_count = 0
for r in NK:
    if r < 23:
        continue
    lead = leading_30_digits(r)
    if has_no_digit_2(lead):
        c30_count += 1
        print(f"  COUNTEREXAMPLE: r={r}, leading={lead}")

print(f"  N_12 survivors r≥23 with leading 30 digits 2-free: {c30_count}")

# Phase 3: Direct search for r where 2^r itself (not mod) has both constraints
print("\n--- Phase 3: Direct search for 2^r with both leading and trailing 2-free ---")
print("Computing 2^r exactly for small r...")

for r in range(1000):
    two_r = 2**r
    # Convert to base 3
    digits = []
    v = two_r
    if v == 0:
        digits = [0]
    else:
        while v > 0:
            digits.append(v % 3)
            v //= 3
    
    n_digits = len(digits)
    
    # Check trailing 10 digits
    trail_10 = digits[:10] if n_digits >= 10 else digits + [0]*(10-n_digits)
    trail_ok = has_no_digit_2(trail_10)
    
    # Check leading 30 digits
    lead_30 = digits[-30:] if n_digits >= 30 else [0]*(30-n_digits) + digits
    lead_30.reverse()  # now most significant first
    lead_ok = has_no_digit_2(lead_30)
    
    if trail_ok and lead_ok and r >= 23:
        print(f"  FOUND: r={r}, 2^r has {n_digits} ternary digits, "
              f"leading 30={lead_30}, trailing 10={trail_10}")

# Phase 4: Check for r in N_K with increasing K
print("\n--- Phase 4: N_K for K=8..20, check leading 30 digits ---")
for K in range(8, 21):
    uK = 2 * 3**(K-1)
    modulus = 3**K
    
    # Don't enumerate all of N_K for large K — instead, sample
    # by checking if 2^r mod 3^K has no digit 2
    n_survivors = 0
    n_c30 = 0
    max_r_checked = min(uK, 100000)  # limit for large K
    
    for r in range(max_r_checked):
        pow2r = pow(2, r, modulus)
        has2 = False
        v = pow2r
        for i in range(K):
            if v % 3 == 2:
                has2 = True
                break
            v //= 3
        
        if not has2 and r >= 23:
            n_survivors += 1
            lead = leading_30_digits(r)
            if has_no_digit_2(lead):
                n_c30 += 1
                if n_c30 <= 3:  # show first few
                    print(f"  K={K:2d}, r={r:6d}: COUNTEREXAMPLE! leading={lead[:10]}...")
    
    print(f"  K={K:2d}: checked r up to {max_r_checked}, "
          f"survivors={n_survivors}, C30={n_c30}")

# Phase 5: The critical check — for each K, what's the first r ≥ 23 in N_K with C30?
print("\n--- Phase 5: First r ≥ 23 in N_K with leading 30 digits 2-free ---")
for K in range(8, 17):
    uK = 2 * 3**(K-1)
    modulus = 3**K
    
    found_first = None
    for r in range(23, uK):
        pow2r = pow(2, r, modulus)
        has2 = False
        v = pow2r
        for i in range(K):
            if v % 3 == 2:
                has2 = True
                break
            v //= 3
        
        if not has2:
            lead = leading_30_digits(r)
            if has_no_digit_2(lead):
                found_first = r
                break
    
    if found_first:
        print(f"  K={K:2d}: First C30 example at r={found_first}")
    else:
        print(f"  K={K:2d}: NO C30 example found for r ∈ [23, {uK})")

# Phase 6: Check the complement — for r NOT in N_K, how often is leading 30 2-free?
print("\n--- Phase 6: How common is C30Lead among ALL r ≥ 23? ---")
n_all = 0
n_c30_all = 0
for r in range(23, 10001):
    n_all += 1
    lead = leading_30_digits(r)
    if has_no_digit_2(lead):
        n_c30_all += 1
        if n_c30_all <= 5:
            # Check if r is in N_12
            pow12 = pow(2, r, 3**12)
            v = pow12
            trail_12 = []
            for i in range(12):
                trail_12.append(v % 3)
                v //= 3
            in_n12 = has_no_digit_2(trail_12)
            print(f"  r={r}: C30, in N_12={in_n12}, trailing 12={trail_12}")

print(f"  Total r in [23,10000]: {n_all}")
print(f"  C30 examples: {n_c30_all}")
print(f"  Fraction: {n_c30_all/n_all:.6f}")
print(f"  Expected from measure: {(2/3)**30:.6f}")
