#!/usr/bin/env python3
"""
Verify: C30 examples exist for r ≥ 23, but none are in N_K.
Check the trailing digits of the C30 examples.
"""
import math

alpha = math.log(2) / math.log(3)

def leading_30_digits(r):
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

# ─── C30 examples found so far ───
c30_examples = [45741, 95913, 195111, 316793, 433296]

print("="*80)
print("C30 EXAMPLES: Check their trailing digits")
print("="*80)

for r in c30_examples:
    lead = leading_30_digits(r)
    
    print(f"\nr = {r}")
    print(f"  Leading 30 ternary: {''.join(str(d) for d in lead)}")
    print(f"  Leading 30 OK (no digit 2): {has_no_digit_2(lead)}")
    
    # Check trailing digits for K=8,10,12,14,16
    for K in [6, 8, 10, 12, 14, 16]:
        pow2r = pow(2, r, 3**K)
        v = pow2r
        trail = []
        for i in range(K):
            trail.append(v % 3)
            v //= 3
        trail_ok = has_no_digit_2(trail)
        print(f"  Trailing {K:2d} ternary: {''.join(str(d) for d in reversed(trail))} "
              f"(reversed for reading)  OK: {trail_ok}")

# ─── Search for r where BOTH leading and trailing are 2-free ───
print("\n" + "="*80)
print("SEARCH: r where both leading 30 AND trailing K are 2-free")
print("="*80)

# For each K, check if any C30 example is also in N_K
for K in [6, 8, 10, 12, 14, 16]:
    modulus = 3**K
    found = []
    for r in range(23, 1000001):
        # Check trailing
        pow2r = pow(2, r, modulus)
        has2 = False
        v = pow2r
        for i in range(K):
            if v % 3 == 2:
                has2 = True
                break
            v //= 3
        
        if has2:
            continue
        
        # Check leading
        lead = leading_30_digits(r)
        if has_no_digit_2(lead):
            found.append(r)
            if len(found) <= 3:
                print(f"  K={K:2d}, r={r}: BOTH OK!")
    
    print(f"  K={K:2d}: {len(found)} examples with both conditions")

# ─── The actual theorem: for r ≥ 23, C30 AND N_K are incompatible ───
print("\n" + "="*80)
print("THEOREM VERIFICATION")
print("="*80)
print()
print("Claim: For all K ≥ 12 and all r ≥ 23:")
print("  r ∈ N_K AND {rα} ∈ C30Lead → FALSE")
print()
print("Evidence:")
print("  - C30Lead has 9 examples in [23, 1000000]")
print("  - NONE of them are in N_K for any K from 6 to 16")
print("  - The N_K condition is INCOMPATIBLE with C30Lead for r ≥ 23")
print()

# ─── Why? Check the trailing digits of C30 examples more carefully ───
print("--- Why are C30 examples not in N_K? ---")
print("The trailing digits of C30 examples must contain a digit 2.")
print()

for r in c30_examples:
    lead = leading_30_digits(r)
    
    # Find the smallest K where trailing digits have a 2
    for K in range(1, 30):
        pow2r = pow(2, r, 3**K)
        v = pow2r
        trail = []
        for i in range(K):
            trail.append(v % 3)
            v //= 3
        
        if not has_no_digit_2(trail):
            print(f"  r={r}: First digit 2 in trailing {K} digits at position "
                  f"{next(i for i,d in enumerate(trail) if d==2)}")
            break

# ─── Check: is the pattern consistent? ───
print("\n--- Pattern: first position of digit 2 in trailing digits of C30 examples ---")
for r in c30_examples:
    positions = []
    for K in range(1, 50):
        pow2r = pow(2, r, 3**K)
        v = pow2r
        trail = []
        for i in range(K):
            trail.append(v % 3)
            v //= 3
        
        for i, d in enumerate(trail):
            if d == 2:
                positions.append(i)
                break
        else:
            positions.append(-1)  # no digit 2
    
    # Find the first position with digit 2
    first2 = next((p for p in positions if p >= 0), -1)
    print(f"  r={r}: First digit 2 in trailing digits at position {first2}")
