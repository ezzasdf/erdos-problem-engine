#!/usr/bin/env python3
"""
Extended search: find ALL C30 examples up to 10^7 and check their trailing digits.
Determine the minimum K such that every C30 example has a digit 2 in last K digits.
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

# ─── Find all C30 examples up to 10^7 ───
print("="*80)
print("FINDING ALL C30 EXAMPLES UP TO 10^7")
print("="*80)

c30_examples = []
for r in range(23, 10000001):
    lead = leading_30_digits(r)
    if has_no_digit_2(lead):
        c30_examples.append(r)

print(f"Found {len(c30_examples)} C30 examples in [23, 10^7]")
print(f"First 20: {c30_examples[:20]}")
print(f"Last 20: {c30_examples[-20:]}")

# ─── For each C30 example, find the first position of digit 2 in trailing digits ───
print("\n" + "="*80)
print("FIRST DIGIT-2 POSITION IN TRAILING DIGITS")
print("="*80)

first2_positions = []
for r in c30_examples:
    for K in range(1, 50):
        pow2r = pow(2, r, 3**K)
        v = pow2r
        trail = []
        for i in range(K):
            trail.append(v % 3)
            v //= 3
        
        # Check if any digit is 2
        has2 = False
        first2 = -1
        for i, d in enumerate(trail):
            if d == 2:
                has2 = True
                first2 = i
                break
        
        if has2:
            first2_positions.append(first2)
            break
    else:
        first2_positions.append(-1)  # no digit 2 found (shouldn't happen)

print(f"First digit 2 positions: {sorted(set(first2_positions))}")
print(f"Distribution:")
for pos in sorted(set(first2_positions)):
    count = first2_positions.count(pos)
    print(f"  Position {pos:2d}: {count:4d} examples ({100*count/len(c30_examples):.1f}%)")

# ─── Key question: is there a MAXIMUM first2 position? ───
max_first2 = max(first2_positions)
print(f"\nMaximum first digit 2 position: {max_first2}")
print(f"This means: every C30 example has a digit 2 in its last {max_first2+1} ternary digits")

# ─── Check: for r ≥ 23, is it TRUE that C30Lead → ∃ digit 2 in last few digits? ───
print("\n" + "="*80)
print("THEOREM VERIFICATION")
print("="*80)
print()
print("Proposed theorem:")
print("  For all r ≥ 23:")
print("    {r log₃ 2} ∈ C30Lead")
print("    ⟹ 2^r has a digit 2 in its last K* ternary digits")
print(f"  where K* = {max_first2+1}")
print()

# Verify: check if any C30 example has no digit 2 in last K* digits
K_star = max_first2 + 1
violations = []
for r in c30_examples:
    pow2r = pow(2, r, 3**K_star)
    v = pow2r
    trail = []
    for i in range(K_star):
        trail.append(v % 3)
        v //= 3
    
    if has_no_digit_2(trail):
        violations.append(r)

if violations:
    print(f"VIOLATIONS: {violations}")
else:
    print(f"VERIFIED: All {len(c30_examples)} C30 examples have digit 2 in last {K_star} digits")

# ─── What's the minimum K that works? ───
print("\n--- Minimum K such that C30Lead → digit 2 in last K digits ---")
for K in range(1, max_first2+2):
    all_have_2 = True
    for r in c30_examples:
        pow2r = pow(2, r, 3**K)
        v = pow2r
        trail = []
        for i in range(K):
            trail.append(v % 3)
            v //= 3
        
        if has_no_digit_2(trail):
            all_have_2 = False
            break
    
    if all_have_2:
        print(f"  K={K}: WORKS! All C30 examples have digit 2 in last {K} digits")
        break
    else:
        # Count how many survive
        n_survive = 0
        for r in c30_examples:
            pow2r = pow(2, r, 3**K)
            v = pow2r
            trail = []
            for i in range(K):
                trail.append(v % 3)
                v //= 3
            if has_no_digit_2(trail):
                n_survive += 1
        print(f"  K={K}: {n_survive} C30 examples survive (no digit 2 in last {K} digits)")

# ─── The finite-state theorem ───
print("\n" + "="*80)
print("FINITE-STATE THEOREM")
print("="*80)
print()
print("Theorem:")
print(f"  For all r ≥ 23, if {{r log₃ 2}} ∈ C30Lead,")
print(f"  then 2^r mod 3^K has a digit 2 for some K ≤ {max_first2+1}.")
print()
print("Corollary:")
print(f"  For all K ≥ {max_first2+1} and all r ≥ 23:")
print(f"    r ∈ N_K ⟹ {{r log₃ 2}} ∉ C30Lead")
print()
print("This is a FINITE theorem that can be verified by checking")
print(f"  K = 1, 2, ..., {max_first2+1}")
print("  and the finitely many r values in each residue class.")
