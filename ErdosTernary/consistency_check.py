#!/usr/bin/env python3
"""
Consistency check: for r ∈ N_K, does the interval [3^{floor(rα)+29}, 3^{floor(rα)+30})
contain an integer congruent to 2^r mod 3^K?

If NO, the theorem holds for that r,K.
If YES, a counterexample might exist (need to check if the integer is actually 2^r).
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

# ─── Consistency check ───
print("="*80)
print("CONSISTENCY CHECK: Can the leading/trailing constraints coexist?")
print("="*80)

# For each r ∈ N_K, check if the interval [3^{floor(rα)+29}, 3^{floor(rα)+30})
# contains an integer congruent to 2^r mod 3^K.

# The interval has width 3^{floor(rα)+29} × 2 (since 3^{n+1} - 3^n = 2×3^n).
# The residue classes mod 3^K partition the integers into 3^K classes.
# The interval contains approximately 2×3^{floor(rα)+29} / 3^K = 2×3^{floor(rα)+29-K} integers.
# For floor(rα) ≈ r×0.631, this is approximately 2×3^{0.631r+29-K}.

# For r=23, K=12: 2×3^{0.631×23+29-12} = 2×3^{31.5} ≈ 10^15. Very large.
# So the interval is HUGE compared to 3^K, and almost certainly contains every residue class.

# The question is NOT whether the interval contains the residue class.
# The question is whether the INTEGER 2^r itself is in the interval and has the right leading digits.

# Let me check directly: for r ∈ N_K, is 2^r in the "right" interval?

print("\n--- Direct check: is 2^r in the interval consistent with its leading digits? ---")

for K in [12]:
    uK = 2 * 3**(K-1)
    modulus = 3**K
    
    n_check = 0
    n_consistent = 0
    
    for r in range(23, min(uK, 50000)):
        # Trailing K digits
        pow2r = pow(2, r, modulus)
        has2_trail = False
        v = pow2r
        for i in range(K):
            if v % 3 == 2:
                has2_trail = True
                break
            v //= 3
        
        if has2_trail:
            continue
        
        n_check += 1
        
        # Leading 30 digits
        lead = leading_30_digits(r)
        lead_ok = has_no_digit_2(lead)
        
        if lead_ok:
            n_consistent += 1
            print(f"  r={r}: BOTH conditions satisfied! "
                  f"trailing mod = {pow2r}, leading = {lead[:10]}...")
    
    print(f"\n  K={K}: checked {n_check} survivors, consistent = {n_consistent}")

# ─── The real question: for r ∉ N_K, how often is C30Lead? ───
print("\n--- How common is C30Lead among ALL r ≥ 23? ---")
n_c30 = 0
n_total = 0
for r in range(23, 100001):
    n_total += 1
    lead = leading_30_digits(r)
    if has_no_digit_2(lead):
        n_c30 += 1
        if n_c30 <= 10:
            # Check if r is in N_12
            pow12 = pow(2, r, 3**12)
            v = pow12
            trail = []
            for i in range(12):
                trail.append(v % 3)
                v //= 3
            in_n12 = has_no_digit_2(trail)
            
            # Also check N_8
            pow8 = pow(2, r, 3**8)
            v = pow8
            trail8 = []
            for i in range(8):
                trail8.append(v % 3)
                v //= 3
            in_n8 = has_no_digit_2(trail8)
            
            print(f"  r={r}: C30, in N_8={in_n8}, in N_12={in_n12}")

print(f"\n  Total r in [23, 100000]: {n_total}")
print(f"  C30 examples: {n_c30}")
print(f"  Fraction: {n_c30/n_total:.6f}")
print(f"  Expected from measure: {(2/3)**30:.6f}")

# ─── Key insight: check if C30Lead is EMPTY for r ≥ 23 ───
print("\n--- Is C30Lead empty for r ≥ 23? ---")
print("Checking r from 23 to 1000000...")
n_c30_large = 0
for r in range(23, 1000001):
    lead = leading_30_digits(r)
    if has_no_digit_2(lead):
        n_c30_large += 1
        if n_c30_large <= 5:
            print(f"  r={r}: C30Lead")

print(f"\n  Total r in [23, 1000000]: 999978")
print(f"  C30 examples: {n_c30_large}")
if n_c30_large == 0:
    print(f"  C30Lead appears to be EMPTY for r ∈ [23, 1000000]!")
    print(f"  Expected count from measure: {999978 * (2/3)**30:.2f}")
