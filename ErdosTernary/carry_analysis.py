#!/usr/bin/env python3
"""
CRITICAL ANALYSIS: Why the digit-state transition is NOT K-independent.

The state must include X = 2^r mod 3^K (the "lower digits"), not just 
the digits at positions K..K+c-1.

Key question: does the transition depend on X, or only on the digit window?
"""
from collections import defaultdict

def uk(K):
    return 2 * (3 ** (K - 1))

def ternary_digits(val, n):
    digits = []
    v = val
    for _ in range(n):
        digits.append(v % 3)
        v //= 3
    return digits

def compute_nk(K):
    period = uk(K)
    modulus = 3 ** K
    result = set()
    for r in range(period):
        p = pow(2, r, modulus)
        v = p
        has2 = False
        for _ in range(K):
            if v % 3 == 2:
                has2 = True
                break
            v //= 3
        if not has2:
            result.add(r)
    return result

SPECIAL = {0, 2, 8}

# ============================================================
# The key insight: the transition depends on the FULL state 
# 2^r mod 3^(K+c), not just the digit window.
# ============================================================

print("="*80)
print("ANALYSIS: What determines the transition?")
print("="*80)

K = 10
c = 6
u = uk(K)
nk = compute_nk(K)
modulus_full = 3 ** (K + c + 5)
mult = pow(2, u, modulus_full)

# Group elements by their digit window
digit_window_to_elements = defaultdict(list)
for r in nk:
    if r in SPECIAL:
        continue
    val = pow(2, r, modulus_full)
    digits = ternary_digits(val, K + c + 5)
    window = tuple(digits[K:K+c])
    lower = pow(2, r, 3 ** K)  # X = 2^r mod 3^K
    digit_window_to_elements[window].append((r, lower, val))

print(f"\nK={K}, c={c}")
print(f"Total non-special elements: {len(nk) - len(SPECIAL)}")

# For each digit window, check if elements with the same window 
# but different X produce different children
inconsistent_count = 0
consistent_count = 0

for window, elements in digit_window_to_elements.items():
    if len(elements) < 2:
        continue
    
    # For each pair, check if children are the same
    for i in range(min(5, len(elements))):
        r1, lower1, val1 = elements[i]
        child1_j1 = (val1 * pow(mult, 1, modulus_full)) % modulus_full
        child1_j2 = (val1 * pow(mult, 2, modulus_full)) % modulus_full
        child1_digits = [ternary_digits(child1_j1, K+c+5), ternary_digits(child1_j2, K+c+5)]
        
        for j in range(i+1, min(5, len(elements))):
            r2, lower2, val2 = elements[j]
            child2_j1 = (val2 * pow(mult, 1, modulus_full)) % modulus_full
            child2_j2 = (val2 * pow(mult, 2, modulus_full)) % modulus_full
            child2_digits = [ternary_digits(child2_j1, K+c+5), ternary_digits(child2_j2, K+c+5)]
            
            # Compare child states at positions K+1..K+c
            same = True
            for d1, d2 in zip(child1_digits, child2_digits):
                if tuple(d1[K+1:K+1+c]) != tuple(d2[K+1:K+1+c]):
                    same = False
                    break
            
            if same:
                consistent_count += 1
            else:
                inconsistent_count += 1

print(f"Consistent pairs: {consistent_count}")
print(f"Inconsistent pairs: {inconsistent_count}")

# ============================================================
# The REAL question: does the carry from position K-1 to K 
# depend on X = 2^r mod 3^K?
# ============================================================

print("\n" + "="*80)
print("CARRY ANALYSIS: What determines the carry?")
print("="*80)

print("""
When we compute 2^(r+uK) = 2^r * 2^(uK), the digit at position K 
in the result depends on:

  digit_K = (carry_from_K_minus_1 + sum_{i+j=K} digit_i(2^r) * digit_j(2^uK)) % 3

The carry from position K-1 depends on the full multiplication of 
2^r and 2^(uK) at positions 0..K-1.

Since 2^(uK) ≡ 1 (mod 3^K), the digits of 2^(uK) at positions 0..K-1 
are just the digits of 1, which are all 0 except position 0 = 1.

So the carry from position K-1 to K is:
  carry = floor((2^r mod 3^K) * 1 / 3^K) = 0

Wait, that's not right. The carry depends on the FULL multiplication 
at position K-1, not just the product at that position.

Let me compute the actual carry for specific examples.
""")

# Compute carry for specific r values
print("Computing carries for r ∈ N_K at K=10:")
for r in sorted(list(nk)[:10]):
    if r in SPECIAL:
        continue
    val = pow(2, r, modulus_full)
    
    # Compute 2^r * 2^(uK) mod 3^(K+c+5)
    result = (val * mult) % modulus_full
    
    # The carry from position K-1 to K is:
    # floor((2^r mod 3^K) * (2^(uK) mod 3^K) / 3^K)
    # But 2^(uK) mod 3^K = 1 (since 2^(uK) ≡ 1 + 3^K mod 3^(K+1))
    # So carry = floor((2^r mod 3^K) / 3^K) = 0
    
    # Actually, the carry is more subtle. Let me compute it directly.
    lower = pow(2, r, 3 ** K)
    carry = lower // (3 ** (K-1))  # This is the (K-1)-th digit, not the carry
    
    # The actual carry is from the multiplication at position K-1
    # Let me compute the full product at positions 0..K
    product = lower * 1  # Since 2^(uK) mod 3^K = 1
    actual_carry = product // (3 ** K)
    
    print(f"  r={r:6d}: lower={lower:6d} carry={actual_carry}")

# ============================================================
# KEY FINDING: The carry is always 0!
# ============================================================

print("\n" + "="*80)
print("KEY FINDING: The carry from position K-1 to K is always 0")
print("="*80)

print("""
Since 2^(uK) ≡ 1 (mod 3^K), we have:
  2^r * 2^(uK) mod 3^K = 2^r mod 3^K * 1 = 2^r mod 3^K

So the lower K digits of 2^(r+uK) are the SAME as the lower K digits of 2^r.

This means:
  - The carry from position K-1 to K is 0
  - The digit at position K in 2^(r+uK) depends ONLY on:
    1. The digit at position K in 2^r
    2. The digit at position K in 2^(uK) (= 1)
    3. The carry from position K-1 (= 0)

So digit_K(2^(r+uK)) = (digit_K(2^r) + 1) % 3

Wait, that's not right either. The multiplication is 2^r * 2^(uK), not 2^r + 2^(uK).

Let me reconsider. The digit at position K in the product 2^r * 2^(uK) is:

  sum_{i+j=K} digit_i(2^r) * digit_j(2^(uK)) + carry_from_K_minus_1

Since 2^(uK) ≡ 1 (mod 3^K), we have digit_j(2^(uK)) = 0 for 0 < j < K, and digit_0(2^(uK)) = 1.

So the sum is:
  digit_K(2^r) * digit_0(2^(uK)) + sum_{i=1}^{K} digit_{K-i}(2^r) * digit_i(2^(uK))
  = digit_K(2^r) * 1 + sum_{i=1}^{K} digit_{K-i}(2^r) * 0
  = digit_K(2^r)

And the carry from position K-1 is:
  floor((sum_{i+j=K-1} digit_i(2^r) * digit_j(2^(uK))) / 3)
  = floor(digit_{K-1}(2^r) * digit_0(2^(uK)) / 3)
  = floor(digit_{K-1}(2^r) / 3)
  = 0 (since digit_{K-1}(2^r) ∈ {0, 1})

So digit_K(2^(r+uK)) = digit_K(2^r) + 0 = digit_K(2^r)?

That can't be right — we know the digit changes!

The issue is that I'm not accounting for the carries from LOWER positions. The carry from position K-1 to K depends on the FULL product at positions 0..K-1, not just the product at position K-1.

Let me recompute more carefully.
""")

# Detailed carry computation
print("Detailed carry computation for r=0 at K=10:")
r = 0
val = pow(2, r, modulus_full)
result = (val * mult) % modulus_full

# Compute digit by digit
print(f"2^r mod 3^(K+c+5) = {val}")
print(f"2^(uK) mod 3^(K+c+5) = {mult}")
print(f"2^(r+uK) mod 3^(K+c+5) = {result}")

# Digits of each
digits_r = ternary_digits(val, K + c + 5)
digits_mult = ternary_digits(mult, K + c + 5)
digits_result = ternary_digits(result, K + c + 5)

print(f"\nDigits of 2^r at positions 0..{K+c+4}:")
for i in range(K + 2):
    print(f"  pos {i:2d}: {digits_r[i]}")

print(f"\nDigits of 2^(uK) at positions 0..{K+c+4}:")
for i in range(K + 2):
    print(f"  pos {i:2d}: {digits_mult[i]}")

print(f"\nDigits of 2^(r+uK) at positions 0..{K+c+4}:")
for i in range(K + 2):
    print(f"  pos {i:2d}: {digits_result[i]}")

# The carry at position K
carry = 0
for pos in range(K + 1):
    # Sum of digit_i(2^r) * digit_j(2^(uK)) for i+j = pos
    s = carry
    for i in range(pos + 1):
        j = pos - i
        if i < len(digits_r) and j < len(digits_mult):
            s += digits_r[i] * digits_mult[j]
    carry = s // 3
    digit = s % 3
    if pos >= K - 2:
        print(f"  pos {pos:2d}: sum={s:3d} carry_out={carry} digit={digit}")

# ============================================================
# The REAL transition rule
# ============================================================

print("\n" + "="*80)
print("THE REAL TRANSITION RULE")
print("="*80)

print("""
The digit at position K in 2^(r+uK) is NOT simply digit_K(2^r) + 1.

It depends on the FULL carry propagation from positions 0..K-1.

The carry from position K-1 to K is:
  carry_K = floor((sum_{i=0}^{K-1} digit_i(2^r) * digit_{K-1-i}(2^(uK)) + carry_{K-1}) / 3)

Since digit_j(2^(uK)) = 0 for 0 < j < K, this simplifies to:
  carry_K = floor((digit_{K-1}(2^r) * 1 + carry_{K-1}) / 3)

And carry_{K-1} depends on digit_{K-2}(2^r), etc.

So the carry depends on the FULL digit pattern of 2^r at positions 0..K-1.

This means the state must include the FULL digit pattern, not just the window.

However, since 2^r mod 3^K has no digit 2 (by definition of N_K), the digits 
are in {0, 1}. So the state space is 2^K, which grows with K.

CONCLUSION: The finite-state automaton approach with K-INDEPENDENT state 
does NOT work directly. The state must include the full lower digits.
""")
