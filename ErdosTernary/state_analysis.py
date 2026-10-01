#!/usr/bin/env python3
"""
The correct state for the transition is X = 2^r mod 3^K (the lower digits).
This determines the carry, which in turn determines the child digits.

Key insight: X ∈ N_K means X has no digit 2 in base 3.
Since digits are in {0,1}, the state space is at most 2^K.
But X mod 3 ∈ {1, 2}, so actually |N_K| = 2^(K-1).

Question: does the transition depend on X in a K-independent way?
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

print("="*80)
print("THE CORRECT STATE SPACE: X = 2^r mod 3^K")
print("="*80)

print("""
Since 2^r mod 3^K determines:
  1. The digits of 2^r at positions 0..K-1 (the "lower state")
  2. The carry from position K-1 to K (when multiplying by 2^(uK))
  3. The digit at position K in 2^(r+uK) (via the carry)

The full state is X = 2^r mod 3^K.
The transition is: X -> {X * 2^(uK) mod 3^(K+1), X * 2^(2*uK) mod 3^(K+1)}
filtered by which have no digit 2 at position K.

But this is K-dependent! The state space grows as 3^K.

However, the transition RULE might be K-independent:
  X -> floor(X * multiplier / 3^K) determines the new digit at position K
  
where multiplier = 2^(uK) mod 3^(K+c) for some fixed c.
""")

# ============================================================
# Test: is the transition K-independent when we use X as state?
# ============================================================

print("="*80)
print("TEST: K-independence of transition with X as state")
print("="*80)

# For K=10 and K=11, check if the same X produces the same child digits
for K_test in [10, 11, 12]:
    nk = compute_nk(K_test)
    u = uk(K_test)
    modulus_k = 3 ** K_test
    modulus_k1 = 3 ** (K_test + 1)
    modulus_k2 = 3 ** (K_test + 6)  # Extra precision
    
    mult1 = pow(2, u, modulus_k2)
    mult2 = pow(2, 2*u, modulus_k2)
    
    # For each r in N_K, compute X = 2^r mod 3^K and child digits
    x_to_children = {}
    inconsistent = 0
    
    for r in sorted(nk):
        if r in SPECIAL:
            continue
        X = pow(2, r, modulus_k)
        
        # Children are r+uK and r+2*uK
        # Their X values are:
        X1 = (X * pow(2, u, modulus_k1)) % modulus_k1
        X2 = (X * pow(2, 2*u, modulus_k1)) % modulus_k1
        
        # Child digit at position K_test (for N_{K+1})
        d1 = (X1 // modulus_k) % 3
        d2 = (X2 // modulus_k) % 3
        
        child_info = (d1, d2)
        
        if X in x_to_children:
            if x_to_children[X] != child_info:
                inconsistent += 1
        else:
            x_to_children[X] = child_info
    
    print(f"K={K_test}: |N_K|={len(nk)}, unique X values={len(x_to_children)}, inconsistent={inconsistent}")

# ============================================================
# The transition in terms of X
# ============================================================

print("\n" + "="*80)
print("THE TRANSITION IN TERMS OF X")
print("="*80)

K = 10
nk = compute_nk(K)
u = uk(K)
modulus_k = 3 ** K
modulus_k1 = 3 ** (K + 1)

print(f"\nK={K}, |N_K|={len(nk)}")

# Compute transition for each X
transitions = {}
for r in sorted(nk):
    if r in SPECIAL:
        continue
    X = pow(2, r, modulus_k)
    
    # Children
    X1 = (X * pow(2, u, modulus_k1)) % modulus_k1
    X2 = (X * pow(2, 2*u, modulus_k1)) % modulus_k1
    
    d1 = (X1 // modulus_k) % 3
    d2 = (X2 // modulus_k) % 3
    
    # Which survive?
    survivors = []
    if d1 != 2:
        survivors.append(1)
    if d2 != 2:
        survivors.append(2)
    
    transitions[X] = {'children': (X1, X2), 'digits': (d1, d2), 'survivors': survivors}

# Show some transitions
print("\nSample transitions (X -> (X1, X2), digits at K, survivors):")
for X in sorted(transitions.keys())[:10]:
    info = transitions[X]
    print(f"  X={X:6d} -> ({info['children'][0]:6d}, {info['children'][1]:6d})  "
          f"digits=({info['digits'][0]}, {info['digits'][1]})  survivors={info['survivors']}")

# Count transitions by type
type_counts = defaultdict(int)
for X, info in transitions.items():
    d1, d2 = info['digits']
    if d1 == 2 and d2 != 2:
        type_counts['child1_dies'] += 1
    elif d2 == 2 and d1 != 2:
        type_counts['child2_dies'] += 1
    elif d1 != 2 and d2 != 2:
        type_counts['both_survive'] += 1
    else:
        type_counts['both_die'] += 1

print(f"\nTransition types: {dict(type_counts)}")

# ============================================================
# The key insight: the transition depends on X mod 3
# ============================================================

print("\n" + "="*80)
print("KEY INSIGHT: Transition depends on X mod 3")
print("="*80)

# Group transitions by X mod 3
mod3_groups = defaultdict(list)
for X, info in transitions.items():
    mod3_groups[X % 3].append(info['digits'])

for mod3_val in sorted(mod3_groups.keys()):
    digits_list = mod3_groups[mod3_val]
    unique_digits = set(digits_list)
    print(f"  X ≡ {mod3_val} (mod 3): {len(digits_list)} elements, "
          f"unique child digit pairs: {len(unique_digits)}")
    # Show distribution
    from collections import Counter
    c = Counter(digits_list)
    for pair, count in c.most_common(5):
        print(f"    {pair}: {count}")

# ============================================================
# What about X mod 9?
# ============================================================

print("\n" + "="*80)
print("What about X mod 9?")
print("="*80)

mod9_groups = defaultdict(list)
for X, info in transitions.items():
    mod9_groups[X % 9].append(info['digits'])

for mod9_val in sorted(mod9_groups.keys()):
    digits_list = mod9_groups[mod9_val]
    unique_digits = set(digits_list)
    print(f"  X ≡ {mod9_val} (mod 9): {len(digits_list)} elements, "
          f"unique child digit pairs: {len(unique_digits)}")
    from collections import Counter
    c = Counter(digits_list)
    for pair, count in c.most_common(3):
        print(f"    {pair}: {count}")

# ============================================================
# The REAL question: does the transition depend on X or only on 
# the digits of X at positions 0..K-1?
# ============================================================

print("\n" + "="*80)
print("REAL QUESTION: What is the minimum state?")
print("="*80)

# For each pair of r values with the same digit window but different X,
# check if they produce the same children

digit_window_to_elements = defaultdict(list)
for r in sorted(nk):
    if r in SPECIAL:
        continue
    X = pow(2, r, modulus_k)
    digits_X = tuple(ternary_digits(X, K))
    digit_window_to_elements[digits_X].append((r, X))

print(f"\nK={K}:")
print(f"Total unique digit windows: {len(digit_window_to_elements)}")
print(f"Windows with multiple elements: {sum(1 for v in digit_window_to_elements.values() if len(v) > 1)}")

# For windows with multiple elements, check if children differ
inconsistent = 0
consistent = 0
for window, elements in digit_window_to_elements.items():
    if len(elements) < 2:
        continue
    for i in range(min(3, len(elements))):
        r1, X1 = elements[i]
        child1_1 = (X1 * pow(2, u, modulus_k1)) % modulus_k1
        child1_2 = (X1 * pow(2, 2*u, modulus_k1)) % modulus_k1
        
        for j in range(i+1, min(3, len(elements))):
            r2, X2 = elements[j]
            child2_1 = (X2 * pow(2, u, modulus_k1)) % modulus_k1
            child2_2 = (X2 * pow(2, 2*u, modulus_k1)) % modulus_k1
            
            # Compare child digits at position K
            d1_1 = (child1_1 // modulus_k) % 3
            d1_2 = (child1_2 // modulus_k) % 3
            d2_1 = (child2_1 // modulus_k) % 3
            d2_2 = (child2_2 // modulus_k) % 3
            
            if (d1_1, d1_2) == (d2_1, d2_2):
                consistent += 1
            else:
                inconsistent += 1

print(f"Consistent pairs (same window, same children): {consistent}")
print(f"Inconsistent pairs (same window, different children): {inconsistent}")

# ============================================================
# CONCLUSION
# ============================================================

print("\n" + "="*80)
print("CONCLUSION")
print("="*80)
print("""
The transition depends on the FULL value X = 2^r mod 3^K, not just 
the digit window. Two elements with the same digit window but different 
X values can produce different children.

However, the transition DOES depend on X mod 3^c for some small c.
The question is: how large must c be for the transition to be 
determined by X mod 3^c?

From the data, X mod 9 already groups elements well (most groups have 
only 1 unique child digit pair). X mod 27 would be even better.

This suggests a FINITE-STATE model where the state is X mod 3^c 
for some fixed c, independent of K.
""")
