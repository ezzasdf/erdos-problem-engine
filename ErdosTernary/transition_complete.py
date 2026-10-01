#!/usr/bin/env python3
"""
Complete transition analysis: determine the MINIMUM K-independent state.

Key finding: X = 2^r mod 3^K fully determines the transition.
Question: does X mod 3^c for some FIXED c determine it?
"""
from collections import defaultdict, Counter

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
print("COMPLETE TRANSITION ANALYSIS")
print("="*80)

# For each K, compute transitions and check K-independence
for K in range(5, 14):
    nk = compute_nk(K)
    u = uk(K)
    modulus_k = 3 ** K
    modulus_k1 = 3 ** (K + 1)
    
    # Compute 2^(uK) mod 3^(K+1)
    mult1 = pow(2, u, modulus_k1)
    mult2 = pow(2, 2*u, modulus_k1)
    
    # For each r in N_K, compute X and child digits
    x_to_info = {}
    for r in sorted(nk):
        if r in SPECIAL:
            continue
        X = pow(2, r, modulus_k)
        
        # Children
        X1 = (X * mult1) % modulus_k1
        X2 = (X * mult2) % modulus_k1
        
        d1 = (X1 // modulus_k) % 3
        d2 = (X2 // modulus_k) % 3
        
        # Also check base digit
        d0 = (X // modulus_k) % 3  # This is always 0 or 1 for r ∈ N_K
        
        x_to_info[X] = {'d0': d0, 'd1': d1, 'd2': d2}
    
    # Group by X mod 3^c for c=1,2,3
    print(f"\nK={K}: |N_K|={len(nk)}, non-special={len(x_to_info)}")
    
    for c in [1, 2, 3]:
        groups = defaultdict(list)
        for X, info in x_to_info.items():
            key = X % (3 ** c)
            groups[key].append(info)
        
        # Check consistency within each group
        inconsistent = 0
        for key, infos in groups.items():
            unique = set((i['d1'], i['d2']) for i in infos)
            if len(unique) > 1:
                inconsistent += 1
        
        print(f"  X mod 3^{c}: {len(groups)} groups, {inconsistent} inconsistent")
    
    # Show the actual transition types
    type_counts = Counter()
    for X, info in x_to_info.items():
        d0, d1, d2 = info['d0'], info['d1'], info['d2']
        # Determine which survive
        survivors = []
        if d0 != 2:
            survivors.append('base')
        if d1 != 2:
            survivors.append('child1')
        if d2 != 2:
            survivors.append('child2')
        type_counts[tuple(survivors)] += 1
    
    print(f"  Transition types: {dict(type_counts)}")

# ============================================================
# The KEY question: does X mod 3 determine the transition?
# ============================================================

print("\n" + "="*80)
print("KEY QUESTION: Does X mod 3 determine the transition?")
print("="*80)

for K in [5, 8, 10, 12]:
    nk = compute_nk(K)
    u = uk(K)
    modulus_k = 3 ** K
    modulus_k1 = 3 ** (K + 1)
    
    mult1 = pow(2, u, modulus_k1)
    mult2 = pow(2, 2*u, modulus_k1)
    
    # Group by X mod 3
    mod3_groups = defaultdict(list)
    for r in sorted(nk):
        if r in SPECIAL:
            continue
        X = pow(2, r, modulus_k)
        X1 = (X * mult1) % modulus_k1
        X2 = (X * mult2) % modulus_k1
        d1 = (X1 // modulus_k) % 3
        d2 = (X2 // modulus_k) % 3
        mod3_groups[X % 3].append((d1, d2))
    
    print(f"\nK={K}:")
    for mod3_val in sorted(mod3_groups.keys()):
        pairs = mod3_groups[mod3_val]
        unique = set(pairs)
        print(f"  X ≡ {mod3_val} (mod 3): {len(pairs)} elements, "
              f"unique (d1,d2): {unique}")

# ============================================================
# The COMPLETE picture: what determines the transition?
# ============================================================

print("\n" + "="*80)
print("COMPLETE PICTURE: What determines the transition?")
print("="*80)

print("""
For K=5..12, the transition (d1, d2) at position K is:
  - For ALL r ∈ N_K: d1 = 1, d2 = 2

This means:
  - 2^(r+uK) always has digit 1 at position K
  - 2^(r+2uK) always has digit 2 at position K
  
And the base r always has digit 0 or 1 at position K (never 2).

So the THREE digits at position K are ALWAYS {0, 1, 2} or {1, 1, 2}.
The digit 2 is ALWAYS at position K for the j=2 lift.

Wait, that can't be right. Let me verify.
""")

# Verify: for each r, what are the three digits at position K?
K = 10
nk = compute_nk(K)
u = uk(K)
modulus_k = 3 ** K
modulus_k1 = 3 ** (K + 1)

mult0 = 1  # 2^0 = 1
mult1 = pow(2, u, modulus_k1)
mult2 = pow(2, 2*u, modulus_k1)

print(f"\nVerification at K={K}:")
digit_triples = Counter()
for r in sorted(nk)[:20]:
    X = pow(2, r, modulus_k)
    d0 = (X // modulus_k) % 3  # digit at K for base
    d1 = ((X * mult1) // modulus_k) % 3  # digit at K for j=1
    d2 = ((X * mult2) // modulus_k) % 3  # digit at K for j=2
    digit_triples[(d0, d1, d2)] += 1
    print(f"  r={r:6d}: digits at K = ({d0}, {d1}, {d2})")

print(f"\nAll triples: {dict(digit_triples)}")

# Check for ALL r
all_triples = Counter()
for r in sorted(nk):
    if r in SPECIAL:
        continue
    X = pow(2, r, modulus_k)
    d0 = (X // modulus_k) % 3
    d1 = ((X * mult1) // modulus_k) % 3
    d2 = ((X * mult2) // modulus_k) % 3
    all_triples[(d0, d1, d2)] += 1

print(f"\nAll {len(nk)-3} non-special elements: {dict(all_triples)}")

# ============================================================
# CONCLUSION
# ============================================================

print("\n" + "="*80)
print("CONCLUSION")
print("="*80)
print("""
KEY FINDING: For all K=5..12, the three digits at position K are:
  - d(r) ∈ {0, 1} (the base always has digit 0 or 1)
  - d(r+uK) = 1 (always)
  - d(r+2uK) = 2 (always)

This means:
  1. The base r ALWAYS survives (digit 0 or 1 at position K)
  2. The lift r+uK ALWAYS survives (digit 1 at position K)
  3. The lift r+2uK ALWAYS dies (digit 2 at position K)

So the transition is COMPLETELY DETERMINED: it's always the "base+1" type.

This is a HUGE simplification! The transition doesn't depend on X at all 
(beyond the fact that X ∈ N_K ensures the base has no digit 2).

The digit-2 position is ALWAYS at the j=2 lift. So the "death" pattern 
is completely uniform: every element's j=2 child dies.

But wait, this contradicts our earlier finding that the transition types 
are {base+1: ~33%, base+2: ~33%, shifted: ~33%}.

Let me re-examine...
""")
