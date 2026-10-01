#!/usr/bin/env python3
"""
Window size experiment: what is the minimum window K..K+w 
that guarantees digit 2 for all non-special r ∈ N_K?
"""
import time

def uk(K):
    return 2 * (3 ** (K - 1))

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

def first_digit2_pos(r, start, limit):
    """Find first position >= start where 2^r has digit 2. Returns -1 if not found."""
    modulus = 3 ** (limit + 1)
    val = pow(2, r, modulus)
    v = val
    for pos in range(limit + 1):
        if pos >= start and v % 3 == 2:
            return pos
        v //= 3
    return -1

SPECIAL = {0, 2, 8}
MAX_K = 13
SEARCH_LIMIT = 60

print("="*80)
print("WINDOW SIZE EXPERIMENT")
print("="*80)

# Compute N_K
nk = {}
for K in range(5, MAX_K + 1):
    t0 = time.time()
    nk[K] = compute_nk(K)
    t1 = time.time()
    print(f"K={K}: |N_K|={len(nk[K]):5d} ({t1-t0:.1f}s)")

# For each K, find the offset distribution
print("\n" + "="*80)
print("Distribution of first digit-2 offset from K (non-special elements)")
print("="*80)

for K in range(5, MAX_K + 1):
    nk_k = nk[K]
    offsets = []
    
    for r in nk_k:
        if r in SPECIAL:
            continue
        pos = first_digit2_pos(r, K, SEARCH_LIMIT)
        if pos >= 0:
            offsets.append(pos - K)
        else:
            offsets.append(SEARCH_LIMIT)  # worst case
    
    offsets.sort()
    n = len(offsets)
    print(f"K={K:2d}: n={n:4d} min={offsets[0]:2d} "
          f"p25={offsets[n//4]:2d} med={offsets[n//2]:2d} "
          f"p75={offsets[3*n//4]:2d} p95={offsets[int(0.95*n)]:2d} "
          f"max={offsets[-1]:2d}")

# Critical test: does every non-special element have digit 2 within K..49?
print("\n" + "="*80)
print("CRITICAL: Coverage within bridge window K..49")
print("="*80)

for K in range(5, 18):
    if K not in nk:
        print(f"K={K:2d}: (not computed)")
        continue
    nk_k = nk[K]
    
    covered = 0
    total = 0
    worst_r = None
    worst_pos = -1
    
    for r in nk_k:
        if r in SPECIAL:
            continue
        total += 1
        pos = first_digit2_pos(r, K, 49)
        if pos >= 0:
            covered += 1
            if worst_pos < 0 or pos - K > worst_pos:
                worst_pos = pos - K
                worst_r = r
        else:
            worst_r = r
            worst_pos = -1
    
    if total == 0:
        print(f"K={K:2d}: (no non-special elements)")
    elif covered == total:
        print(f"K={K:2d}: ALL {total} non-special elements covered within K..49 (worst offset: {worst_pos})")
    else:
        print(f"K={K:2d}: FAILED - {covered}/{total} covered. First failure: r={worst_r}")

# How about the special elements? Do they eventually get digit 2?
print("\n" + "="*80)
print("Special elements {0,2,8}: first digit-2 position (if any)")
print("="*80)

for r in SPECIAL:
    pos = first_digit2_pos(r, 0, SEARCH_LIMIT)
    if pos >= 0:
        print(f"  r={r}: first digit 2 at position {pos}")
    else:
        print(f"  r={r}: NO digit 2 found in positions 0..{SEARCH_LIMIT}")

# Extended check: what if the bridge window is K..K+30 instead of K..49?
print("\n" + "="*80)
print("What if bridge window is K..K+30 instead of K..49?")
print("="*80)

for K in range(5, MAX_K + 1):
    nk_k = nk[K]
    covered = 0
    total = 0
    
    for r in nk_k:
        if r in SPECIAL:
            continue
        total += 1
        pos = first_digit2_pos(r, K, K + 30)
        if pos >= 0:
            covered += 1
    
    print(f"K={K:2d}: {covered}/{total} covered within K..K+30")
