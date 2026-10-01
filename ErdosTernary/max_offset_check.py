#!/usr/bin/env python3
"""Check if the max digit-2 offset is bounded for larger K."""
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

def first_digit2_offset(r, start, limit):
    modulus = 3 ** (limit + 1)
    val = pow(2, r, modulus)
    v = val
    for pos in range(limit + 1):
        if pos >= start and v % 3 == 2:
            return pos - start
        v //= 3
    return -1

SPECIAL = {0, 2, 8}

print("Computing max offset for K=5..15...")
print(f"{'K':>3} {'|N_K|':>8} {'max_offset':>10} {'worst_r':>8} {'bridge_ok':>10}")
print("-"*50)

for K in range(5, 16):
    t0 = time.time()
    nk = compute_nk(K)
    t1 = time.time()
    
    max_offset = 0
    worst_r = 0
    bridge_ok = True
    
    for r in nk:
        if r in SPECIAL:
            continue
        offset = first_digit2_offset(r, K, 59)
        if offset < 0:
            bridge_ok = False
            worst_r = r
            break
        if offset > max_offset:
            max_offset = offset
            worst_r = r
    
    # Check if worst case is within bridge window K..49
    in_bridge = max_offset <= (49 - K)
    
    print(f"{K:3d} {len(nk):8d} {max_offset:10d} {worst_r:8d} {'YES' if in_bridge else 'NO':>10}  ({t1-t0:.1f}s)")
