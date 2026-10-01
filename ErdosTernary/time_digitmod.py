#!/usr/bin/env python3
"""Quick timing test: how long does it take to compute digitMod for one (s, k) pair
checking positions 5-55?"""

import time

def digitMod(r, j):
    m = 3 ** (j + 1)
    return (pow(2, r, m) // (3 ** j)) % 3

# Time a single (s, k) pair with range 51
s, k = 0, 10000
r = s + 162 * k

start = time.time()
for _ in range(1000):
    for j in range(5, 56):
        if digitMod(r, j) == 2:
            break
elapsed = time.time() - start
print(f"1000 iterations of range 51: {elapsed:.3f}s")
print(f"Per iteration: {elapsed/1000*1000:.3f}ms")

# Estimate for 945K cases
est_38 = 945000 * (elapsed / 1000) * (38/51)
est_51 = 945000 * (elapsed / 1000)
print(f"\nEstimated time for 945K cases, range 38: {est_38:.0f}s = {est_38/60:.1f}min")
print(f"Estimated time for 945K cases, range 51: {est_51:.0f}s = {est_51/60:.1f}min")
print(f"Estimated time for 59K cases (1 residue), range 51: {est_51/16:.0f}s = {est_51/16/60:.1f}min")
