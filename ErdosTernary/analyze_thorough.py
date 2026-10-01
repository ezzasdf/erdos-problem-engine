#!/usr/bin/env python3
"""Thorough check: for each gap case, verify that EVERY q in [1, 500]
has digit 2 at some position 5-42."""

N5_EVEN = [0, 2, 8, 20, 24, 26, 54, 56, 62, 72, 74, 78, 80, 96, 126, 150]
P = 162 * 59049

def digitMod(r, j):
    m = 3 ** (j + 1)
    return (pow(2, r, m) // (3 ** j)) % 3

# Find all gap cases
gap_cases = []
for s in N5_EVEN:
    for k in range(59049):
        r_prime = s + 162 * k
        if r_prime < 69:
            continue
        has_5_14 = False
        for j in range(5, 15):
            if digitMod(r_prime, j) == 2:
                has_5_14 = True
                break
        if not has_5_14:
            gap_cases.append((s, k, r_prime))

print(f"Total gap cases: {len(gap_cases)}")

# For ALL gap cases, check q=1..500
total_checks = 0
total_fails = 0
worst_fail_q = 0

for s, k, r_prime in gap_cases:
    for q in range(1, 501):
        r = r_prime + P * q
        found = False
        for j in range(5, 43):
            if digitMod(r, j) == 2:
                found = True
                break
        if not found:
            total_fails += 1
            if q > worst_fail_q:
                worst_fail_q = q
            if total_fails <= 5:
                print(f"  FAIL: s={s}, k={k}, q={q}, r={r}")
        total_checks += 1

print(f"Total checks: {total_checks}")
print(f"Total failures: {total_fails}")
print(f"Worst failing q: {worst_fail_q}")
if total_checks > 0:
    print(f"Success rate: {100*(total_checks - total_fails)/total_checks:.4f}%")
