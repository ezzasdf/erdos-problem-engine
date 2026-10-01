#!/usr/bin/env python3
"""Analyze the 89 failures more carefully."""

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

# For each gap case, find ALL failing q in [1, 500]
fail_by_s = {}
all_failures = []

for s, k, r_prime in gap_cases:
    for q in range(1, 501):
        r = r_prime + P * q
        found = False
        for j in range(5, 43):
            if digitMod(r, j) == 2:
                found = True
                break
        if not found:
            all_failures.append((s, k, q, r))
            fail_by_s[s] = fail_by_s.get(s, 0) + 1

print(f"Total failures: {len(all_failures)}")
print()
print("Failures by residue s:")
for s in sorted(fail_by_s.keys()):
    print(f"  s={s}: {fail_by_s[s]} failures")

print()
print("First 20 failures:")
for s, k, q, r in all_failures[:20]:
    # Check what position DOES have digit 2 for this r
    for j in range(5, 100):
        if digitMod(r, j) == 2:
            print(f"  s={s}, k={k}, q={q}: first digit 2 at position {j}")
            break
    else:
        print(f"  s={s}, k={k}, q={q}: NO digit 2 at positions 5-99!")

# Check if failures repeat with period 3^28
print()
print("Periodicity analysis for first failure:")
if all_failures:
    s0, k0, q0, r0 = all_failures[0]
    r_prime = s0 + 162 * k0
    # Check q0, q0+3^28, q0+2*3^28
    period = 3**28
    for offset in [0, 1, 2, 3, 4, 5]:
        q_test = q0 + offset * period
        r_test = r_prime + P * q_test
        found = False
        for j in range(5, 43):
            if digitMod(r_test, j) == 2:
                found = True
                break
        print(f"  q={q_test}: {'FOUND' if found else 'MISS'} at positions 5-42")
