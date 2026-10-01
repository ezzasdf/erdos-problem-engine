#!/usr/bin/env python3
"""Check: for each gap case, does position 15 alone have digit2 for all q mod 81?
If yes, we can handle all q by checking 81 residues per gap case.
If not, try positions 15-16 (period 3^5=243), etc."""

N5_EVEN = [0, 2, 8, 20, 24, 26, 54, 56, 62, 72, 74, 78, 80, 96, 126, 150]
P = 162 * 59049

def digitMod(r, j):
    m = 3 ** (j + 1)
    return (pow(2, r, m) // (3 ** j)) % 3

# Find gap cases
gap_cases = []
for s in N5_EVEN:
    for k in range(59049):
        r_prime = s + 162 * k
        if r_prime < 69:
            continue
        has_5_14 = any(digitMod(r_prime, j) == 2 for j in range(5, 15))
        if not has_5_14:
            gap_cases.append((s, k, r_prime))

print(f"Gap cases: {len(gap_cases)}")

# For position 15 alone: period in q is 3^4 = 81
# digitMod(r' + P*q, 15) depends on q mod 81
# Check: for each gap case, is digit2 at position 15 for all q mod 81?
pos15_fails = 0
for s, k, r_prime in gap_cases:
    for q_mod in range(81):
        q = q_mod  # representative
        r = r_prime + P * q
        if digitMod(r, 15) != 2:
            pos15_fails += 1
            break

print(f"Gap cases where position 15 alone fails: {pos15_fails}")
print(f"(i.e., for some q mod 81, position 15 has digit != 2)")

# For positions 15-16: period is 3^5 = 243
pos15_16_fails = 0
for s, k, r_prime in gap_cases:
    for q_mod in range(243):
        q = q_mod
        r = r_prime + P * q
        has2 = any(digitMod(r, j) == 2 for j in [15, 16])
        if not has2:
            pos15_16_fails += 1
            break

print(f"\nGap cases where positions 15-16 fail: {pos15_16_fails}")

# For positions 15-20: period is 3^9 = 19683
pos15_20_fails = 0
for s, k, r_prime in gap_cases[:100]:  # check first 100 for speed
    for q_mod in range(19683):
        q = q_mod
        r = r_prime + P * q
        has2 = any(digitMod(r, j) == 2 for j in range(15, 21))
        if not has2:
            pos15_20_fails += 1
            break

print(f"\nGap cases (first 100) where positions 15-20 fail: {pos15_20_fails}")

# For positions 15-30: period is 3^19 ≈ 10^9 — too large
# But check: for the 89 failing q=1..500 cases, what's the min position range?
print("\nFor the 89 cases needing pos 43-55:")
print("These are for q values where positions 15-42 fail.")
print("Check: do positions 15-42 always have digit2 for q mod 3^31?")
# Too large. Let's check with a different approach.
