#!/usr/bin/env python3
"""Find the TRUE max position needed across all gap cases and q values."""

N5_EVEN = [0, 2, 8, 20, 24, 26, 54, 56, 62, 72, 74, 78, 80, 96, 126, 150]
P = 162 * 59049

def digitMod(r, j):
    m = 3 ** (j + 1)
    return (pow(2, r, m) // (3 ** j)) % 3

# Find gap cases and their max needed position
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

# For each gap case, find failing q values and their max position
max_pos_overall = 0
fail_count_by_pos = {}

for s, k, r_prime in gap_cases:
    for q in range(1, 501):
        r = r_prime + P * q
        # Find first position with digit 2
        first_pos = None
        for j in range(5, 200):
            if digitMod(r, j) == 2:
                first_pos = j
                break
        if first_pos is not None and first_pos > 42:
            fail_count_by_pos[first_pos] = fail_count_by_pos.get(first_pos, 0) + 1
            if first_pos > max_pos_overall:
                max_pos_overall = first_pos

print(f"Max position needed: {max_pos_overall}")
print()
print("Distribution of positions > 42:")
for pos in sorted(fail_count_by_pos.keys()):
    print(f"  Position {pos}: {fail_count_by_pos[pos]} cases")

# Check: for gap cases, what's the max position for q=1?
print()
print("Max position for q=1 across all gap cases:")
max_pos_q1 = 0
for s, k, r_prime in gap_cases:
    r = r_prime + P * 1
    for j in range(5, 200):
        if digitMod(r, j) == 2:
            if j > max_pos_q1:
                max_pos_q1 = j
            break
print(f"  Max position: {max_pos_q1}")

# The key question: is the max position bounded?
# Check q=1..1000 for a few gap cases with high positions
print()
print("Checking periodicity of max position for specific gap cases:")
for s, k, r_prime in gap_cases[:5]:
    max_pos = 0
    for q in range(1, 1001):
        r = r_prime + P * q
        for j in range(5, 200):
            if digitMod(r, j) == 2:
                if j > max_pos:
                    max_pos = j
                break
    print(f"  s={s}, k={k}: max position over q=1..1000 = {max_pos}")
