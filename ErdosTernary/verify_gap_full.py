#!/usr/bin/env python3
"""For each gap case (r' with no digit2 at pos 5-14), check the full r.
Question: for EVERY q ≥ 1, does 2^r have digit2 at some position in [15, K_star)?"""

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

# For gap cases, find max position with digit2 over q=1..500
total_max_pos = 0
total_no_digit2 = 0

for s, k, r_prime in gap_cases:
    max_pos = 0
    no_digit2_count = 0
    for q in range(1, 501):
        r = r_prime + P * q
        found = False
        for j in range(15, 56):
            if digitMod(r, j) == 2:
                found = True
                if j > max_pos:
                    max_pos = j
                break
        if not found:
            no_digit2_count += 1
            total_no_digit2 += 1
    if max_pos > total_max_pos:
        total_max_pos = max_pos

print(f"Max position in [15,55] with digit2 across all gap cases, q=1..500: {total_max_pos}")
print(f"Cases with NO digit2 at positions 15-55: {total_no_digit2}")

# CRITICAL: check positions 15-42 specifically (what certificate gives for r')
# The certificate gives digit2 at pos dj+5 in r'. For gap cases, dj >= 10, so pos >= 15.
# For the full r: is digit2 always at some position in [15,42]?
no_digit2_15_42 = 0
for s, k, r_prime in gap_cases:
    for q in range(1, 501):
        r = r_prime + P * q
        found = False
        for j in range(15, 43):
            if digitMod(r, j) == 2:
                found = True
                break
        if not found:
            no_digit2_15_42 += 1

print(f"\nGap cases with NO digit2 at positions 15-42 (q=1..500): {no_digit2_15_42}")
print(f"This means these need positions 43+")

# Check: for q=1, do all gap cases have digit2 at [15,42]?
no_digit2_q1 = 0
for s, k, r_prime in gap_cases:
    r = r_prime + P * 1
    found = False
    for j in range(15, 43):
        if digitMod(r, j) == 2:
            found = True
            break
    if not found:
        no_digit2_q1 += 1

print(f"\nGap cases with NO digit2 at positions 15-42 (q=1 only): {no_digit2_q1}")

# For q=1 specifically, what's the max position?
max_pos_q1 = 0
for s, k, r_prime in gap_cases:
    r = r_prime + P * 1
    for j in range(15, 200):
        if digitMod(r, j) == 2:
            if j > max_pos_q1:
                max_pos_q1 = j
            break
print(f"Max position with digit2 for q=1: {max_pos_q1}")
