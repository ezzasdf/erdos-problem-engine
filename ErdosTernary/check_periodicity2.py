#!/usr/bin/env python3
"""Check if positions 5-42 cover all (s,k) pairs, and how many need higher positions."""
N5 = [0, 2, 8, 20, 24, 26, 54, 56, 62, 72, 74, 78, 80, 96, 126, 150]

def digit_mod(n, j):
    m = 3**(j+1)
    return pow(2, n, m) // (3**j) % 3

# For each missing case from pos 5-11, find earliest position with digit 2
missing_details = {}
total = 0
covered_by_full = 0

for s in N5:
    for k in range(59049):
        r = s + 162 * k
        if r < 69:
            continue
        total += 1
        found = False
        for j in range(7):
            if digit_mod(r, j + 5) == 2:
                found = True
                break
        if not found:
            # Check positions 12-42
            for j in range(7, 38):
                d = digit_mod(r, j + 5)
                if d == 2:
                    covered_by_full += 1
                    break
            else:
                # Truly missing even with all 38 positions
                if len(missing_details) < 3:
                    missing_details[r] = [digit_mod(r, j) for j in range(5, 43)]

print(f"Total: {total}")
print(f"Covered by pos 5-11: {total - 55293}")
print(f"Need pos 12+: {55293}")
print(f"Covered by full range 5-42: {covered_by_full}")
print(f"Truly uncovered: {55293 - covered_by_full}")
if missing_details:
    print(f"\nTruly uncovered examples:")
    for r, digits in missing_details.items():
        print(f"  r={r}: digits at pos 5-42 = {digits}")

# Check: for the cases needing pos 12+, what's the max position needed?
max_pos_needed = 0
pos_histogram = {}
for s in N5:
    for k in range(59049):
        r = s + 162 * k
        if r < 69:
            continue
        found_low = any(digit_mod(r, j+5) == 2 for j in range(7))
        if not found_low:
            for j in range(7, 38):
                if digit_mod(r, j + 5) == 2:
                    pos = j + 5
                    max_pos_needed = max(max_pos_needed, pos)
                    pos_histogram[pos] = pos_histogram.get(pos, 0) + 1
                    break

print(f"\nMax position needed (for cases missing pos 5-11): {max_pos_needed}")
print(f"Position histogram:")
for p in sorted(pos_histogram.keys()):
    print(f"  pos {p}: {pos_histogram[p]} cases")
