#!/usr/bin/env python3
"""Check if positions 5-14 cover all cases. If yes, we can restrict
n5_digitMod_covers to j < 10 and use periodicity for r >= 162*59049."""
N5 = [0, 2, 8, 20, 24, 26, 54, 56, 62, 72, 74, 78, 80, 96, 126, 150]

def digit_mod(n, j):
    m = 3**(j+1)
    return pow(2, n, m) // (3**j) % 3

# Check positions 5-14 for ALL (s, k) pairs in full range
total = 0
missing_5_14 = 0
for s in N5:
    for k in range(59049):
        r = s + 162 * k
        if r < 69:
            continue
        total += 1
        found = any(digit_mod(r, j+5) == 2 for j in range(10))  # pos 5-14
        if not found:
            missing_5_14 += 1
            if missing_5_14 <= 3:
                print(f"  MISSING: s={s}, k={k}, r={r}")
                for jj in range(38):
                    d = digit_mod(r, jj+5)
                    if d == 2:
                        print(f"    First digit 2 at position {jj+5}")
                        break

print(f"\nTotal: {total}")
print(f"Missing (pos 5-14): {missing_5_14}")
print(f"Covered by pos 5-14: {total - missing_5_14}/{total}")

# Also check: for cases needing pos >= 15, v3(2^(162*59049)-1) = 15
# So positions 5-14 transfer via period 162*59049
# For position 15+: v3 = 15, need dj+6 <= 15, i.e. dj <= 9, pos <= 14
# So positions 5-14 transfer, positions 15+ don't

# Check if there are cases where the FIRST digit 2 is at pos >= 15
# but there's ALSO a digit 2 at pos <= 14
first_pos_dist = {}
for s in N5:
    for k in range(59049):
        r = s + 162 * k
        if r < 69:
            continue
        for jj in range(38):
            if digit_mod(r, jj+5) == 2:
                first_pos_dist[jj+5] = first_pos_dist.get(jj+5, 0) + 1
                break

print("\nFirst digit-2 position distribution:")
for p in sorted(first_pos_dist.keys()):
    print(f"  pos {p}: {first_pos_dist[p]} cases")
