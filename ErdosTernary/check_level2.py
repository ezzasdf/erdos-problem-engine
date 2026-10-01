#!/usr/bin/env python3
"""Generate two-level certificate data."""
N5 = [0, 2, 8, 20, 24, 26, 54, 56, 62, 72, 74, 78, 80, 96, 126, 150]

def digit_mod(n, j):
    m = 3**(j+1)
    return pow(2, n, m) // (3**j) % 3

# For each s, find k_mod in [0, 2187) where pos 5-11 all fail
print("=== Level 1: positions 5-11 ===")
total_level1 = 0
failing_ks = {}  # s -> list of k values where pos 5-11 fail

for s in N5:
    fails = []
    for k in range(2187):
        r = s + 162 * k
        if r < 69:
            continue
        total_level1 += 1
        found = any(digit_mod(r, j+5) == 2 for j in range(7))
        if not found:
            fails.append(k)
    failing_ks[s] = fails
    print(f"  s={s:>3}: {2187} checked, {len(fails)} fail pos 5-11")

total_failing = sum(len(v) for v in failing_ks.values())
print(f"\nTotal level1 cases: {total_level1}")
print(f"Total failing (need level 2): {total_failing}")

# For level 2: for each failing (s, k_mod), find what positions 12-42 give digit 2
# AND figure out what k range we need
print("\n=== Level 2: positions 12-42 ===")
# For each failing (s, k_mod), the period for position j+5 is 3^(j+1)
# For position 12 (j=7): period = 3^8 = 6561
# So k_mod_6561 = k_mod (if k_mod < 6561) or k_mod % 6561

# But k ranges up to 59049 = 3^10
# Period for pos 12: 6561
# Period for pos 13: 19683
# Period for pos 14+: 59049+

# For each failing (s, k_mod_2187), find all k in [0, 59049) with k%2187 = k_mod_2187
# Then check which position covers them

# Actually, simpler: for each (s, k_mod_2187), we need that for ALL k with k%2187=k_mod_2187,
# there exists j >= 7 such that digit_mod(s+162k, j+5) = 2.

# Since digit at pos j+5 has period 3^(j+1) in k:
# - pos 12: period 6561 → k mod 6561 determines it
# - If k_mod_2187 works, then all k ≡ k_mod_2187 (mod 2187) with k mod 6561 in {k_mod_2187, k_mod_2187+2187, k_mod_2187+4374} work

# Actually let's just check ALL (s, k) pairs where k >= 2187 and pos 5-11 fail
# That's the "hard" cases
hard_cases = 0
hard_positions = {}
for s in N5:
    for k in range(2187, 59049):
        r = s + 162 * k
        found_low = any(digit_mod(r, j+5) == 2 for j in range(7))
        if not found_low:
            hard_cases += 1
            # Find first position 12-42 with digit 2
            for j in range(7, 38):
                if digit_mod(r, j+5) == 2:
                    pos = j + 5
                    hard_positions[pos] = hard_positions.get(pos, 0) + 1
                    break

print(f"Hard cases (k >= 2187, no pos 5-11): {hard_cases}")
print(f"Hard position distribution:")
for p in sorted(hard_positions.keys()):
    print(f"  pos {p}: {hard_positions[p]}")
