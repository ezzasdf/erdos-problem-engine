#!/usr/bin/env python3
"""Analyze optimal split strategy for n5_digitMod_covers."""
N5 = [0, 2, 8, 20, 24, 26, 54, 56, 62, 72, 74, 78, 80, 96, 126, 150]

def digit_mod(n, j):
    m = 3**(j+1)
    return pow(2, n, m) // (3**j) % 3

# Strategy A: Split by residue (16 native_decides, each ~59K cases)
print("=== Strategy A: Split by residue ===")
for s in N5:
    count = sum(1 for k in range(59049) if s + 162*k >= 69)
    print(f"  s={s:>3}: {count} cases")

# Strategy B: Two-level split
# Level 1: For each (s, k), check pos 5-11 first
# Level 2: For remaining, check pos 12-42 with a smaller k range

# Strategy C: Split by k range
# For k in [0, 2187): covers all cases where pos 5-11 suffice
# For k in [2187, 59049): need to check all positions

print("\n=== Strategy C: Split by k range ===")
# How many (s,k) pairs need the full range?
full_range_needed = 0
for s in N5:
    for k in range(2187, 59049):
        r = s + 162 * k
        found = any(digit_mod(r, j+5) == 2 for j in range(7))
        if not found:
            full_range_needed += 1
print(f"Cases needing k >= 2187: {full_range_needed}")

# Strategy D: Per-residue x per-position decomposition
# For each s and each position p (5-11), the digit is periodic in k with period 3^(p-4)
# So we only need k in [0, 3^(p-4)) per (s, p) pair
# Total cases: sum over s of sum over positions of period
print("\n=== Strategy D: Per-position periodicity ===")
for s in N5[:3]:  # just first 3 for brevity
    total_per_s = 0
    for j in range(7):  # positions 5-11
        period = 3**(j+1)  # period in k for position j+5
        total_per_s += period
    print(f"  s={s}: {total_per_s} cases for pos 5-11 (vs 59049 full)")

# Strategy E: What if we just prove it for k in [0, max_period)?
# For positions 5-42, the max_period for position 42 is huge
# But we only need ONE position to have digit 2

# Check: for each s, how many unique (k mod period) patterns exist
# across positions 5-11?
print("\n=== Unique k patterns for pos 5-11 ===")
for s in N5[:3]:
    pattern = {}
    for k in range(59049):
        r = s + 162 * k
        digits = tuple(digit_mod(r, j+5) for j in range(7))
        if digits not in pattern:
            pattern[digits] = k
    print(f"  s={s}: {len(pattern)} unique digit patterns (of 59049 k values)")
