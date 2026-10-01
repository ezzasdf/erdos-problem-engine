#!/usr/bin/env python3
"""Verify that for each N5 residue s, checking k in [0, 2187) suffices
for positions 5-11 (i.e., j in range 7)."""
from math import gcd

N5 = [0, 2, 8, 20, 24, 26, 54, 56, 62, 72, 74, 78, 80, 96, 126, 150]

def digit_mod(n, j):
    """digitMod n j: compute (2^n % 3^(j+1)) // 3^j % 3"""
    m = 3**(j+1)
    return pow(2, n, m) // (3**j) % 3

# Check: for each s and each k in [0, 2187), is there j in [0,7) with digit=2?
period = 2187  # = 3^7, LCM of periods for positions 5-11
all_covered = True
missing = 0
total = 0

for s in N5:
    for k in range(period):
        r = s + 162 * k
        if r < 69:
            continue
        total += 1
        found = False
        for j in range(7):  # positions 5-11
            if digit_mod(r, j + 5) == 2:
                found = True
                break
        if not found:
            missing += 1
            all_covered = False
            if missing <= 5:
                print(f"  MISSING: s={s}, k={k}, r={r}")

print(f"\nTotal (s,k) pairs with r>=69: {total}")
print(f"Missing (no digit2 in pos 5-11): {missing}")
print(f"All covered by pos 5-11: {all_covered}")

# Also check full range [0, 59049)
print("\n--- Full range check ---")
missing_full = 0
total_full = 0
for s in N5:
    for k in range(59049):
        r = s + 162 * k
        if r < 69:
            continue
        total_full += 1
        found = False
        for j in range(7):
            if digit_mod(r, j + 5) == 2:
                found = True
                break
        if not found:
            missing_full += 1
            if missing_full <= 5:
                print(f"  MISSING: s={s}, k={k}, r={r}")
                # Show which positions 5-11 have
                for jj in range(7):
                    print(f"    pos {jj+5}: digit={digit_mod(r, jj+5)}")

print(f"\nTotal (s,k) pairs (full range): {total_full}")
print(f"Missing (pos 5-11 only, full range): {missing_full}")
