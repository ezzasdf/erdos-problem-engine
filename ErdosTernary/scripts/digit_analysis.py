#!/usr/bin/env python3
"""Analyze oddTarget digit patterns for Lean proof strategy."""

def oddTarget(d):
    k = d + 4
    delta = d % 2
    val = (2**(k + delta) - 1) // 3
    t = (val - 3**(d-1)) % (2**k)
    return t

def digit3(n, i):
    return (n // (3**i)) % 3

# Check: for d >= 71, what is oddTarget(d) mod 3?
d0_vals = set()
for d in range(71, 501):
    d0_vals.add(oddTarget(d) % 3)
print("digit 0 values:", sorted(d0_vals))

# Check: what values of d mod P give digit 0 = 2?
print("\nd mod 6 -> digit 0 of oddTarget:")
for r in range(6):
    vals = set()
    for d in range(71 + (r - 71 % 6) % 6, 200, 6):
        vals.add(oddTarget(d) % 3)
    print(f"  d={r} mod 6: digit0 values = {sorted(vals)}")

# Check: what values of d mod 18 give digit 1 = 2 (when digit 0 != 2)?
print("\nd mod 18 -> digits 0,1 of oddTarget:")
for r in range(18):
    vals = set()
    for d in range(71 + (r - 71 % 18) % 18, 200, 18):
        v = oddTarget(d) % 9
        vals.add(v)
    # Check: for ALL these values, does at least one of digit0, digit1 = 2?
    all_covered = all(any(digit3(v, j) == 2 for j in range(2)) for v in vals)
    print(f"  d={r:2d} mod 18: values = {sorted(vals)}, all covered = {all_covered}")

# Check: what values of d mod 54 give digits 0,1,2 covering?
print("\nd mod 54 -> digits 0,1,2 of oddTarget:")
uncovered = 0
for r in range(54):
    vals = set()
    for d in range(71 + (r - 71 % 54) % 54, 500, 54):
        v = oddTarget(d) % 27
        vals.add(v)
    all_covered = all(any(digit3(v, j) == 2 for j in range(3)) for v in vals)
    if not all_covered:
        uncovered_vals = [v for v in vals if not any(digit3(v, j) == 2 for j in range(3))]
        uncovered += 1
        print(f"  d={r:2d} mod 54: UNCOVERED vals = {uncovered_vals}")

print(f"\nTotal uncovered residue classes mod 54: {uncovered}")
