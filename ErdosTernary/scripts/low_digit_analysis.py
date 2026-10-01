#!/usr/bin/env python3
"""
Analyze oddTarget(d) mod 3^25 for d ≥ 71.

Key insight: for d ≥ 26, 3^(d-1) ≡ 0 (mod 3^25), so
oddTarget(d) mod 3^25 = ((2^(d+4+d%2)-1)/3) mod 2^(d+4) mod 3^25

The mod 2^(d+4) operation complicates things, but we can compute
oddTarget(d) mod 3^25 directly and look for structure.
"""

MOD3_25 = 3**25

def oddTarget(d):
    k = d + 4
    delta = d % 2
    val = (2**(k + delta) - 1) // 3
    t = (val - 3**(d-1)) % (2**k)
    return t

def digit3(n, i):
    return (n // (3**i)) % 3

def has_low_digit2(d):
    t = oddTarget(d)
    for j in range(25):
        if digit3(t, j) == 2:
            return True
    return False

# 1. Verify for large range
print("=== Verifying d=71..10000 ===")
for d in range(71, 10001):
    if not has_low_digit2(d):
        print(f"  FAIL at d={d}!")
        break
else:
    print("  All pass!")

# 2. Check if oddTarget(d) mod 3^25 is eventually periodic
# The key: for d ≥ 26, oddTarget(d) mod 3^25 depends on:
# - (2^(d+4+d%2)-1)/3 mod 2^(d+4)
# - 3^(d-1) mod 2^(d+4)
# Since the modulus 2^(d+4) changes with d, oddTarget(d) is NOT periodic.
# But maybe oddTarget(d) mod 3^25 IS periodic (since we only care about mod 3^25)?

vals = [oddTarget(d) % MOD3_25 for d in range(71, 71+500)]
print(f"\n=== Checking periodicity of oddTarget(d) mod 3^25 ===")
for period in range(1, 251):
    if all(vals[i] == vals[i + period] for i in range(len(vals) - period)):
        print(f"Period = {period}")
        break
else:
    print("Period > 250")

# 3. Key insight: The proof might work by showing that for d ≥ 71,
# oddTarget(d) mod 3^25 is ALWAYS in a set that has digit 2.
# Let's characterize the set of "bad" values (no digit 2 in positions 0..24).
# These are numbers n with 0 ≤ n < 3^25 and all base-3 digits ≤ 1.
# There are 2^25 such numbers. Let's check if any oddTarget(d) mod 3^25 is bad.

print(f"\n=== Checking if any oddTarget(d) mod 3^25 is 'bad' (no digit 2) ===")
bad_count = 0
for d in range(71, 10001):
    t = oddTarget(d) % MOD3_25
    is_bad = all(digit3(t, j) != 2 for j in range(25))
    if is_bad:
        bad_count += 1
        print(f"  BAD at d={d}: {t}")
print(f"Total bad: {bad_count}")

# 4. Try a different approach: prove that oddTarget(d) mod 3^25
# always has a digit 2 by using the structure of (2^n-1)/3.
# 
# For d even (δ=0): oddTarget(d) = ((2^(d+4)-1)/3 - 3^(d-1)) mod 2^(d+4)
# For d odd (δ=1): oddTarget(d) = ((2^(d+5)-1)/3 - 3^(d-1)) mod 2^(d+4)
#
# Let's compute oddTarget(d) mod 3^j for j=1..25 and see the pattern.

print(f"\n=== Digit patterns for d=71..80 ===")
for d in range(71, 81):
    t = oddTarget(d)
    digits = [digit3(t, j) for j in range(25)]
    has2 = any(dd == 2 for dd in digits)
    first2 = next((j for j, dd in enumerate(digits) if dd == 2), -1)
    print(f"  d={d}: first2={first2}, digits[0:12]={digits[:12]}")
