#!/usr/bin/env python3
"""Investigate period of oddRoot(d) mod 3^j."""

def oddRoot(d):
    k = d + 4
    delta = d % 2
    val = (2**(k+delta) - 1) // 3
    return val - 3**(d-1)

def digit3(n, i):
    return (abs(n) // (3**i)) % 3

# Verify period 199 for mod 3^j
for j in [1, 2, 3, 5, 9]:
    mod = 3**j
    # Check all divisors of 199 (= prime) and also 197
    for p in [1, 197, 199]:
        ok = True
        for d in range(1, 500):
            if oddRoot(d) % mod != oddRoot(d + p) % mod:
                ok = False
                break
        if ok:
            print(f"  mod 3^{j}: p={p} works")

# The key question: what is the ACTUAL period?
# Compute oddRoot(d) mod 3^j for j=1..10, find minimal period
print("\nMinimal period of oddRoot(d) mod 3^j:")
for j in range(1, 11):
    mod = 3**j
    # For d large enough (d > j+1), 3^(d-1) ≡ 0 mod 3^j
    # So oddRoot(d) mod 3^j = g(d) mod 3^j for d > j+1
    # g(d) = (2^(d+4+d%2)-1)/3
    # Let n = d+4+d%2. Period of g mod 3^j = period of (2^n-1)/3 mod 3^j
    # which is period of 2^n mod 3^(j+1) (since /3 shifts by one power)
    # ord_{3^(j+1)}(2) = 2 * 3^j

    # But n = d+4+d%2, which is NOT simply periodic in d.
    # For even d: n = d+4, for odd d: n = d+5
    # So d → n maps even/odd to consecutive integers.

    # The sequence of n values for d=1,2,3,4,... is:
    # 6, 6, 8, 8, 10, 10, 12, 12, ...
    # (each value appears twice)

    # So g(d) for d=1,2,... depends on:
    # (2^6-1)/3, (2^6-1)/3, (2^8-1)/3, (2^8-1)/3, ...

    # The underlying period of (2^n-1)/3 mod 3^j is 2*3^j
    # But since each n appears twice, the effective period in d is also 2*3^j

    # However, 3^(d-1) mod 3^j = 0 for d-1 >= j, i.e., d >= j+1
    # For d < j+1, 3^(d-1) contributes

    # So for d >= j+2 (large enough), the period is 2*3^j
    period_theory = 2 * 3**j

    # Verify
    d_start = j + 10  # well past the transient
    ok = True
    for d in range(d_start, d_start + 500):
        if oddRoot(d) % mod != oddRoot(d + period_theory) % mod:
            ok = False
            print(f"  FAIL at d={d}")
            break
    if ok:
        print(f"  j={j:2d}: theoretical period 2*3^{j} = {period_theory} VERIFIED (for d >= {d_start})")
    else:
        # Search for actual period
        for p in range(1, period_theory * 3):
            ok2 = True
            for d in range(d_start, d_start + 200):
                if oddRoot(d) % mod != oddRoot(d + p) % mod:
                    ok2 = False
                    break
            if ok2:
                print(f"  j={j:2d}: actual period = {p} (theory said {period_theory})")
                break
        else:
            print(f"  j={j:2d}: no period found up to {period_theory * 3}")

# NOW THE KEY QUESTION: does the digit-2 property have a period?
# For each d, compute: the first j in 0..24 where digit3(abs(oddRoot(d)), j) = 2
print("\nDigit-2 witness position for d=1..100:")
for d in range(1, 101):
    r = abs(oddRoot(d))
    for j in range(25):
        if digit3(r, j) == 2:
            print(f"  d={d:3d}: j={j}", end="")
            break
    else:
        print(f"  d={d:3d}: NO digit 2 in pos 0..24!")
    if d % 10 == 0:
        print()
