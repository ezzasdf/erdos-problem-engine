#!/usr/bin/env python3
"""Verify: does digitMod(r' + P*q, j) = digitMod(r', j) for j < 15?
If yes, the Python analysis should be wrong and positions 5-14 are invariant."""

N5_EVEN = [0, 2, 8, 20, 24, 26, 54, 56, 62, 72, 74, 78, 80, 96, 126, 150]
P = 162 * 59049

def digitMod(r, j):
    m = 3 ** (j + 1)
    return (pow(2, r, m) // (3 ** j)) % 3

# Pick a specific case and check whether transfer holds
s, k = 0, 10890
r_prime = s + 162 * k

print(f"r_prime = {r_prime}")
print()
for q in [1, 203, 500]:
    r_full = r_prime + P * q
    print(f"q={q}: r_full = {r_full}")
    for j in range(5, 15):
        d_full = digitMod(r_full, j)
        d_prime = digitMod(r_prime, j)
        match = "==" if d_full == d_prime else "!="
        print(f"  j={j}: digitMod(r_full)={d_full}, digitMod(r')={d_prime} {match}")
    print()

# Also: is the transfer theoretically guaranteed?
# v_3(2^P - 1) = 15, so 2^P ≡ 1 (mod 3^15)
# Thus 2^r_full = 2^(r' + Pq) = 2^r' * (2^P)^q ≡ 2^r' (mod 3^j) for j ≤ 15
print("Theoretical check: 2^P mod 3^15 =", pow(2, P, 3**15))
print("Expected: 1")
print("2^P mod 3^16 =", pow(2, P, 3**16))
print("Expected: != 1 (since v_3(2^P-1) = 15, not 16)")
