#!/usr/bin/env python3
"""
Compute N_16: residues r in [0, u_16) where u_16 = 2*3^15,
such that 2^r mod 3^16 has NO digit 2 in its ternary representation.
Then verify bridge: for all r in N_16 \ {0,2,8}, 2^r mod 3^50 has digit 2 in positions 16..49.

Uses streaming modular exponentiation to avoid recomputing from scratch.
"""

def has_digit2_in_range(val, lo, hi):
    """Check if val has digit 2 in ternary positions lo..hi-1."""
    for i in range(lo, hi):
        if (val // (3**i)) % 3 == 2:
            return True
    return False

def compute_NK_and_verify(K):
    """Compute N_K and verify bridge in one pass."""
    period = 2 * 3**(K-1)
    modulus_K = 3**K
    mod50 = 3**50

    NK = []
    pow2r_modK = 1  # 2^0 mod 3^K
    pow2r_mod50 = 1  # 2^0 mod 3^50

    special = {0, 2, 8}

    for r in range(period):
        # Check if 2^r mod 3^K has digit 2
        has_digit2_K = False
        temp = pow2r_modK
        for i in range(K):
            if temp % 3 == 2:
                has_digit2_K = True
                break
            temp //= 3

        if not has_digit2_K:
            NK.append(r)

        # Advance: 2^(r+1) mod 3^K and mod 3^50
        pow2r_modK = (pow2r_modK * 2) % modulus_K
        pow2r_mod50 = (pow2r_mod50 * 2) % mod50

    # Now verify bridge
    return NK

K = 16
uK = 2 * 3**(K-1)
modulus_K = 3**K
mod50 = 3**50

print(f"Computing N_{K}, u_{K} = {uK}...")

NK = []
special = {0, 2, 8}
pow2r_modK = 1
pow2r_mod50 = 1

for r in range(uK):
    # Check digit 2 in 2^r mod 3^K
    has_digit2_K = False
    temp = pow2r_modK
    for i in range(K):
        if temp % 3 == 2:
            has_digit2_K = True
            break
        temp //= 3

    if not has_digit2_K:
        NK.append(r)

    pow2r_modK = (pow2r_modK * 2) % modulus_K
    pow2r_mod50 = (pow2r_mod50 * 2) % mod50

print(f"|N_{K}| = {len(NK)}")
print(f"First 20: {NK[:20]}")

check_values = [r for r in NK if r not in special]
print(f"|N_{K} \\ {{0,2,8}}| = {len(check_values)}")

# Verify bridge: recompute 2^r mod 3^50 and check positions K..49
pow2r_mod50 = 1
failures = []
for r in range(uK):
    if r in special:
        pow2r_mod50 = (pow2r_mod50 * 2) % mod50
        continue
    if r in NK:
        if not has_digit2_in_range(pow2r_mod50, K, 50):
            failures.append(r)
    pow2r_mod50 = (pow2r_mod50 * 2) % mod50

if failures:
    print(f"FAILED: {len(failures)} values: {failures[:10]}")
else:
    print("ALL PASSED: checkMiddleBridgeList(NK_16, 16) = true")
