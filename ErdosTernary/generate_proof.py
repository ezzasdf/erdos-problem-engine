#!/usr/bin/env python3
"""Generate certificate table and Lean proof code for the r >= 48 case."""

import math

def min_j_mod_pow(r, max_j=20):
    """Find min j >= 5 with digit_j(2^r) = 2, using modular exponentiation."""
    for j in range(5, max_j + 1):
        period = 2 * 3**j
        r_mod = r % period
        mod_j = 3**(j + 1)
        pow_mod = pow(2, r_mod, mod_j)
        digit = (pow_mod // (3**j)) % 3
        if digit == 2:
            return j
    return None

N5_even = [0, 2, 8, 20, 24, 26, 54, 56, 62, 72, 74, 78, 80, 96, 126, 150]

# Generate certificate: for each N5 residue s and each k%19683,
# find the witness j such that digit_j(2^(s+162*(k%19683))) = 2.
#
# Key constraint: for the periodicity reduction to work,
# we need j <= d+4 where d is the split depth.
# At depth 9 (k%19683): j <= 13.
#
# But we also need j <= 20 for norm_num capacity.
# And the modulus 3^(j+1) is at most 3^21 ~ 10^10.

# For depth 9, j must be <= 13 for periodicity.
# For j > 13, we need deeper depth. But let's first check:
# how many cases at depth 9 have min_j > 13?

print("=== Cases at depth 9 needing j > 13 ===")
need_deeper = []
for s in N5_even:
    for m9 in range(19683):
        r = s + 162 * m9
        if r < 48:
            continue
        mj = min_j_mod_pow(r, max_j=20)
        if mj is None:
            print(f"  BUG: s={s}, m9={m9}, r={r}")
        elif mj > 13:
            need_deeper.append((s, m9, r, mj))

print(f"Total needing j > 13: {len(need_deeper)}")

# Group by needed j
from collections import Counter
j_counts = Counter(mj for _, _, _, mj in need_deeper)
print(f"By j: {sorted(j_counts.items())}")

# For each j > 13, what depth is needed? depth = j - 4
for j_val in sorted(j_counts.keys()):
    depth_needed = j_val - 4
    P = 3**depth_needed
    print(f"  j={j_val}: need depth {depth_needed} (k%{P}), {j_counts[j_val]} cases")

# The periodicity modulus for j is 2*3^j.
# At depth d, k is split mod 3^d.
# r mod 2*3^j = (s + 162*k) mod 2*3^j
# Since 162 = 2*3^4, for j >= 4:
#   r mod 2*3^j = (s + 162*(k mod 3^(j-4))) mod 2*3^j
# So we need k mod 3^(j-4) to be fixed.
# At depth d, k mod 3^d is fixed, so k mod 3^(j-4) is fixed iff d >= j-4.

# This means: for j <= 13, depth 9 suffices (9 >= j-4 for j <= 13).
# For j = 14, need depth >= 10.
# For j = 15, need depth >= 11.
# ...
# For j = 20, need depth >= 16.

# Alternative approach: instead of going deeper, we can increase the
# residue range. At depth d, the residue is s + 162 * (k_class mod 3^d).
# For d = j-4, the residue ranges up to 150 + 162*(3^(j-4) - 1).
# For j=20, d=16: max residue = 150 + 162*(3^16 - 1) ~ 7.1 billion.
# 2^7.1B mod 3^21 is computable (modular exponentiation), but the
# residue itself is huge. We can't enumerate all of them.

# BETTER APPROACH: for j > 13, we don't need to go deeper.
# We just need: for each (s, k%3^9) pair that needs j > 13,
# find an ALTERNATIVE j' <= 13 that works.
# If no such j' exists, then we truly need j > 13.

# But we already checked: at depth 9, some residues have min_j > 13.
# So there's no alternative j' <= 13 for those residues.

# REVISED APPROACH: For the 831 cases needing j > 13,
# we go to depth 10 (k%3^10 = k%59049).
# At depth 10, the residue is s + 162 * (k_class mod 59049).
# For j = 14: need depth >= 10. 10 >= 14-4 = 10. OK.
# Max residue at depth 10: 150 + 162*59048 ~ 9.6M.
# 2^9.6M mod 3^15 is computable.

# For cases still needing j > 14 at depth 10, go to depth 11. Etc.

print("\n=== Cascading depth analysis ===")
# For each (s, m9) pair that needs j > 13 at depth 9,
# check what happens at depth 10.
count_still_need_deeper = 0
for s, m9, r_orig, mj_needed in need_deeper:
    # At depth 10, k_class = m9 * 3 + m10 for m10 in {0,1,2}
    # Each gives a different residue
    found = False
    for m10 in range(3):
        k_class_10 = m9 * 3 + m10
        r_10 = s + 162 * (k_class_10 % 59049)
        mj_10 = min_j_mod_pow(r_10, max_j=14)
        if mj_10 is not None and mj_10 <= 14:
            found = True
            break
    if not found:
        count_still_need_deeper += 1

print(f"Cases still needing j > 14 at depth 10: {count_still_need_deeper}")
