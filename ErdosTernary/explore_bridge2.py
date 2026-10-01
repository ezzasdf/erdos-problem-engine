#!/usr/bin/env python3
"""
Phase 2 simplified: check small r, check N_K C30, find the mechanism.
"""
import math

alpha = math.log(2) / math.log(3)

cf_coeffs = [0, 1, 1, 1, 2, 2, 3, 1, 5, 2, 23, 2, 2, 1, 1, 55]

def convergents(cf):
    convs = []
    for i in range(len(cf)):
        if i == 0:
            num, den = cf[0], 1
        elif i == 1:
            num, den = cf[0]*cf[1]+1, cf[1]
        else:
            num = cf[i]*convs[-1][0] + convs[-2][0]
            den = cf[i]*convs[-1][1] + convs[-2][1]
        convs.append((num, den))
    return convs

convs = convergents(cf_coeffs)
nums = [c[0] for c in convs]
dens = [c[1] for c in convs]
epsilons = [dens[k] * alpha - nums[k] for k in range(len(cf_coeffs))]

def ostrowski_rep(r):
    if r == 0:
        return []
    top = 0
    for k in range(len(dens)):
        if dens[k] <= r:
            top = k
        else:
            break
    coeffs = {}
    remaining = r
    for k in range(top, -1, -1):
        if dens[k] <= remaining:
            b_k = remaining // dens[k]
            coeffs[k] = b_k
            remaining -= b_k * dens[k]
    return sorted(coeffs.items())

def is_C30Lead(x):
    if x < 0 or x >= 1:
        return False
    val = int(math.floor(3**(x + 29)))
    for k in range(30):
        if (val // (3**k)) % 3 == 2:
            return False
    return True

# ─── Check ALL r from 0 to 200: C30Lead check ───
print("=== ALL r from 0 to 200: C30Lead check ===")
c30_count = 0
non_c30_count = 0
for r in range(201):
    x = (r * alpha) % 1.0
    c30 = is_C30Lead(x)
    rep = ostrowski_rep(r)
    max_k = max(k for k, b in rep) if rep else 0
    high = [k for k, b in rep if k >= 5 and b > 0]
    error = sum(b * epsilons[k] for k, b in rep)
    
    if c30:
        c30_count += 1
    else:
        non_c30_count += 1
    
    if r <= 30 or c30 or r % 20 == 0:
        marker = "*" if c30 else " "
        print(f"{marker} r={r:5d}: max_k={max_k}, high≥5={str(high):>20}, ε_sum={error:+.12f}, {{rα}}={x:.12f}, C30={'Y' if c30 else 'N'}")

print(f"\nC30: {c30_count}, Non-C30: {non_c30_count}")

# ─── N_K survivors across K=8..16 ───
print("\n=== N_K survivors across K=8..16: C30Lead check ===")
for K in range(8, 17):
    uK = 2 * 3**(K-1)
    modulus = 3**K
    NK = []
    pow2r = 1
    for r in range(uK):
        has2 = False
        v = pow2r
        for i in range(K):
            if v % 3 == 2:
                has2 = True
                break
            v //= 3
        if not has2:
            NK.append(r)
        pow2r = (pow2r * 2) % modulus
    
    c30_in_NK = []
    for r in NK:
        x = (r * alpha) % 1.0
        if is_C30Lead(x):
            c30_in_NK.append(r)
    
    small_survivors = [r for r in NK if r not in (0, 2, 8) and r >= 1]
    print(f"K={K:2d}: |N_K|={len(NK):6d}, survivors (exc 0,2,8)={len(small_survivors):6d}, "
          f"C30Lead={c30_in_NK if c30_in_NK else 'NONE'}")

# ─── First digit 2 position analysis ───
print("\n=== First digit 2 position for N_K survivors (K=12) ===")
K = 12
uK = 2 * 3**(K-1)
modulus = 3**K
NK = []
pow2r = 1
for r in range(uK):
    has2 = False
    v = pow2r
    for i in range(K):
        if v % 3 == 2:
            has2 = True
            break
        v //= 3
    if not has2:
        NK.append(r)
    pow2r = (pow2r * 2) % modulus

first_pos_count = {}
for r in NK:
    if r < 23:
        continue
    x = (r * alpha) % 1.0
    val = int(math.floor(3**(x + 29)))
    for pos in range(30):
        digit = (val // (3**pos)) % 3
        if digit == 2:
            first_pos_count.setdefault(pos, 0)
            first_pos_count[pos] += 1
            break

print(f"  Total survivors r≥23: {sum(first_pos_count.values())}")
for pos in sorted(first_pos_count.keys()):
    print(f"    First digit 2 at pos {pos:2d}: {first_pos_count[pos]:4d} ({100*first_pos_count[pos]/sum(first_pos_count.values()):.1f}%)")

# ─── ε_sum bounds and C30Lead gap structure ───
print("\n=== ε_sum analysis for N_K survivors (K=12) ===")
sums = []
for r in NK:
    if r < 23:
        continue
    rep = ostrowski_rep(r)
    error = sum(b * epsilons[k] for k, b in rep)
    sums.append((error, r))

sums.sort()
print(f"  |ε_sum| range: [{min(abs(s) for s,_ in sums):.12f}, {max(abs(s) for s,_ in sums):.12f}]")
print(f"  ε_sum range: [{sums[0][0]:.12f}, {sums[-1][0]:.12f}]")

# Check: is there a gap around 0 that C30Lead occupies?
# C30Lead near 0: the interval [0, 1/3^30) is C30Lead (all digits 0)
# C30Lead near 1: the interval [(3^30-1)/3^30, 1) is C30Lead (all digits 1... wait no, 1 is not in [0,1))
# Actually: a = 0 has digits all 0 → [0, 1/3^30) ∈ C30Lead
# a = 1 has ternary 0...01 → [(1)/3^30, 2/3^30) ∈ C30Lead
# a = 3^29 has ternary 100...0 → [(3^29)/3^30, (3^29+1)/3^30) = [1/3, 1/3+1/3^30) ∈ C30Lead
# So C30Lead has intervals near 0, 1/3, 2/3, etc.

# The key: for N_K survivors, is {rα} always FAR from these intervals?
print(f"\n  1/3^30 = {1/3**30:.15e}")
print(f"  Smallest |ε_sum|: {min(abs(s) for s,_ in sums):.15e}")
print(f"  Ratio: {min(abs(s) for s,_ in sums) / (1/3**30):.2f}")

# Check distance to nearest C30Lead interval for closest survivors
print(f"\n  Closest to 0:")
for error, r in sums[:5]:
    x = (r * alpha) % 1.0
    print(f"    r={r:5d}: ε_sum={error:+.15f}, {{rα}}={x:.15f}")

print(f"\n  Closest to 1 (i.e., ε_sum near -1 or +1):")
for error, r in sums[-5:]:
    x = (r * alpha) % 1.0
    print(f"    r={r:5d}: ε_sum={error:+.15f}, {{rα}}={x:.15f}")

# ─── Check: is C30Lead actually populated for small r? ───
print("\n=== Small r with C30Lead (any r, not just N_K) ===")
c30_any = []
for r in range(500):
    x = (r * alpha) % 1.0
    if is_C30Lead(x):
        c30_any.append(r)

print(f"  r values with {{rα}} ∈ C30Lead (r < 500): {c30_any[:30]}")
print(f"  Count: {len(c30_any)}")

# ─── What does C30Lead look like near 0? ───
print("\n=== C30Lead intervals near 0 ===")
# a = 0: digits all 0 → interval [0, 1/3^30)
# a = 1: digits 0...01 → [1/3^30, 2/3^30)
# a = 3: digits 0...010 → [3/3^30, 4/3^30)
# a = 9: digits 0...0100 → [9/3^30, 10/3^30)
# These are all very close to 0

# The C30Lead set near 0 consists of intervals of width 1/3^30
# at positions that are ternary numbers with no digit 2.
# The smallest such positions are: 0, 1, 3, 9, 10, 12, 27, 28, 30, 36, ...
# (These are numbers whose ternary representation has only 0s and 1s)

# For N_K survivors, {rα} is a finite sum of ε_k terms.
# The ε_k alternate sign and decrease.
# The sum is constrained to a specific range.

# Let's check: what's the minimum |{rα} - a/3^30| for a with no digit 2?
print(f"  Checking distance from {{rα}} to nearest C30Lead interval for N_K survivors...")
min_dist = float('inf')
min_r = None
for error, r in sums[:100]:  # check closest to 0
    x = (r * alpha) % 1.0
    # The nearest C30Lead interval is at a/3^30 for some a
    # Since x is small, the nearest is at a=0, giving distance x
    # But also check a=1, a=3, etc.
    # Actually for small x, the nearest C30Lead is [0, 1/3^30), so distance = x if x > 1/3^30
    if x < 1/3**30:
        d = 0  # it's IN C30Lead
    else:
        d = x  # distance to [0, 1/3^30)
    if d < min_dist:
        min_dist = d
        min_r = r

print(f"  Min distance to C30Lead [0, 1/3^30): {min_dist:.15e}")
print(f"  At r = {min_r}")
print(f"  {min_r}α mod 1 = {(min_r * alpha) % 1.0:.15f}")

# Also check distance to C30Lead at 1/3 (a = 3^29)
third_dist = float('inf')
third_r = None
for error, r in sums:
    x = (r * alpha) % 1.0
    d = abs(x - 1/3)
    if d < third_dist:
        third_dist = d
        third_r = r
print(f"\n  Min distance to 1/3: {third_dist:.15e}")
print(f"  At r = {third_r}")
