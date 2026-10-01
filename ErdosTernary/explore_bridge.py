#!/usr/bin/env python3
"""
Computational exploration of the Erdős conjecture bridge.
Compute epsilon values, Ostrowski vectors, and N_K survivors for K=12..16.
Search for deterministic conditions implying {rα} ∉ C30Lead.
"""

import math
from fractions import Fraction

# ─── CF of log₃(2) = [0; 1,1,1,2,2,3,1,5,2,23,2,2,1,1,55,...] ───
cf_coeffs = [0, 1, 1, 1, 2, 2, 3, 1, 5, 2, 23, 2, 2, 1, 1, 55]
alpha = math.log(2) / math.log(3)  # log₃(2)

# ─── Convergent numerators/denominators ───
def convergents(cf):
    """Return list of (num, den) for each convergent."""
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
nums = [c[0] for c in convs]  # numerators
dens = [c[1] for c in convs]  # denominators (= Q_k)

# ─── Epsilon values: ε_k = dens_k * α - nums_k ───
epsilons = [dens[k] * alpha - nums[k] for k in range(len(cf_coeffs))]

print("=== Convergents and Epsilon Values ===")
print(f"{'k':>3} {'CF':>4} {'num':>10} {'den':>12} {'ε_k':>20} {'|ε_k|':>20} {'1/Q(k+1)':>20}")
for k in range(len(cf_coeffs)):
    bound = 1.0 / dens[k+1] if k+1 < len(dens) else float('inf')
    print(f"{k:3d} {cf_coeffs[k]:4d} {nums[k]:10d} {dens[k]:12d} {epsilons[k]:20.15f} {abs(epsilons[k]):20.15f} {bound:20.15f}")

print(f"\nα = {alpha:.15f}")

# ─── Ostrowski representation (greedy) ───
def ostrowski_rep(r):
    """Compute Ostrowski representation of r using Q_k = dens_k.
    Returns list of (k, b_k) for nonzero coefficients."""
    if r == 0:
        return []
    # Find topIdx: largest t with Q_t ≤ r
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

# ─── N_K computation ───
def has_trailing_digit_2(val, K):
    """Check if val has any digit 2 in last K ternary digits."""
    for i in range(K):
        if (val // (3**i)) % 3 == 2:
            return True
    return False

def compute_NK(K):
    """Compute N_K = {r in [0, u_K) : 2^r mod 3^K has no digit 2}."""
    uK = 2 * 3**(K-1)
    modulus = 3**K
    result = []
    pow2r = 1  # 2^0 = 1
    for r in range(uK):
        if not has_trailing_digit_2(pow2r, K):
            result.append(r)
        pow2r = (pow2r * 2) % modulus
    return result

# ─── C30Lead check ───
def is_C30Lead(x):
    """Check if x ∈ C30Lead: 0 ≤ x < 1 and leading 30 ternary digits of 3^(x+29) have no 2."""
    if x < 0 or x >= 1:
        return False
    # Compute floor(3^(x+29))
    val = int(math.floor(3**(x + 29)))
    # Check first 30 ternary digits
    for k in range(30):
        digit = (val // (3**k)) % 3
        if digit == 2:
            return False
    return True

# ─── Main exploration ───
print("\n" + "="*80)
print("=== N_K SURVIVORS AND OSTROWSKI ANALYSIS ===")
print("="*80)

# For each K, compute N_K and analyze survivors
for K in range(12, 17):
    NK = compute_NK(K)
    uK = 2 * 3**(K-1)
    print(f"\n{'='*60}")
    print(f"K = {K}, u_K = {uK}, |N_K| = {len(NK)}")
    print(f"{'='*60}")
    
    survivors_ge23 = [r for r in NK if r >= 23]
    print(f"Survivors with r ≥ 23: {len(survivors_ge23)}")
    
    in_C30 = 0
    not_in_C30 = 0
    example_in = None
    example_not = None
    
    for r in survivors_ge23:
        x = (r * alpha) % 1.0  # {rα}
        in_set = is_C30Lead(x)
        if in_set:
            in_C30 += 1
            if example_in is None:
                example_in = r
        else:
            not_in_C30 += 1
            if example_not is None:
                example_not = r
    
    print(f"  {{rα}} ∈ C30Lead: {in_C30}")
    print(f"  {{rα}} ∉ C30Lead: {not_in_C30}")
    if example_in:
        print(f"  Example r with {{rα}} ∈ C30Lead: {example_in}")
    if example_not:
        print(f"  Example r with {{rα}} ∉ C30Lead: {example_not}")
    
    # Show Ostrowski vectors for a few survivors
    print(f"\n  Ostrowski vectors for first 10 survivors r ≥ 23:")
    for r in survivors_ge23[:10]:
        rep = ostrowski_rep(r)
        x = (r * alpha) % 1.0
        c30 = is_C30Lead(x)
        # Compute signed error sum
        error_sum = sum(b * epsilons[k] for k, b in rep)
        frac_error = error_sum % 1.0  # fractional part
        rep_str = ", ".join(f"b_{k}={b}" for k, b in rep)
        max_k = max(k for k, b in rep) if rep else 0
        nonzero_above5 = [(k, b) for k, b in rep if k >= 5 and b > 0]
        print(f"    r={r:5d}: [{rep_str}]  max_k={max_k}  "
              f"ε_sum={error_sum:+.12f}  {{rα}}={x:.12f}  C30={'Y' if c30 else 'N'}  "
              f"highCoeffs={nonzero_above5}")

# ─── Detailed analysis: what distinguishes C30 survivors? ───
print("\n" + "="*80)
print("=== DETAILED ANALYSIS: WHAT DISTINGUISHES C30 vs NON-C30 ===")
print("="*80)

# Use K=12 for detailed analysis
K = 12
NK = compute_NK(K)
survivors_ge23 = [r for r in NK if r >= 23]

c30_groups = {}  # Ostrowski pattern -> list of r
non_c30_groups = {}

for r in survivors_ge23:
    rep = ostrowski_rep(r)
    x = (r * alpha) % 1.0
    in_set = is_C30Lead(x)
    pattern = tuple((k, b) for k, b in rep if k >= 1)
    if in_set:
        c30_groups.setdefault(pattern, []).append(r)
    else:
        non_c30_groups.setdefault(pattern, []).append(r)

print(f"\nDistinct Ostrowski patterns (k≥1) for C30 survivors: {len(c30_groups)}")
print(f"Distinct Ostrowski patterns (k≥1) for NON-C30 survivors: {len(non_c30_groups)}")

# Patterns only in C30 or only in NON-C30
c30_only = set(c30_groups.keys()) - set(non_c30_groups.keys())
non_c30_only = set(non_c30_groups.keys()) - set(c30_groups.keys())
both = set(c30_groups.keys()) & set(non_c30_groups.keys())

print(f"\nPatterns ONLY in C30Lead: {len(c30_only)}")
for p in list(c30_only)[:5]:
    print(f"  {p}: r = {c30_groups[p][:5]}")

print(f"\nPatterns ONLY in NON-C30Lead: {len(non_c30_only)}")
for p in list(non_c30_only)[:5]:
    print(f"  {p}: r = {non_c30_groups[p][:5]}")

print(f"\nPatterns in BOTH: {len(both)}")
for p in list(both)[:5]:
    print(f"  {p}:")
    print(f"    C30:     {c30_groups[p][:5]}")
    print(f"    Non-C30: {non_c30_groups[p][:5]}")

# ─── Trailing residue analysis ───
print("\n" + "="*80)
print("=== TRAILING RESIDUE ANALYSIS ===")
print("="*80)

# For each r, compute r mod something meaningful
# The trailing K digits of 2^r in base 3 determine membership in N_K
# What about r mod Q_k for various k?

for modulus_label, modulus_fn in [
    ("r mod 2", lambda r: r % 2),
    ("r mod 3", lambda r: r % 3),
    ("r mod 4", lambda r: r % 4),
    ("r mod 8", lambda r: r % 8),
    ("r mod 16", lambda r: r % 16),
    ("r mod 5", lambda r: r % 5),
    ("r mod 10", lambda r: r % 10),
]:
    print(f"\n--- {modulus_label} ---")
    c30_by_mod = {}
    non_c30_by_mod = {}
    for r in survivors_ge23:
        x = (r * alpha) % 1.0
        in_set = is_C30Lead(x)
        m = modulus_fn(r)
        if in_set:
            c30_by_mod.setdefault(m, 0)
            c30_by_mod[m] += 1
        else:
            non_c30_by_mod.setdefault(m, 0)
            non_c30_by_mod[m] += 1
    
    all_mods = sorted(set(list(c30_by_mod.keys()) + list(non_c30_by_mod.keys())))
    for m in all_mods:
        c = c30_by_mod.get(m, 0)
        nc = non_c30_by_mod.get(m, 0)
        total = c + nc
        if total > 0:
            print(f"  {modulus_label}={m}: C30={c:3d}, Non-C30={nc:3d}, "
                  f"Non-C30%={100*nc/total:.1f}%")

# ─── Ostrowski coefficient patterns ───
print("\n" + "="*80)
print("=== OSTROWSKI COEFFICIENT PATTERN ANALYSIS ===")
print("="*80)

# Focus on which high-index coefficients are nonzero
for r in survivors_ge23[:50]:
    rep = ostrowski_rep(r)
    x = (r * alpha) % 1.0
    in_set = is_C30Lead(x)
    nonzero = [k for k, b in rep if b > 0]
    error = sum(b * epsilons[k] for k, b in rep)
    high_nonzero = [k for k in nonzero if k >= 5]
    
    if in_set:
        marker = "*"
    else:
        marker = " "
    
    print(f"  {marker} r={r:5d}: nonzero_k={nonzero}, high≥5={high_nonzero}, "
          f"ε_sum={error:+.12f}, {{rα}}={x:.10f}")

# ─── Check: is there a simple threshold on ε_sum? ───
print("\n" + "="*80)
print("=== EPSILON SUM DISTRIBUTION ===")
print("="*80)

c30_sums = []
non_c30_sums = []
for r in survivors_ge23:
    rep = ostrowski_rep(r)
    x = (r * alpha) % 1.0
    in_set = is_C30Lead(x)
    error = sum(b * epsilons[k] for k, b in rep)
    if in_set:
        c30_sums.append(error)
    else:
        non_c30_sums.append(error)

if c30_sums:
    print(f"C30 ε_sum: min={min(c30_sums):+.12f}, max={max(c30_sums):+.12f}, "
          f"mean={sum(c30_sums)/len(c30_sums):+.12f}")
if non_c30_sums:
    print(f"Non-C30 ε_sum: min={min(non_c30_sums):+.12f}, max={max(non_c30_sums):+.12f}, "
          f"mean={sum(non_c30_sums)/len(non_c30_sums):+.12f}")

# ─── Check: is {rα} close to specific values? ───
print("\n" + "="*80)
print("=== FRACTIONAL PART DISTRIBUTION ===")
print("="*80)

c30_fracs = []
non_c30_fracs = []
for r in survivors_ge23:
    x = (r * alpha) % 1.0
    in_set = is_C30Lead(x)
    if in_set:
        c30_fracs.append(x)
    else:
        non_c30_fracs.append(x)

if c30_fracs:
    c30_fracs.sort()
    print(f"C30 {{rα}}: min={min(c30_fracs):.10f}, max={max(c30_fracs):.10f}, "
          f"count={len(c30_fracs)}")
    # Show distribution in buckets
    buckets = [0]*10
    for x in c30_fracs:
        b = min(int(x * 10), 9)
        buckets[b] += 1
    print(f"  Bucket distribution: {buckets}")

if non_c30_fracs:
    non_c30_fracs.sort()
    print(f"Non-C30 {{rα}}: min={min(non_c30_fracs):.10f}, max={max(non_c30_fracs):.10f}, "
          f"count={len(non_c30_fracs)}")
    buckets = [0]*10
    for x in non_c30_fracs:
        b = min(int(x * 10), 9)
        buckets[b] += 1
    print(f"  Bucket distribution: {buckets}")

# ─── Check: is C30Lead really populated? ───
print("\n" + "="*80)
print("=== C30Lead VALIDATION ===")
print("="*80)

# How many x in [0,1) are in C30Lead?
# Should be (2/3)^30 ≈ 1.32e-5 of [0,1)
# But we're checking discrete r values, not all x
print(f"Expected C30Lead density: {(2/3)**30:.10f}")
print(f"C30Lead count among survivors: {len(c30_sums)} / {len(survivors_ge23)} = "
      f"{len(c30_sums)/len(survivors_ge23):.10f}" if survivors_ge23 else "N/A")

# Show some actual C30Lead x values
if c30_fracs:
    print(f"\nActual C30Lead x values (first 20):")
    for x in c30_fracs[:20]:
        val = int(math.floor(3**(x + 29)))
        ternary_digits = []
        v = val
        for _ in range(30):
            ternary_digits.append(v % 3)
            v //= 3
        print(f"  x={x:.12f}, 3^(x+29)={val}, digits={ternary_digits}")
