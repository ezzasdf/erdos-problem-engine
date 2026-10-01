#!/usr/bin/env python3
"""
Targeted residue-class search: the critical test for B4.

Pick r₀ ∈ N₁₂, search r_n = r₀ + n×u₁₂ for C30Lead hits.
The sequence {r_n×α} is equidistributed, so it MUST enter C30Lead eventually.
If we don't find hits after a large search, there's a hidden constraint.
"""
import math
import sys

alpha = math.log(2) / math.log(3)
u12 = 2 * 3**11  # = 354294

def leading_30_digits(r):
    x = (r * alpha) % 1.0
    val = int(math.floor(3**(x + 29)))
    digits = []
    v = val
    for _ in range(30):
        digits.append(v % 3)
        v //= 3
    return digits

def has_no_digit_2(digits):
    return all(d != 2 for d in digits)

def in_C30Lead(r):
    return has_no_digit_2(leading_30_digits(r))

# ─── Find N₁₂ survivors ───
print("="*80)
print("TARGETED RESIDUE-CLASS SEARCH")
print("="*80)
print(f"Period T = u₁₂ = {u12}")
print(f"α = {alpha:.15f}")
print(f"T×α = {u12*alpha:.15f}")
print(f"T×α mod 1 = {(u12*alpha) % 1:.15f}")
print()

# Find N₁₂ survivors
modulus = 3**12
NK = []
pow2r = 1
for r in range(u12):
    has2 = False
    v = pow2r
    for i in range(12):
        if v % 3 == 2:
            has2 = True
            break
        v //= 3
    if not has2:
        NK.append(r)
    pow2r = (pow2r * 2) % modulus

survivors = [r for r in NK if r >= 23]
print(f"N₁₂ survivors r ≥ 23: {len(survivors)}")
print(f"First 10: {survivors[:10]}")
print()

# ─── Pick residue classes to search ───
# Use several r₀ values to be thorough
r0_candidates = survivors[:5]  # first 5 survivors

MAX_N = 5_000_000  # search up to n = 5 million

print(f"Searching r_n = r₀ + n×{u12} for n = 0..{MAX_N:,}")
print(f"Maximum r checked: {r0_candidates[0] + MAX_N * u12:,.0f}")
print(f"Expected C30 hits per residue class: {MAX_N * (2/3)**30:.1f}")
print()

total_hits = 0
total_checked = 0

for r0 in r0_candidates:
    hits = []
    n = 0
    while n <= MAX_N:
        r = r0 + n * u12
        if in_C30Lead(r):
            hits.append((n, r))
            if len(hits) <= 5:
                x = (r * alpha) % 1.0
                lead = leading_30_digits(r)
                print(f"  HIT! r₀={r0}, n={n}, r={r:,}, {{rα}}={x:.12f}")
                print(f"    Leading 30: {''.join(str(d) for d in lead)}")
        n += 1
        if n % 1_000_000 == 0:
            print(f"  r₀={r0}: checked n up to {n:,} ({len(hits)} hits so far)", 
                  file=sys.stderr)
    
    total_hits += len(hits)
    total_checked += MAX_N + 1
    
    if hits:
        print(f"  r₀={r0}: {len(hits)} C30 hits found!")
        for n, r in hits[:10]:
            print(f"    n={n:,}, r={r:,}")
    else:
        print(f"  r₀={r0}: NO C30 hits in {MAX_N+1:,} values")

print(f"\n{'='*80}")
print(f"TOTAL: {total_hits} C30 hits in {total_checked:,} values")
print(f"Expected: {total_checked * (2/3)**30:.1f}")
print(f"{'='*80}")

# ─── Also search with negative n (r₀ - n×u₁₂) for small r ───
print(f"\n--- Checking negative n (small r values) ---")
for r0 in r0_candidates:
    hits = []
    for n in range(1, 1000):
        r = r0 - n * u12
        if r < 23:
            break
        if in_C30Lead(r):
            hits.append((n, r))
    if hits:
        print(f"  r₀={r0}: {len(hits)} hits at negative n")
    else:
        print(f"  r₀={r0}: no hits for n = -1..-999")

# ─── Final verdict ───
print(f"\n{'='*80}")
print("VERDICT")
print(f"{'='*80}")
if total_hits > 0:
    print(f"COUNTEREXAMPLE FOUND! B4 bridge is DISPROVEN.")
    print(f"The theorem r ∈ N₁₂ ∧ r ≥ 23 ⟹ {{rα}} ∉ C30Lead is FALSE.")
else:
    print(f"No counterexamples found in {total_checked:,} values.")
    print(f"Expected hits: {total_checked * (2/3)**30:.1f}")
    if total_checked * (2/3)**30 > 10:
        print(f"EXPECTED > 10 HITS BUT FOUND 0. Strong evidence of hidden constraint.")
    elif total_checked * (2/3)**30 > 1:
        print(f"Expected ~{total_checked * (2/3)**30:.0f} hits, found 0. Suggestive but not conclusive.")
    else:
        print(f"Expected < 1 hit. Need larger search.")
