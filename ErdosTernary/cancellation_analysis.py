#!/usr/bin/env python3
"""
Cancellation analysis: reverse-engineer the finite arithmetic theorem.
For each r ∈ N_K, record the full Ostrowski structure, epsilon contributions,
partial sums, and relationship to the leading ternary digit pattern.
"""
import math
from collections import defaultdict

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

def ostrowski_rep_full(r):
    """Return full Ostrowski coefficient vector up to index 15."""
    if r == 0:
        return [0] * 16
    top = 0
    for k in range(len(dens)):
        if dens[k] <= r:
            top = k
        else:
            break
    coeffs = [0] * 16
    remaining = r
    for k in range(top, -1, -1):
        if dens[k] <= remaining:
            b_k = remaining // dens[k]
            coeffs[k] = b_k
            remaining -= b_k * dens[k]
    return coeffs

def ternary_digits(x, n):
    """First n ternary digits of x ∈ [0,1)."""
    digits = []
    val = x
    for _ in range(n):
        val *= 3
        d = int(val)
        digits.append(d)
        val -= d
    return digits

def first_digit2_pos(digits):
    """Position of first digit 2, or -1 if none."""
    for i, d in enumerate(digits):
        if d == 2:
            return i
    return -1

def val_to_ternary_block(x):
    """Compute floor(3^(x+29)) and its 30 ternary digits."""
    val = int(math.floor(3**(x + 29)))
    digits = []
    v = val
    for _ in range(30):
        digits.append(v % 3)
        v //= 3
    return val, digits

def compute_NK(K):
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
    return NK

# ─── Main analysis ───
K = 12
NK = compute_NK(K)
survivors = [r for r in NK if r >= 23]

print(f"K = {K}, survivors r ≥ 23: {len(survivors)}")
print(f"α = {alpha:.15f}")
print()

# ─── Compute full data for each survivor ───
records = []
for r in survivors:
    x = (r * alpha) % 1.0
    b = ostrowski_rep_full(r)
    
    # Epsilon contributions
    contributions = [b[k] * epsilons[k] for k in range(16)]
    total = sum(contributions)
    
    # Partial sums (cumulative from k=0)
    partial_sums = []
    s = 0
    for k in range(16):
        s += contributions[k]
        partial_sums.append(s)
    
    # Dominant term (largest |contribution|)
    max_abs = 0
    max_k = 0
    for k in range(16):
        if abs(contributions[k]) > max_abs:
            max_abs = abs(contributions[k])
            max_k = k
    
    # Leading ternary block
    val, digits30 = val_to_ternary_block(x)
    first2 = first_digit2_pos(digits30)
    
    # topIdx
    top = 0
    for k in range(len(dens)):
        if dens[k] <= r:
            top = k
        else:
            break
    
    # 2^r mod 3^K
    pow2r_mod = pow(2, r, 3**K)
    
    # Sign pattern of nonzero contributions
    sign_pattern = []
    for k in range(16):
        if contributions[k] > 0:
            sign_pattern.append(f"+{k}")
        elif contributions[k] < 0:
            sign_pattern.append(f"-{k}")
    
    records.append({
        'r': r,
        'x': x,
        'b': b,
        'contributions': contributions,
        'total': total,
        'partial_sums': partial_sums,
        'max_k': max_k,
        'max_abs': max_abs,
        'top': top,
        'first2': first2,
        'digits30': digits30,
        'val': val,
        'pow2r_mod': pow2r_mod,
        'sign_pattern': sign_pattern,
    })

# ─── Sort by first2 (closest to C30Lead) ───
records.sort(key=lambda rec: -rec['first2'])

print("="*100)
print("TOP 30 CLOSEST TO C30Lead (largest first digit 2 position)")
print("="*100)
print(f"{'r':>7} {'topIdx':>6} {'first2':>6} {'max_k':>5} {'total':>14} {'max|contrib|':>14} "
      f"{'sign pattern':>20} {'leading block (first 15 ternary digits)'}")
print("-"*100)

for rec in records[:30]:
    r = rec['r']
    top = rec['top']
    first2 = rec['first2']
    max_k = rec['max_k']
    total = rec['total']
    max_abs = rec['max_abs']
    
    # Sign pattern of nonzero contributions
    signs = rec['sign_pattern']
    
    # Leading digits (first 15)
    leading15 = ''.join(str(d) for d in rec['digits30'][:15])
    
    print(f"{r:7d} {top:6d} {first2:6d} {max_k:5d} {total:+14.10f} {max_abs:14.10f} "
          f"{str(signs):>20} {leading15}")

# ─── For the top candidates, show full Ostrowski structure ───
print("\n" + "="*100)
print("FULL OSTROWSKI STRUCTURE FOR TOP 10 CLOSEST TO C30Lead")
print("="*100)

for rec in records[:10]:
    r = rec['r']
    b = rec['b']
    contribs = rec['contributions']
    partials = rec['partial_sums']
    
    print(f"\n--- r = {r}, first2 = {rec['first2']}, topIdx = {rec['top']} ---")
    print(f"  Ostrowski coefficients:")
    for k in range(16):
        if b[k] != 0:
            sign = "+" if contribs[k] > 0 else "-"
            print(f"    b[{k:2d}] = {b[k]:3d}  |  ε[{k:2d}] = {epsilons[k]:+.12f}  |  "
                  f"b*ε = {contribs[k]:+.12f}  |  partial = {partials[k]:+.12f}")
    
    print(f"  Total ε_sum = {rec['total']:+.12f}")
    print(f"  Dominant term: k={rec['max_k']}, |b*ε|={rec['max_abs']:.12f}")
    print(f"  Leading 30 ternary: {''.join(str(d) for d in rec['digits30'])}")
    print(f"  2^{r} mod 3^{K} = {rec['pow2r_mod']}")
    
    # Cancellation analysis: how much do terms cancel?
    pos_sum = sum(c for c in contribs if c > 0)
    neg_sum = sum(c for c in contribs if c < 0)
    net = pos_sum + neg_sum
    gross = pos_sum - neg_sum  # = sum of absolute values
    if gross > 0:
        cancellation_ratio = abs(net) / gross
    else:
        cancellation_ratio = 0
    print(f"  Positive contributions: {pos_sum:+.12f}")
    print(f"  Negative contributions: {neg_sum:+.12f}")
    print(f"  Gross magnitude: {gross:.12f}")
    print(f"  Cancellation ratio (|net|/gross): {cancellation_ratio:.6f}")
    print(f"  High-index terms (k≥5): {sum(c for k, c in enumerate(contribs) if k >= 5):+.12f}")

# ─── Statistical summary by first2 bucket ───
print("\n" + "="*100)
print("STATISTICAL SUMMARY BY FIRST DIGIT-2 POSITION")
print("="*100)

buckets = defaultdict(list)
for rec in records:
    bucket = rec['first2'] // 5 * 5  # bucket in groups of 5
    buckets[bucket].append(rec)

for bucket in sorted(buckets.keys()):
    recs = buckets[bucket]
    n = len(recs)
    avg_total = sum(r['total'] for r in recs) / n
    avg_cancel = sum(
        abs(r['total']) / max(sum(abs(c) for c in r['contributions']), 1e-15)
        for r in recs
    ) / n
    avg_max_k = sum(r['max_k'] for r in recs) / n
    avg_top = sum(r['top'] for r in recs) / n
    max_first2 = max(r['first2'] for r in recs)
    
    print(f"  first2 ∈ [{bucket:2d},{bucket+5:2d}): {n:4d} records, "
          f"avg_total={avg_total:+.8f}, avg_|cancel_ratio|={avg_cancel:.4f}, "
          f"avg_max_k={avg_max_k:.1f}, avg_topIdx={avg_top:.1f}, max_first2={max_first2}")

# ─── Check: is there a relationship between topIdx and first2? ───
print("\n" + "="*100)
print("topIdx vs first2 CORRELATION")
print("="*100)

by_top = defaultdict(list)
for rec in records:
    by_top[rec['top']].append(rec['first2'])

for top in sorted(by_top.keys()):
    first2s = by_top[top]
    n = len(first2s)
    avg = sum(first2s) / n
    mx = max(first2s)
    print(f"  topIdx={top:2d}: {n:4d} records, avg first2={avg:.1f}, max first2={mx}")

# ─── Check: what about the sign of the dominant term? ───
print("\n" + "="*100)
print("DOMINANT TERM SIGN vs first2")
print("="*100)

by_dom_sign = {'pos': [], 'neg': []}
for rec in records:
    if contribs := [c for c in rec['contributions'] if abs(c) > 1e-10]:
        dominant_sign = 'pos' if max(contribs) > -min(contribs) else 'neg'
        by_dom_sign[dominant_sign].append(rec['first2'])

for sign, first2s in by_dom_sign.items():
    if first2s:
        n = len(first2s)
        avg = sum(first2s) / n
        mx = max(first2s)
        print(f"  Dominant {sign:3s}: {n:4d} records, avg first2={avg:.1f}, max first2={mx}")

# ─── Check: partial sum trajectory for top candidates ───
print("\n" + "="*100)
print("PARTIAL SUM TRAJECTORIES FOR TOP 5 CLOSEST TO C30Lead")
print("="*100)

for rec in records[:5]:
    r = rec['r']
    partials = rec['partial_sums']
    contribs = rec['contributions']
    
    print(f"\n--- r = {r}, first2 = {rec['first2']} ---")
    print(f"  {'k':>3} {'b[k]':>5} {'ε[k]':>15} {'b*ε':>15} {'partial':>15} {'|partial|':>12}")
    for k in range(16):
        if rec['b'][k] != 0:
            print(f"  {k:3d} {rec['b'][k]:5d} {epsilons[k]:+15.12f} {contribs[k]:+15.12f} "
                  f"{partials[k]:+15.12f} {abs(partials[k]):12.10f}")
    print(f"  Final: {rec['total']:+.15f}")
