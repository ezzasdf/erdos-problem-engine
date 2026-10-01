#!/usr/bin/env python3
"""
Verify C30 hits using Python's decimal module for high precision.
No external dependencies needed.
"""
import math
from decimal import Decimal, getcontext

# Set precision to 50 digits
getcontext().prec = 50

alpha = math.log(2) / math.log(3)
u12 = 2 * 3**11

def has_no_digit_2(digits):
    return all(d != 2 for d in digits)

# High-precision alpha
alpha_hp = Decimal(2).ln() / Decimal(3).ln()

def leading_30_digits_hp(r):
    """High-precision computation using Decimal."""
    r_hp = Decimal(r)
    # Compute {r × alpha}
    product = r_hp * alpha_hp
    # Extract fractional part
    int_part = int(product)
    frac = product - int_part
    # Compute 3^(frac + 29)
    # 3^29 = 68630377364883
    pow3_29 = Decimal(68630377364883)
    val = pow3_29 * (Decimal(3) ** frac)
    val_int = int(val)
    digits = []
    v = val_int
    for _ in range(30):
        digits.append(v % 3)
        v //= 3
    return digits

# ─── Verify the non-zero hits ───
print("="*80)
print("HIGH-PRECISION VERIFICATION (using Decimal)")
print("="*80)

hits_to_verify = [
    (186, 13555, 4802455356, 0.299005985260),
    (186, 188458, 66769538838, 0.139198303223),
    (474, 38736, 13723932858, 0.129167556763),
    (560, 73841, 26161423814, 0.045476913452),
]

all_confirmed = True

for r0, n, r, expected_frac in hits_to_verify:
    # Verify r ∈ N₁₂
    pow2r = pow(2, r, 3**12)
    v = pow2r
    trail12 = []
    for i in range(12):
        trail12.append(v % 3)
        v //= 3
    trail_ok = has_no_digit_2(trail12)
    
    # High-precision leading digits
    lead_hp = leading_30_digits_hp(r)
    lead_hp_ok = has_no_digit_2(lead_hp)
    
    # High-precision fractional part
    r_hp = Decimal(r)
    frac_hp = r_hp * alpha_hp
    int_part = int(frac_hp)
    frac_val = frac_hp - int_part
    
    print(f"\nr = {r:,} (r₀={r0}, n={n})")
    print(f"  Trailing 12: {''.join(str(d) for d in reversed(trail12))}  OK: {trail_ok}")
    print(f"  {{rα}} (HP): {float(frac_val):.15f}  (float showed {expected_frac:.12f})")
    print(f"  Leading 30 (HP): {''.join(str(d) for d in lead_hp)}")
    print(f"  Leading OK (HP): {lead_hp_ok}")
    
    if trail_ok and lead_hp_ok:
        print(f"  *** COUNTEREXAMPLE CONFIRMED ***")
        all_confirmed = False
    elif trail_ok and not lead_hp_ok:
        print(f"  FLOATING-POINT FALSE POSITIVE — HP shows digit 2 in leading block")
    else:
        print(f"  Not in N₁₂")

print(f"\n{'='*80}")
if all_confirmed:
    print("ALL HITS VERIFIED AS FLOATING-POINT FALSE POSITIVES")
    print("The B4 bridge theorem survives this test.")
else:
    print("COUNTEREXAMPLES CONFIRMED — B4 bridge is DISPROVEN")
print(f"{'='*80}")

# ─── Also check: what is the actual {rα} for these r values? ───
print("\n--- Actual {rα} values (high precision) ---")
for r0, n, r, expected_frac in hits_to_verify:
    r_hp = Decimal(r)
    frac_hp = r_hp * alpha_hp
    int_part = int(frac_hp)
    frac_val = frac_hp - int_part
    print(f"  r={r:,}: {{rα}} = {float(frac_val):.15f}  (float: {expected_frac:.12f})")
