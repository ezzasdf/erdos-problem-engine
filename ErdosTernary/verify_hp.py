#!/usr/bin/env python3
"""
Verify the C30 hits using high-precision arithmetic.
The floating-point computation is unreliable for r > 10^9.
Use mpmath for exact verification.
"""
import math

try:
    import mpmath
    mpmath.mp.dps = 50  # 50 decimal digits of precision
    HAS_MPMATH = True
except ImportError:
    HAS_MPMATH = False
    print("mpmath not available, using fallback verification")

alpha = math.log(2) / math.log(3)
u12 = 2 * 3**11  # = 354294

def leading_30_digits_float(r):
    """Floating-point computation (unreliable for large r)."""
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

# ─── High-precision verification ───
if HAS_MPMATH:
    print("="*80)
    print("HIGH-PRECISION VERIFICATION")
    print("="*80)
    
    alpha_hp = mpmath.log(2) / mpmath.log(3)
    
    def leading_30_digits_hp(r):
        """High-precision computation."""
        r_hp = mpmath.mpf(r)
        x = mpmath.fmod(r_hp * alpha_hp, 1)
        # Compute 3^(x + 29)
        val = mpmath.floor(mpmath.power(3, x + 29))
        val_int = int(val)
        digits = []
        v = val_int
        for _ in range(30):
            digits.append(v % 3)
            v //= 3
        return digits
    
    # ─── Verify the hits from the targeted search ───
    print("\n--- Verifying C30 hits from targeted search ---")
    
    # These are the hits we found (non-zero {rα})
    hits_to_verify = [
        (186, 13555, 4802455356),
        (186, 188458, 66769538838),
        (474, 38736, 13723932858),
        (560, 73841, 26161423814),
    ]
    
    for r0, n, r in hits_to_verify:
        # Verify r ∈ N₁₂
        pow2r = pow(2, r, 3**12)
        v = pow2r
        trail12 = []
        for i in range(12):
            trail12.append(v % 3)
            v //= 3
        trail_ok = has_no_digit_2(trail12)
        
        # Verify leading digits with high precision
        lead_hp = leading_30_digits_hp(r)
        lead_hp_ok = has_no_digit_2(lead_hp)
        
        # Compare with floating-point
        lead_float = leading_30_digits_float(r)
        match = (lead_hp == lead_float)
        
        print(f"\nr = {r:,} (r₀={r0}, n={n})")
        print(f"  Trailing 12 (reversed): {''.join(str(d) for d in reversed(trail12))}")
        print(f"  Trailing OK: {trail_ok}")
        print(f"  Leading 30 (HP):  {''.join(str(d) for d in lead_hp)}")
        print(f"  Leading 30 (float): {''.join(str(d) for d in lead_float)}")
        print(f"  Leading OK (HP): {lead_hp_ok}")
        print(f"  HP matches float: {match}")
        
        if trail_ok and lead_hp_ok:
            print(f"  *** COUNTEREXAMPLE CONFIRMED WITH HIGH PRECISION ***")
        elif trail_ok and not lead_hp_ok:
            print(f"  Floating-point FALSE POSITIVE — HP shows digit 2 present")
        elif not trail_ok:
            print(f"  Not in N₁₂ (trailing digit 2 found)")
    
    # ─── Also verify some "zero" hits ───
    print("\n--- Verifying 'zero' hits (likely floating-point artifacts) ---")
    zero_hits = [
        (186, 87487, 30996119364),
        (186, 230380, 81622251906),
        (332, 61525, 21797938682),
    ]
    
    for r0, n, r in zero_hits:
        pow2r = pow(2, r, 3**12)
        v = pow2r
        trail12 = []
        for i in range(12):
            trail12.append(v % 3)
            v //= 3
        trail_ok = has_no_digit_2(trail12)
        
        lead_hp = leading_30_digits_hp(r)
        lead_hp_ok = has_no_digit_2(lead_hp)
        
        # Check {rα} with high precision
        r_hp = mpmath.mpf(r)
        frac_hp = mpmath.fmod(r_hp * alpha_hp, 1)
        
        print(f"\nr = {r:,} (r₀={r0}, n={n})")
        print(f"  Trailing OK: {trail_ok}")
        print(f"  {{rα}} (HP): {float(frac_hp):.15f}")
        print(f"  Leading 30 (HP):  {''.join(str(d) for d in lead_hp)}")
        print(f"  Leading OK (HP): {lead_hp_ok}")
        
        if trail_ok and lead_hp_ok:
            print(f"  *** COUNTEREXAMPLE CONFIRMED ***")
        elif trail_ok and not lead_hp_ok:
            print(f"  Floating-point FALSE POSITIVE")

else:
    print("mpmath not available. Using Python's fractions module for partial verification.")
    
    # At least verify the floating-point is wrong for the "zero" hits
    print("\n--- Checking if {rα} can be exactly 0 ---")
    print("For α = log₃(2), {rα} = 0 iff r×log₃(2) ∈ ℤ")
    print("This would mean 2^r = 3^k for some k, which is impossible for r > 0.")
    print("So {rα} = 0 is ALWAYS a floating-point artifact.")
    print()
    print("The 'zero' hits are definitely false positives.")
    print("The non-zero hits need high-precision verification.")
