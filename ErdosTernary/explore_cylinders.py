#!/usr/bin/env python3
"""
Phase 3: Ternary cylinder analysis.
Partition [0,1) into ternary cylinders at depths d=1..10.
Check which cylinders contain N_K points and which are C30Lead-compatible.
"""
import math

alpha = math.log(2) / math.log(3)

# ─── Ternary cylinder helpers ───
def ternary_digits(x, n):
    """Return first n ternary digits of x ∈ [0,1)."""
    digits = []
    val = x
    for _ in range(n):
        val *= 3
        d = int(val)
        digits.append(d)
        val -= d
    return digits

def cylinder_index(digits):
    """Convert list of ternary digits to integer a."""
    a = 0
    for d in digits:
        a = a * 3 + d
    return a

def has_no_digit_2(digits):
    """Check if digit list has no 2."""
    return all(d != 2 for d in digits)

# ─── C30Lead compatibility at depth d ───
def c30_compatible_at_depth(d):
    """Return set of cylinder indices a ∈ [0, 3^d) that are C30-compatible.
    A cylinder is C30-compatible if its first d digits have no digit 2,
    because the remaining 30-d digits can be chosen freely."""
    compatible = set()
    for a in range(3**d):
        # Get ternary digits of a (padded to d digits)
        digits = []
        temp = a
        for _ in range(d):
            digits.append(temp % 3)
            temp //= 3
        digits.reverse()  # now digits[0] is most significant
        if has_no_digit_2(digits):
            compatible.add(a)
    return compatible

# ─── N_K computation ───
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
print("="*80)
print("TERNARY CYLINDER ANALYSIS: Which cylinders contain N_K points?")
print("="*80)

for K in range(8, 17):
    NK = compute_NK(K)
    survivors = [r for r in NK if r >= 23]
    
    print(f"\n{'='*60}")
    print(f"K = {K}, |N_K| = {len(NK)}, survivors r ≥ 23: {len(survivors)}")
    print(f"{'='*60}")
    
    for d in range(1, 11):
        # Which cylinders contain N_K points?
        occupied = set()
        for r in survivors:
            x = (r * alpha) % 1.0
            digits = ternary_digits(x, d)
            a = cylinder_index(digits)
            occupied.add(a)
        
        # Which cylinders are C30-compatible?
        compatible = c30_compatible_at_depth(d)
        
        # Intersection
        overlap = occupied & compatible
        
        n_compatible = len(compatible)
        n_occupied = len(occupied)
        n_overlap = len(overlap)
        
        status = "EXCLUDED" if n_overlap == 0 else f"OVERLAP={n_overlap}"
        
        print(f"  d={d:2d}: occupied={n_occupied:5d}/{3**d:6d}, "
              f"C30-compat={n_compatible:5d}/{3**d:6d}, "
              f"overlap={n_overlap:5d}  {status}")
        
        if n_overlap > 0 and d <= 5:
            # Show which overlapping cylinders
            print(f"         Overlapping cylinders: {sorted(overlap)[:20]}")
            # Show example r values in each overlapping cylinder
            for a in sorted(overlap)[:3]:
                examples = []
                for r in survivors:
                    x = (r * alpha) % 1.0
                    digits = ternary_digits(x, d)
                    if cylinder_index(digits) == a:
                        examples.append(r)
                        if len(examples) >= 3:
                            break
                print(f"           Cylinder {a} (digits={ternary_digits(a/3**d, d)}): "
                      f"r = {examples}")

print("\n" + "="*80)
print("SUMMARY: At what depth d does exclusion first occur?")
print("="*80)

for K in [8, 12, 16]:
    NK = compute_NK(K)
    survivors = [r for r in NK if r >= 23]
    
    exclusion_depth = None
    for d in range(1, 31):
        occupied = set()
        for r in survivors:
            x = (r * alpha) % 1.0
            digits = ternary_digits(x, d)
            a = cylinder_index(digits)
            occupied.add(a)
        
        compatible = c30_compatible_at_depth(d)
        overlap = occupied & compatible
        
        if len(overlap) == 0:
            exclusion_depth = d
            break
    
    if exclusion_depth:
        print(f"  K={K:2d}: Exclusion at depth d = {exclusion_depth}")
    else:
        print(f"  K={K:2d}: No exclusion found up to depth 30")

# ─── Detailed view at the exclusion depth ───
print("\n" + "="*80)
print("DETAILED VIEW AT EXCLUSION DEPTH")
print("="*80)

K = 12
NK = compute_NK(K)
survivors = [r for r in NK if r >= 23]

for d in [1, 2, 3, 4, 5]:
    occupied = {}
    for r in survivors:
        x = (r * alpha) % 1.0
        digits = ternary_digits(x, d)
        a = cylinder_index(digits)
        occupied.setdefault(a, []).append(r)
    
    compatible = c30_compatible_at_depth(d)
    
    print(f"\n--- Depth d = {d} ---")
    print(f"  C30-compatible cylinders ({len(compatible)}): {sorted(compatible)}")
    print(f"  Occupied cylinders ({len(occupied)}):")
    for a in sorted(occupied.keys()):
        marker = " *" if a in compatible else "  "
        n = len(occupied[a])
        print(f"    Cylinder {a:3d} (ternary={ternary_digits(a/3**d, d)}): "
              f"{n:4d} points{marker}")

# ─── What's the structure of C30-compatible cylinders? ───
print("\n" + "="*80)
print("C30-COMPATIBLE CYLINDER STRUCTURE")
print("="*80)

for d in range(1, 8):
    compatible = c30_compatible_at_depth(d)
    # Count by first digit
    by_first = {0: 0, 1: 0, 2: 0}
    for a in compatible:
        first_digit = a // (3**(d-1))
        by_first[first_digit] += 1
    
    print(f"  d={d}: {len(compatible):5d} compatible cylinders, "
          f"by first digit: 0→{by_first[0]:4d}, 1→{by_first[1]:4d}, 2→{by_first[2]:4d}")
