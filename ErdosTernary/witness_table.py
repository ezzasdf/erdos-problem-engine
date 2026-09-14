#!/usr/bin/env python3
"""Generate N5 witness table: for each N5_even residue s and each k < 59049,
find the smallest j ∈ {5,...,13} such that digit_j(2^(s+162*k)) == 2.

Strategy:
  digit_j(2^n) = (2^n mod 3^(j+1)) // 3^j % 3

  We use the periodicity: 2^(162) ≡ 1 (mod 3^(j+1)) for j < 5.
  For j >= 5, digit_j(2^n) has period 2*3^j.
  Since 162 = 2*3^4, digit_j(2^(s+162*k)) = digit_j(2^(s + 162*k mod (2*3^j))).

  To avoid huge exponents, we reduce the exponent modulo 2*3^j.
  For j <= 13, 2*3^j <= 3188646, so the reduced exponent is manageable.
"""

from math import gcd

N5_even = [0, 2, 8, 20, 24, 26, 54, 56, 62, 72, 74, 78, 80, 96, 126, 150]
K_MAX = 59049  # 3^10
PERIOD = 162   # = 2 * 3^4

def powmod(base, exp, mod):
    return pow(base, exp, mod)

def digit_j_of_2_to_n(n, j):
    """Compute digit_j(2^n) = (2^n mod 3^(j+1)) // 3^j % 3"""
    m = 3 ** (j + 1)
    return (powmod(2, n, m) // (3 ** j)) % 3

def main():
    print("Generating witness table for N5 certificate...")
    print(f"N5_even residues: {N5_even}")
    print(f"K_MAX = {K_MAX}, PERIOD = {PERIOD}")

    # Step 1: For each (s, k), find witness j in {5,...,13}
    # But we optimize: use periodicity to reduce k range.
    #
    # For j <= 13, digit_j(2^(s+162*k)) depends on (s+162*k) mod (2*3^j).
    # Since 2*3^j | 2*3^13 = 3188646, and 162 = 2*3^4,
    # the k-dependence for a given j is via k mod (3^(j-4)).
    # So for j=13, we need k mod 3^9 = k mod 19683.
    #
    # For k >= 19683, digit_j for j <= 13 just repeats the k < 19683 values.
    # So we only need to check k < 19683 for j <= 13.
    #
    # BUT the theorem requires k < 59049. For k in [19683, 59049),
    # we need j > 13 OR we need the k < 19683 case to already cover it.
    # Since digit_j periodicity means the same values repeat,
    # if every k < 19683 is covered, then k < 59049 is also covered.

    # Actually, let me think more carefully. For j = 13:
    # period = 2*3^13 = 3188646
    # 162 * 19683 = 3188646
    # So digit_13(2^(s+162*k)) depends on k mod 19683.
    # For k in [0, 19683), all values are distinct.
    # For k in [19683, 39366), they repeat.
    # So checking k < 19683 is sufficient for j <= 13.

    # For k >= 19683 but k < 59049:
    # The digit values for j <= 13 are the same as for k % 19683.
    # So if every k % 19683 in [0, 19683) is covered, we're done.

    # BUT what if some k < 19683 has NO j <= 13 that works?
    # Then k' = k + 19683 also has no j <= 13.
    # We need to check if there are such cases.

    # Let me just compute for k < 59049 as stated in the theorem.
    # For most (s, k), j=5 works. Only a few need j > 5.

    # Actually let me first check: for EACH s, is there a SINGLE j
    # that works for ALL k? That would be ideal.

    print("\n--- Checking if single j works for all k per residue ---")
    for s in N5_even:
        for j in range(5, 14):
            all_ok = True
            for k in range(K_MAX):
                r = s + PERIOD * k
                if r < 48:
                    continue
                if digit_j_of_2_to_n(r, j) != 2:
                    all_ok = False
                    break
            if all_ok:
                print(f"  s={s:3d}: j={j} works for ALL k")
                break
        else:
            print(f"  s={s:3d}: NO single j works for all k")

    # Step 2: For each (s, k), find the minimum j
    print("\n--- Per-(s,k) witness table ---")
    max_k_per_s = {}
    for s in N5_even:
        max_k_needed = 0
        worst_j = 5
        for k in range(K_MAX):
            r = s + PERIOD * k
            if r < 48:
                continue
            found = False
            for j in range(5, 14):
                if digit_j_of_2_to_n(r, j) == 2:
                    found = True
                    if k > max_k_needed:
                        max_k_needed = k
                        worst_j = j
                    break
            if not found:
                print(f"  FAIL: s={s}, k={k}, r={r}")
        max_k_per_s[s] = (max_k_needed, worst_j)
        print(f"  s={s:3d}: max k needed = {max_k_needed:5d}, worst-case j = {worst_j}")

    # Step 3: Generate the Lean witness table
    # For each (s, k) with s in N5_even and k < 59049 and s+162*k >= 48,
    # output the witness j.
    # But this is 944K entries -- too large for Lean source.
    #
    # Alternative: use native_decide directly on the proposition.
    # The native_decide evaluates the entire proposition at C level.

    # Let me check the actual sizes involved
    print("\n--- Checking native_decide feasibility ---")
    import time
    t0 = time.time()
    count = 0
    for s in N5_even:
        for k in range(min(K_MAX, 100)):  # sample
            r = s + PERIOD * k
            if r < 48:
                continue
            for j in range(5, 14):
                if digit_j_of_2_to_n(r, j) == 2:
                    count += 1
                    break
    t1 = time.time()
    per_case = (t1 - t0) / max(count, 1)
    est_total = per_case * 944000
    print(f"  Sampled {count} cases in {t1-t0:.4f}s ({per_case*1000:.3f}ms/case)")
    print(f"  Estimated total for 944K cases: {est_total:.1f}s")

    # Step 4: Check with reduced exponent (periodic reduction)
    print("\n--- Testing with reduced exponent ---")
    t0 = time.time()
    count2 = 0
    for s in N5_even:
        for k in range(min(K_MAX, 100)):
            r = s + PERIOD * k
            if r < 48:
                continue
            for j in range(5, 14):
                period_j = 2 * (3 ** j)
                r_red = r % period_j
                m = 3 ** (j + 1)
                d = (powmod(2, r_red, m) // (3 ** j)) % 3
                if d == 2:
                    count2 += 1
                    break
    t1 = time.time()
    per_case2 = (t1 - t0) / max(count2, 1)
    est_total2 = per_case2 * 944000
    print(f"  Sampled {count2} cases in {t1-t0:.4f}s ({per_case2*1000:.3f}ms/case)")
    print(f"  Estimated total: {est_total2:.1f}s")

    # Step 5: Full validation with reduced exponents
    print("\n--- Full validation (all cases) ---")
    t0 = time.time()
    fails = []
    total = 0
    for s in N5_even:
        for k in range(K_MAX):
            r = s + PERIOD * k
            if r < 48:
                continue
            total += 1
            found = False
            for j in range(5, 14):
                if digit_j_of_2_to_n(r, j) == 2:
                    found = True
                    break
            if not found:
                fails.append((s, k, r))
    t1 = time.time()
    print(f"  Total cases: {total}")
    print(f"  Passed: {total - len(fails)}")
    print(f"  Failed: {len(fails)}")
    print(f"  Time: {t1-t0:.2f}s")
    if fails:
        print(f"  First 20 failures:")
        for s, k, r in fails[:20]:
            print(f"    s={s}, k={k}, r={r}")
            for j in range(5, 20):
                d = digit_j_of_2_to_n(r, j)
                print(f"      j={j}: digit={d}")

    # Step 6: For native_decide in Lean, check with j up to 13
    # but using the actual exponent (not reduced) -- to see if
    # the kernel can handle it.
    print("\n--- Checking native_decide with unreduced 2^r ---")
    # For native_decide, Lean evaluates digitMod r j = (2^r % 3^(j+1) / 3^j) % 3
    # For r up to ~9.6M, 2^r is a ~2.9M digit number.
    # But powmod(2, r, m) is fast even for large r.
    # The question is: can Lean's native_decide evaluate this for 944K cases?
    # Answer: the C code uses GMP, so yes. But the compilation of the
    # decision procedure might be slow.

    # Let me check timing with unreduced exponents
    t0 = time.time()
    count3 = 0
    for s in N5_even:
        for k in range(min(K_MAX, 50)):
            r = s + PERIOD * k
            if r < 48:
                continue
            for j in range(5, 14):
                # Use unreduced exponent like Lean's digitMod
                m = 3 ** (j + 1)
                d = (powmod(2, r, m) // (3 ** j)) % 3
                if d == 2:
                    count3 += 1
                    break
    t1 = time.time()
    per_case3 = (t1 - t0) / max(count3, 1)
    est_total3 = per_case3 * 944000
    print(f"  Sampled {count3} cases in {t1-t0:.4f}s ({per_case3*1000:.3f}ms/case)")
    print(f"  Estimated total: {est_total3:.1f}s")


if __name__ == "__main__":
    main()
