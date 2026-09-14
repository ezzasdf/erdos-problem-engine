#!/usr/bin/env python3
"""Phase 2: Find the actual max j needed, and generate Lean witness table."""

N5_even = [0, 2, 8, 20, 24, 26, 54, 56, 62, 72, 74, 78, 80, 96, 126, 150]
K_MAX = 59049
PERIOD = 162

def digit_j_of_2_to_n(n, j):
    m = 3 ** (j + 1)
    return (pow(2, n, m) // (3 ** j)) % 3

def main():
    # Find actual max j needed
    max_j_overall = 0
    max_j_by_s = {s: 0 for s in N5_even}
    fails_with_j = {}
    
    total = 0
    for s in N5_even:
        for k in range(K_MAX):
            r = s + PERIOD * k
            if r < 48:
                continue
            total += 1
            found_j = None
            for j in range(5, 30):
                if digit_j_of_2_to_n(r, j) == 2:
                    found_j = j
                    break
            if found_j is None:
                print(f"  NO j < 30 found: s={s}, k={k}, r={r}")
            else:
                if found_j > max_j_overall:
                    max_j_overall = found_j
                if found_j > max_j_by_s[s]:
                    max_j_by_s[s] = found_j
                if found_j not in fails_with_j:
                    fails_with_j[found_j] = 0
                fails_with_j[found_j] += 1
    
    print(f"\nTotal cases: {total}")
    print(f"Max j needed: {max_j_overall}")
    print(f"Max j by residue: {max_j_by_s}")
    print(f"\nJ distribution:")
    for j in sorted(fails_with_j.keys()):
        print(f"  j={j}: {fails_with_j[j]} cases")
    
    # For the first failure at s=0, show what j values work
    print(f"\n--- Tracing s=0, k=7 (r=1134) ---")
    r = 1134
    for j in range(5, 30):
        d = digit_j_of_2_to_n(r, j)
        print(f"  j={j}: digit={d}")

    # Now generate per-residue witness table
    # For each s, group k values by witness j
    print("\n=== Per-residue witness analysis ===")
    for s in N5_even:
        j_groups = {}
        for k in range(K_MAX):
            r = s + PERIOD * k
            if r < 48:
                continue
            for j in range(5, max_j_overall + 1):
                if digit_j_of_2_to_n(r, j) == 2:
                    if j not in j_groups:
                        j_groups[j] = 0
                    j_groups[j] += 1
                    break
        total_s = sum(j_groups.values())
        print(f"  s={s:3d}: {total_s} cases, j distribution: {dict(sorted(j_groups.items()))}")

    # Check: for j >= 14, what is the period?
    # digit_j(2^n) has period 2*3^j.
    # Since 162 = 2*3^4, digit_j(2^(s+162*k)) depends on k mod 3^(j-4).
    # For j=19: period for k is 3^15 = 14348907, so all 59049 k values are distinct.
    # But we only need to check for each (s, k_mod) where k_mod = k mod period_k.
    
    # Check if we can use periodicity for larger j
    for j in range(14, 25):
        period_k = 3 ** (j - 4)
        print(f"\n  j={j}: period_k = {period_k}, K_MAX = {K_MAX}")
        if period_k >= K_MAX:
            print(f"    No periodicity benefit for k < {K_MAX}")
        else:
            print(f"    Can reduce k range to {period_k}")

if __name__ == "__main__":
    main()
