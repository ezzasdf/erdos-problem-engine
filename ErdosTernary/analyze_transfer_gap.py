#!/usr/bin/env python3
"""For cases needing positions > 14, check if there's a digit 2 at positions 5-14
of the FULL r = r' + 162*59049*q for various q values.

Key insight: the transfer preserves positions 5-14 from r' to r.
So if r' has no digit 2 at positions 5-14, neither does r.
We need to check positions 15+ directly.
"""

N5_EVEN = [0, 2, 8, 20, 24, 26, 54, 56, 62, 72, 74, 78, 80, 96, 126, 150]

def digitMod(r, j):
    m = 3 ** (j + 1)
    return (pow(2, r, m) // (3 ** j)) % 3

def analyze_transfer_gap():
    """For the ~1.7% cases, check if digit 2 exists at positions 15-42
    for r = r' + 162*59049*q for q = 1, 2, 3, ..., 100."""
    
    gap_cases = []
    for s in N5_EVEN:
        for k in range(59049):
            r_prime = s + 162 * k
            if r_prime < 69:
                continue
            # Check if positions 5-14 have digit 2
            has_5_14 = False
            for j in range(5, 15):
                if digitMod(r_prime, j) == 2:
                    has_5_14 = True
                    break
            if has_5_14:
                continue
            
            # This is a gap case: r' needs positions 15-42
            gap_cases.append((s, k, r_prime))
    
    print(f"Gap cases (need positions > 14): {len(gap_cases)}")
    
    # For each gap case, check q = 1..100
    works_for_all_q = 0
    fails_for_some_q = 0
    
    P = 162 * 59049
    
    # Check a sample of gap cases
    sample = gap_cases[:50]  # Check first 50
    
    for s, k, r_prime in sample:
        all_q_work = True
        for q in range(1, 101):
            r = r_prime + P * q
            found = False
            for j in range(5, 43):
                if digitMod(r, j) == 2:
                    found = True
                    break
            if not found:
                all_q_work = False
                print(f"  FAIL: s={s}, k={k}, q={q}, r={r}")
                break
        if all_q_work:
            works_for_all_q += 1
        else:
            fails_for_some_q += 1
    
    print(f"Works for all q=1..100: {works_for_all_q}/{len(sample)}")
    print(f"Fails for some q: {fails_for_some_q}/{len(sample)}")
    
    # Also check: for gap cases, what position does digit 2 appear at for q=1?
    print()
    print("Gap case analysis for q=1:")
    pos_counts = {}
    for s, k, r_prime in gap_cases[:200]:
        r = r_prime + P * 1
        for j in range(5, 43):
            if digitMod(r, j) == 2:
                pos_counts[j] = pos_counts.get(j, 0) + 1
                break
        else:
            pos_counts[-1] = pos_counts.get(-1, 0) + 1  # No digit 2 found
    
    for pos in sorted(pos_counts.keys()):
        if pos == -1:
            print(f"  No digit 2 at positions 5-42: {pos_counts[pos]} cases")
        else:
            print(f"  First digit 2 at position {pos}: {pos_counts[pos]} cases")

if __name__ == "__main__":
    analyze_transfer_gap()
