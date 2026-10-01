#!/usr/bin/env python3
"""Analyze whether positions 5-14 cover all (s, k) pairs for n5_digitMod_covers.

For each residue s in N5_even_set and each k < 59049 with s + 162*k >= 69,
compute digitMod(s + 162*k, j) for j in [5, 14] and check if any equals 2.
"""

N5_EVEN = [0, 2, 8, 20, 24, 26, 54, 56, 62, 72, 74, 78, 80, 96, 126, 150]

def digitMod(r, j):
    """Compute (2^r % 3^(j+1)) / 3^j % 3"""
    m = 3 ** (j + 1)
    pow_mod = pow(2, r, m)
    return (pow_mod // (3 ** j)) % 3

def analyze():
    total = 0
    covered_5_14 = 0
    covered_5_11 = 0
    uncovered = []
    max_pos_needed = 0
    pos_distribution = {}  # position -> count of first occurrence

    for s in N5_EVEN:
        for k in range(59049):
            r = s + 162 * k
            if r < 69:
                continue
            total += 1

            # Check positions 5-14
            found_5_14 = False
            found_5_11 = False
            first_pos = None
            for j in range(5, 43):
                if digitMod(r, j) == 2:
                    if first_pos is None:
                        first_pos = j
                    if j <= 11:
                        found_5_11 = True
                    if j <= 14:
                        found_5_14 = True
                    break  # Found first position

            if found_5_11:
                covered_5_11 += 1
            if found_5_14:
                covered_5_14 += 1

            if first_pos is not None:
                pos_distribution[first_pos] = pos_distribution.get(first_pos, 0) + 1
                if first_pos > max_pos_needed:
                    max_pos_needed = first_pos
            else:
                uncovered.append((s, k, r))

    print(f"Total (s, k) pairs: {total}")
    print(f"Covered by positions 5-11: {covered_5_11} ({100*covered_5_11/total:.1f}%)")
    print(f"Covered by positions 5-14: {covered_5_14} ({100*covered_5_14/total:.1f}%)")
    print(f"Uncovered (no digit 2 at positions 5-42): {len(uncovered)}")
    print(f"Max position needed: {max_pos_needed}")
    print()
    print("Position distribution (first occurrence):")
    for pos in sorted(pos_distribution.keys()):
        count = pos_distribution[pos]
        print(f"  Position {pos}: {count} cases ({100*count/total:.2f}%)")

    # Show which residues have cases needing positions > 14
    print()
    print("Residues with cases needing positions > 14:")
    for s in N5_EVEN:
        count = 0
        for k in range(59049):
            r = s + 162 * k
            if r < 69:
                continue
            for j in range(5, 15):
                if digitMod(r, j) == 2:
                    break
            else:
                count += 1
        if count > 0:
            print(f"  s={s}: {count} cases")

    if uncovered:
        print()
        print(f"First 10 uncovered cases: {uncovered[:10]}")

if __name__ == "__main__":
    analyze()
