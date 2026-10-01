#!/usr/bin/env python3
"""
Block-2 classification for the Erdos ternary conjecture.

For each s in {0, 2, 8}, we already know the block-1 exceptional residues
(32,767 per s). Now we check whether those residues have digit 2 in
block 2 (positions 30..44) of 2^(s + P*r).

Block 2 uses modulus 3^45 (need digits up to position 44).
"""

import time
from collections import Counter


def generate_no2_set(n_digits):
    """Numbers < 3^n_digits with only digits 0,1 in base 3."""
    no2 = set()
    for i in range(2 ** n_digits):
        val = 0
        temp = i
        for _ in range(n_digits):
            val = val * 3 + (temp & 1)
            temp >>= 1
        no2.add(val)
    return no2


def compute_block1_exceptional(s, P, mod_3_15, mod_3_30, pow2_P_mod30, no2_set):
    """Get the list of block-1 exceptional residues for a given s."""
    pow2_s_30 = pow(2, s, mod_3_30)
    current = pow2_s_30
    exc = []
    for r in range(1, mod_3_15):
        current = (current * pow2_P_mod30) % mod_3_30
        block1 = (current // (3 ** 15)) % (3 ** 15)
        if block1 in no2_set:
            exc.append(r)
    return exc


def classify_block2(s, P, mod_3_15, mod_3_45, pow2_P_mod45, exceptional_list):
    """
    For each exceptional residue r, compute 2^(s+P*r) mod 3^45
    and check block 2 (positions 30..44).
    """
    pow2_s_45 = pow(2, s, mod_3_45)

    caught = 0
    exceptional = 0
    exc_residues = []
    witnesses = []
    pow_3_30 = 3 ** 30
    pow_3_15 = 3 ** 15

    # Build set of exceptional r for O(1) lookup
    exc_set = set(exceptional_list)

    # Iterate all r but only report for exceptional ones
    current = pow2_s_45
    for r in range(1, mod_3_15):
        current = (current * pow2_P_mod45) % mod_3_45
        if r in exc_set:
            block2 = (current // pow_3_30) % pow_3_15
            if block2 not in no2_set_global:
                # Has digit 2 in block 2 -> caught
                caught += 1
                # Find witness
                temp = block2
                for pos in range(15):
                    if temp % 3 == 2:
                        witnesses.append(30 + pos)
                        break
                    temp //= 3
            else:
                exceptional += 1
                exc_residues.append(r)

    return caught, exceptional, witnesses, exc_residues


def main():
    P = 162 * 59049
    mod_3_15 = 3 ** 15
    mod_3_30 = 3 ** 30
    mod_3_45 = 3 ** 45

    print(f"P = {P}")
    print(f"3^15 = {mod_3_15}")
    print(f"3^30 = {mod_3_30}")
    print(f"3^45 = {mod_3_45}")

    pow2_P_mod30 = pow(2, P, mod_3_30)
    pow2_P_mod45 = pow(2, P, mod_3_45)
    print(f"2^P mod 3^30 = {pow2_P_mod30}")
    print(f"2^P mod 3^45 = {pow2_P_mod45}")

    global no2_set_global
    no2_set_global = generate_no2_set(15)
    print(f"No-digit-2 set: {len(no2_set_global)} numbers")

    for s in [0, 2, 8]:
        print(f"\n{'='*60}")
        print(f"Block 2 analysis for s = {s}")
        print(f"{'='*60}")

        # Step 1: get block-1 exceptional residues
        t0 = time.time()
        exc1 = compute_block1_exceptional(s, P, mod_3_15, mod_3_30, pow2_P_mod30, no2_set_global)
        t1 = time.time()
        print(f"Block-1 exceptional: {len(exc1)} residues ({t1-t0:.1f}s)")

        # Step 2: classify block 2
        t0 = time.time()
        caught2, exc2, witnesses2, exc_res2 = classify_block2(
            s, P, mod_3_15, mod_3_45, pow2_P_mod45, exc1
        )
        t1 = time.time()

        print(f"Block-2 caught (has digit 2 in pos 30..44): {caught2}")
        print(f"Block-2 exceptional (no digit 2 in pos 30..44): {exc2}")
        print(f"Time: {t1-t0:.1f}s")

        if witnesses2:
            wc = Counter(witnesses2)
            print(f"\nBlock-2 first witness position distribution:")
            for pos in sorted(wc.keys()):
                print(f"  position {pos}: {wc[pos]} residues")

        if exc_res2:
            print(f"\nBlock-2 exceptional residues ({len(exc_res2)} total):")
            if len(exc_res2) <= 100:
                print(f"  {exc_res2}")
            else:
                print(f"  First 50: {exc_res2[:50]}")
        else:
            print(f"\nAll block-1 exceptions resolved in block 2!")

    print(f"\n{'='*60}")
    print("Done.")


if __name__ == "__main__":
    main()
