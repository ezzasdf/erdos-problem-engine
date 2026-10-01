#!/usr/bin/env python3
"""
Block-1 digit classification for the Erdos ternary conjecture.

For s in {0, 2, 8} and each residue r in 0 < r < 3^15, compute:
  2^(s + P*r) mod 3^30  where P = 2 * 3^14
and check whether the ternary digits at positions 15..29 contain a digit 2.

Optimization: precompute "no-digit-2" numbers < 3^15 (only digits 0,1 in base 3).
These are exactly 2^15 = 32,768 numbers. Check set membership instead of digit extraction.

Metrics reported:
  - Number caught (has digit 2 in block 1)
  - Number exceptional (no digit 2 in block 1)
  - Max/min first witness position
  - Exceptional residues
"""

import time
import sys


def generate_no2_set(n_digits):
    """
    Generate all numbers < 3^n_digits whose base-3 representation uses only digits 0 and 1.
    These are numbers with NO digit 2 in base 3.
    There are exactly 2^n_digits such numbers.
    """
    no2 = set()
    for i in range(2 ** n_digits):
        # Interpret binary digits of i as base-3 digits
        val = 0
        temp = i
        for _ in range(n_digits):
            val = val * 3 + (temp & 1)
            temp >>= 1
        no2.add(val)
    return no2


def classify_block1(s, P, mod_3_15, mod_3_30, pow2_P_mod, no2_set):
    """
    Classify all residues r = 1..mod_3_15-1 for a given s.

    Returns: (caught_count, exceptional_count, first_witness_map, exceptional_list)
    """
    pow2_s = pow(2, s, mod_3_30)

    # current = 2^(s + P*r) mod 3^30, iteratively computed
    # Start: current = 2^(s + P*0) = 2^s
    # After first iteration: current = 2^s * 2^P mod 3^30 = 2^(s+P)
    current = pow2_s

    caught_count = 0
    exceptional_count = 0
    exceptional_list = []
    witness_positions = []  # first position where digit=2 for caught residues

    for r in range(1, mod_3_15):
        current = (current * pow2_P_mod) % mod_3_30

        # Extract block-1 portion: digits 15..29
        block1 = (current // (3 ** 15)) % (3 ** 15)

        if block1 not in no2_set:
            # block1 has at least one digit 2 in positions 15..29 -> caught
            caught_count += 1
            # Find first witness position (lowest j in [15,30) where digit=2)
            temp = block1
            for pos in range(15):
                if temp % 3 == 2:
                    witness_positions.append(15 + pos)
                    break
                temp //= 3
        else:
            # block1 has no digit 2 (all digits are 0 or 1) -> exceptional
            exceptional_count += 1
            exceptional_list.append(r)

    return caught_count, exceptional_count, witness_positions, exceptional_list


def main():
    P = 162 * 59049  # = 2 * 3^14 = 9,565,938
    mod_3_15 = 3 ** 15  # = 14,348,907
    mod_3_30 = 3 ** 30  # = 2,058,911,320,946,944 (~2 * 10^15)

    print(f"P = {P}")
    print(f"3^15 = {mod_3_15}")
    print(f"3^30 = {mod_3_30}")
    print(f"2^P mod 3^30 = {pow(2, P, mod_3_30)}")

    # Precompute 2^P mod 3^30
    pow2_P_mod = pow(2, P, mod_3_30)

    # Precompute "no digit 2" set: numbers < 3^15 with only digits 0 and 1 in base 3
    print(f"\nPrecomputing no-digit-2 set for 15 ternary digits...")
    t0 = time.time()
    no2_set = generate_no2_set(15)
    print(f"  Generated {len(no2_set)} numbers in {time.time() - t0:.2f}s")
    assert len(no2_set) == 32768

    for s in [0, 2, 8]:
        print(f"\n{'='*60}")
        print(f"s = {s}")
        print(f"{'='*60}")

        t0 = time.time()
        caught, exceptional, witnesses, exc_residues = classify_block1(
            s, P, mod_3_15, mod_3_30, pow2_P_mod, no2_set
        )
        elapsed = time.time() - t0

        total = mod_3_15 - 1  # r = 1..3^15-1
        print(f"Total residues:     {total}")
        print(f"Caught (digit 2):   {caught} ({100*caught/total:.2f}%)")
        print(f"Exceptional:        {exceptional} ({100*exceptional/total:.2f}%)")
        print(f"Time:               {elapsed:.1f}s")

        if witnesses:
            from collections import Counter
            wc = Counter(witnesses)
            print(f"\nFirst witness position distribution:")
            for pos in sorted(wc.keys()):
                print(f"  position {pos}: {wc[pos]} residues")
            print(f"Min first witness:  {min(witnesses)}")
            print(f"Max first witness:  {max(witnesses)}")

        if exc_residues:
            print(f"\nExceptional residues ({len(exc_residues)} total):")
            if len(exc_residues) <= 50:
                print(f"  {exc_residues}")
            else:
                print(f"  First 50: {exc_residues[:50]}")
                print(f"  Last  50: {exc_residues[-50:]}")
                # Show some structure
                print(f"  Min: {min(exc_residues)}, Max: {max(exc_residues)}")
        else:
            print(f"\nNo exceptional residues! All residues caught.")

    print(f"\n{'='*60}")
    print("Done.")


if __name__ == "__main__":
    main()
