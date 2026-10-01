#!/usr/bin/env python3
"""Phase 12: Quantitative Bridge Bound Verification.

Verifies that the number of extra survivors (excluding n=0,2,8) in A_L ∩ B_K
decays exponentially with L, consistent with the equidistribution argument.
"""

import csv
from math import log

def u_k(k):
    return 2 * (3 ** (k - 1))


def verify_exponential_decay():
    """Check that extra survivors decay like (2/3)^L."""
    L_VALUES = [10, 20, 30, 40, 50, 60, 70]
    K_VALUES = [5, 8, 10, 12, 15]

    print("Extra survivors (excluding n=0,2,8) vs predicted (2/3)^L * |N_K|")
    print()
    print(f"{'K':>5s} | {'L':>3s} | {'extra':>6s} | {'predicted':>10s} | {'ratio':>8s}")
    print("-" * 55)

    for K in K_VALUES:
        filepath = f"verify_middle/bridge_data_K{K}.csv"
        with open(filepath) as f:
            sigs = list(csv.DictReader(f))

        n_k = 2 ** (K - 1)  # |N_K|

        for L in L_VALUES:
            survivors = [s for s in sigs if s[f"survives_L{L}"] == "True"]
            extra = [s for s in survivors if int(s["n"]) not in (0, 2, 8)]
            predicted = n_k * (2 / 3) ** L
            ratio = len(extra) / predicted if predicted > 0.01 else float("inf")
            print(f"{K:5d} | {L:3d} | {len(extra):6d} | {predicted:10.2f} | {ratio:8.2f}")
        print()


def verify_final_set():
    """Verify that for L>=30, only n=0,2,8 survive."""
    K_VALUES = [5, 8, 10, 12, 15]

    print("Verification: for L>=30, only n=0,2,8 survive")
    print()

    all_ok = True
    for K in K_VALUES:
        filepath = f"verify_middle/bridge_data_K{K}.csv"
        with open(filepath) as f:
            sigs = list(csv.DictReader(f))

        for L in [30, 40, 50, 60, 70]:
            survivors = [s for s in sigs if s[f"survives_L{L}"] == "True"]
            survivor_ns = sorted(int(s["n"]) for s in survivors)
            ok = survivor_ns == [0, 2, 8]
            if not ok:
                print(f"  K={K}, L={L}: FAIL — survivors = {survivor_ns}")
                all_ok = False

    if all_ok:
        print("  All K=5..15, L=30..70: PASS — only n=0,2,8 survive")
    print()


def compute_decay_rate():
    """Estimate the decay rate of extra survivors with L."""
    K = 15
    filepath = f"verify_middle/bridge_data_K{K}.csv"
    with open(filepath) as f:
        sigs = list(csv.DictReader(f))

    print(f"Decay rate for K={K}:")
    print()
    prev_count = None
    prev_L = None
    for L in [10, 20, 30]:
        survivors = [s for s in sigs if s[f"survives_L{L}"] == "True"]
        extra = [s for s in survivors if int(s["n"]) not in (0, 2, 8)]
        count = len(extra)
        if prev_count is not None and count > 0 and prev_count > 0:
            ratio = prev_count / count
            expected_ratio = (3 / 2) ** (L - prev_L)
            print(f"  L={prev_L:2d}->{L:2d}: {prev_count}->{count}, "
                  f"ratio={ratio:.1f}, expected (3/2)^{L-prev_L}={expected_ratio:.1f}")
        elif prev_count is not None and count == 0:
            print(f"  L={prev_L:2d}->{L:2d}: {prev_count}->0 (exhausted)")
        else:
            print(f"  L={L:2d}: {count} extra survivors")
        prev_count = count
        prev_L = L
    print()


if __name__ == "__main__":
    verify_final_set()
    verify_exponential_decay()
    compute_decay_rate()
