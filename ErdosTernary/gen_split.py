#!/usr/bin/env python3
# Copyright (c) 2026 Ezzeldin Ashraf Mohamed Shafey Wahba. All rights reserved.
# Released under the PolyForm Strict License 1.0.0 as described in the file LICENSE-CODE.
# Authors: Ezzeldin Ashraf Mohamed Shafey Wahba
"""Generate split n5_digitMod_covers theorems, one per N5 residue."""

N5 = [0, 2, 8, 20, 24, 26, 54, 56, 62, 72, 74, 78, 80, 96, 126, 150]

for s in N5:
    # Find which k values give s + 162*k >= 69
    min_k = max(0, -(- (69 - s) // 162))  # ceiling division
    print(f"n5_covers_{s}: ∀ k ∈ Finset.range 59049, k ≥ {min_k} → ∃ j ∈ Finset.range 38, digitMod ({s} + 162 * k) (j + 5) = 2")
    print(f"  -- k ranges from {min_k} to 59048, that's {59049 - min_k} cases")
