#!/usr/bin/env python3
"""
Key check: for K >= 29 and j >= 38 with Q(j)+18 < uK(K),
is Q(j)+18 < uK(28)? If so, the K=28 native_decide covers it.

Also check: for j >= 38 and ALL K >= 26 with Q(j)+18 < uK(K),
is Q(j)+18 < uK(K)? (Always true by definition.)

The question is: can we handle ALL K >= 26 using ONLY K=26..28 native_decide?
Answer: only if Q(j)+18 < uK(28) for all relevant j.
"""
import math

log32_cf = [0, 1, 1, 1, 2, 2, 3, 1, 5, 2, 23, 2, 2, 1, 1, 55]

def Al32(k):
    if k < len(log32_cf):
        return max(1, log32_cf[k])
    return 1

def compute_Q(max_j):
    Q = [0] * (max_j + 1)
    Q[0] = 1
    if max_j >= 1:
        Q[1] = 1
    for k in range(max_j - 1):
        j = k + 2
        Q[j] = Al32(j) * Q[j-1] + Q[j-2]
    return Q

def uK(K):
    return 2 * 3 ** (K - 1)

Q = compute_Q(80)

print("=== Critical check: for K >= 29, does Q(j)+18 < uK(28) for all relevant j? ===\n")

uk28 = uK(28)
print(f"uK(28) = {uk28}")

for K in range(29, 35):
    ukK = uK(K)
    # Find max j with Q(j)+18 < uK(K)
    jmax = None
    for j in range(38, 81):
        if Q[j] + 18 >= ukK:
            jmax = j - 1
            break
    if jmax is None:
        jmax = 80
    
    if jmax >= 38:
        max_Q = Q[jmax] + 18
        fits = max_Q < uk28
        print(f"K={K}: j ∈ [38, {jmax}], max Q(j)+18 = {max_Q}, < uK(28)={uk28}: {fits}")
    else:
        print(f"K={K}: no j >= 38 with Q(j)+18 < uK({K})")

print()
print("=== For K >= 29, which j values need SEPARATE verification? ===\n")

for K in range(29, 40):
    ukK = uK(K)
    jmax = None
    for j in range(38, 81):
        if Q[j] + 18 >= ukK:
            jmax = j - 1
            break
    if jmax is None:
        jmax = 80
    
    if jmax < 38:
        continue
    
    # Which j in [38, jmax] have Q(j)+18 >= uK(28)?
    uncovered = []
    for j in range(38, jmax + 1):
        if Q[j] + 18 >= uk28:
            uncovered.append(j)
    
    if uncovered:
        print(f"K={K}: j ∈ [38, {jmax}], UNCOVERED by K=28: {uncovered}")
    else:
        print(f"K={K}: j ∈ [38, {jmax}], ALL covered by K=28 verification")
