#!/usr/bin/env python3
"""Phase 3: Check the 39 failing cases for actual j needed."""

N5_even = [0, 2, 8, 20, 24, 26, 54, 56, 62, 72, 74, 78, 80, 96, 126, 150]
K_MAX = 59049
PERIOD = 162

def digit_j_of_2_to_n(n, j):
    m = 3 ** (j + 1)
    return (pow(2, n, m) // (3 ** j)) % 3

def main():
    # Find all failures for j < 30
    failures = []
    for s in N5_even:
        for k in range(K_MAX):
            r = s + PERIOD * k
            if r < 48:
                continue
            found = False
            for j in range(5, 30):
                if digit_j_of_2_to_n(r, j) == 2:
                    found = True
                    break
            if not found:
                failures.append((s, k, r))
    
    print(f"Found {len(failures)} failures for j < 30")
    
    # For each failure, find actual j needed
    print("\n--- Actual j needed for failures ---")
    for s, k, r in failures[:50]:  # check first 50
        for j in range(30, 200):
            if digit_j_of_2_to_n(r, j) == 2:
                print(f"  s={s:3d}, k={k:5d}, r={r:10d}: first j = {j}")
                break
        else:
            print(f"  s={s:3d}, k={k:5d}, r={r:10d}: NO j < 200!")
    
    # Also check: does EVERY r eventually have a digit 2?
    # This is guaranteed by our theorem (r >= 48, even, N5 → digit 2 exists)
    # but let's verify for the failures
    print("\n--- Checking j up to 100 for all failures ---")
    max_j = 0
    for s, k, r in failures:
        for j in range(30, 100):
            if digit_j_of_2_to_n(r, j) == 2:
                if j > max_j:
                    max_j = j
                break
        else:
            print(f"  NO j < 100: s={s}, k={k}, r={r}")
    print(f"  Max j needed among failures: {max_j}")
    
    # Actually, these 39 failures should not exist for N5 r >= 48
    # Let me verify: are these r values actually N5?
    print("\n--- Verifying N5 property for failures ---")
    for s, k, r in failures[:5]:
        is_n5 = all(digit_j_of_2_to_n(r, j) in (0, 1) for j in range(5))
        print(f"  s={s}, k={k}, r={r}: N5 = {is_n5}")
        if is_n5:
            # Show all digits 5-10
            for j in range(5, 40):
                d = digit_j_of_2_to_n(r, j)
                if d != 0 and d != 1:
                    print(f"    First non-{0,1} digit: j={j}, digit={d}")
                    break
            else:
                print(f"    All digits 5-39 are 0 or 1!")
    
    # Wait - I need to reconsider. The N5 condition is for j < 5 only.
    # digit_j(2^r) ∈ {0,1} for j = 0,1,2,3,4.
    # For j >= 5, the digit can be 0, 1, or 2.
    # These failures have no digit 2 in positions 5-29.
    # But we need digit 2 SOMEWHERE (any position) to disprove Cantor membership.
    # Actually, we need digit 2 at position j where j < K_star(r).
    # For r >= 48, K_star(r) >= 30 (since 3^30 > 2^48).
    # So j < 30 is sufficient!
    
    # Wait, that means the 39 failures DON'T have any digit 2 in positions 5-29.
    # But K_star(249968) = log3Floor(2^249968).
    # 2^249968 has about 249968 * log10(2) ≈ 75272 decimal digits.
    # K_star is about 249968 * log2(3) ≈ 249968 / 1.585 ≈ 157,700.
    # So K_star is much larger than 30.
    
    # The theorem says: digit_j(criticalGap r) = 2 for SOME j.
    # By our transfer: digit_j(criticalGap r) = digit_j(2^r) for j < K_star.
    # So we need digit_j(2^r) = 2 for SOME j < K_star.
    # For r >= 48, K_star > 30. So we need j < K_star.
    # The current approach checks j = 5, ..., j_max.
    # If j_max < K_star, we're fine.
    # For r ~ 250K, K_star ~ 157K. So j up to 29 is definitely < K_star.
    
    # BUT the failures show NO digit 2 at ALL for j = 5, ..., 29.
    # This means digit_j(2^r) ∈ {0, 1} for j = 5, ..., 29.
    # Combined with the N5 property (j < 5), this means digit_j(2^r) ∈ {0, 1}
    # for j = 0, ..., 29. That's 30 consecutive digits without a 2.
    # This is fine - we just need SOME j < K_star with digit 2.
    # So we need to check j = 30, 31, ... until we find one.
    
    # But for the Lean certificate, we need a BOUNDED j.
    # Let me check: what is the max j needed for ANY r < 162*59049?
    print("\n=== Finding max j for ALL r < 162*59049 ===")
    max_j_all = 0
    worst_r = 0
    total = 0
    for s in N5_even:
        for k in range(K_MAX):
            r = s + PERIOD * k
            if r < 48:
                continue
            total += 1
            for j in range(5, 500):
                if digit_j_of_2_to_n(r, j) == 2:
                    if j > max_j_all:
                        max_j_all = j
                        worst_r = r
                    break
            else:
                print(f"  NO j < 500: r={r}")
    print(f"  Total: {total}, Max j: {max_j_all}, worst r: {worst_r}")

if __name__ == "__main__":
    main()
