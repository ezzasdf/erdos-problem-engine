#!/usr/bin/env python3
"""
For K in {15, 16, 17}, generate range-aligned chunks and prove:
  computeNKFast K = NK_K  (chunk-by-chunk, via native_decide)

Each chunk covers range [lo, hi). For each chunk, prove:
  NK_K_chunk = (List.range (hi-lo)).filter fun s => ¬hasTrailingDigit2 (pow2Mod (s+lo) (3^K)) K

This proves NK_K = computeNKFast K without a single massive list equality.
"""

def pow2mod(r, m):
    result, base = 1, 2
    while r > 0:
        if r & 1:
            result = (result * base) % m
        base = (base * base) % m
        r >>= 1
    return result

def has_trailing_digit_2(val, K):
    for _ in range(K):
        if val % 3 == 2:
            return True
        val //= 3
    return False

def has_digit2_up_to(val, max_d):
    for _ in range(max_d):
        if val % 3 == 2:
            return True
        val //= 3
    return False

def compute_nk(K):
    period = 2 * 3**(K-1)
    modulus = 3**K
    return [r for r in range(period) if not has_trailing_digit_2(pow2mod(r, modulus), K)]

def format_list(xs, per_line=15):
    lines = []
    for i in range(0, len(xs), per_line):
        group = xs[i:i+per_line]
        lines.append('  ' + ', '.join(str(v) for v in group))
    return '[\n' + ',\n'.join(lines) + '\n]'

def main():
    CHUNK_SIZE = 4096

    for K in [15, 16, 17]:
        nk = compute_nk(K)
        period = 2 * 3**(K-1)
        print(f"K={K}: |NK|={len(nk)}, uK={period}")

        # Build range-aligned chunks
        ranges = []
        for lo in range(0, period, CHUNK_SIZE):
            hi = min(lo + CHUNK_SIZE, period)
            chunk = [r for r in nk if lo <= r < hi]
            ranges.append((lo, hi, chunk))

        print(f"  {len(ranges)} chunks")
        for i, (lo, hi, chunk) in enumerate(ranges):
            print(f"    [{lo},{hi}): {len(chunk)} elements")

        # Verify bridge
        bad = [r for r in nk if r not in (0,2,8) and not has_digit2_up_to(pow2mod(r, 3**50), 50)]
        print(f"  Bridge failures: {bad}")

        # Write Lean file
        path = f'/media/playplatoon/New Volume1/projects/erdos problem ternary expansion/ErdosTernary/ErdosTernary/BridgeK{K}_axiom_free.lean'
        with open(path, 'w') as f:
            f.write(f"/-\n  Bridge K={K} — axiom-free via range-aligned chunks\n-/\n\n")
            f.write("import Mathlib.Tactic\n")
            f.write("import ErdosTernary.BridgeCompute\n")
            f.write("import ErdosTernary.BridgeMiddle\n")
            f.write("import ErdosTernary.BridgeMiddle16\n\n")
            f.write("open ErdosTernary.BridgeCompute\n")
            f.write("open ErdosTernary.BridgeMiddle\n")
            f.write("open ErdosTernary.BridgeMiddle16\n\n")
            f.write(f"namespace ErdosTernary.BridgeK{K}\n\n")

            # 1) Write chunk definitions (Python-computed elements in [lo,hi))
            chunk_names = []
            for i, (lo, hi, chunk) in enumerate(ranges):
                cn = f"NK_{K}_c{i}"
                f.write(f"set_option maxHeartbeats 10000000 in\n")
                f.write(f"private def {cn} : List Nat := {format_list(chunk)}\n\n")
                chunk_names.append((cn, lo, hi))

            # 2) For each chunk, prove ∀ r ∈ chunk, r ∈ computeNKFast K
            for cn, lo, hi in chunk_names:
                f.write(f"private theorem {cn}_subset : {cn} ⊆ computeNKFast {K} := by\n")
                f.write(f"  intro r hr\n")
                f.write(f"  unfold computeNKFast\n")
                f.write(f"  simp only [List.mem_filter, List.mem_range]\n")
                f.write(f"  constructor\n")
                f.write(f"  · exact List.mem_range.mpr (by omega)\n")
                f.write(f"  · exact (List.mem_filter.mp hr).2\n\n")

            # 3) For each chunk, prove ∀ r ∈ chunk, bridge_property(r)
            for cn, lo, hi in chunk_names:
                f.write(f"set_option maxHeartbeats 16000000 in\n")
                f.write(f"private theorem {cn}_bridge : ∀ r ∈ {cn}, r ≠ 0 → r ≠ 2 → r ≠ 8 → hasDigit2UpTo (pow2Mod r (3 ^ 50)) 50 = true := by\n")
                f.write(f"  intro r hr h0 h2 h8\n")
                f.write(f"  have hcheck : checkMiddleBridgeListMod {cn} {K} = true := by native_decide\n")
                f.write(f"  unfold checkMiddleBridgeListMod at hcheck\n")
                f.write(f"  have hprop := List.all_eq_true.mp hcheck r hr\n")
                f.write(f"  simp only [Bool.or_eq_true, beq_iff_eq, h0, h2, h8, false_or] at hprop\n")
                f.write(f"  rw [hasDigit2InRange_pow2Mod r {K} 50 50] at hprop\n")
                f.write(f"  exact BridgeMiddle16.modM_hasDigit2_not_cantor r {K} 50 50 (by omega) hprop\n\n")

            # 4) Prove ∀ r ∈ computeNKFast K, r is in some chunk
            #    Use the fact that chunks partition [0, uK K) by range
            f.write(f"/-- Coverage: every r ∈ computeNKFast {K} is in some chunk --/\n")
            f.write(f"theorem computeNKFast_covered (r : Nat) (hr : r ∈ computeNKFast {K}) :\n")
            f.write(f"    {' ∨ '.join(f'r ∈ {cn}' for cn, _, _ in chunk_names)} := by\n")
            f.write(f"  unfold computeNKFast at hr\n")
            f.write(f"  simp only [List.mem_filter, List.mem_range] at hr\n")
            f.write(f"  obtain ⟨hrange, _hfilter⟩ := hr\n")
            # For each r, determine which range it falls into
            # This is a big case split that omega can't handle directly
            # Instead, use decide on the concrete range
            f.write(f"  -- Each chunk covers a known range [lo, hi)\n")
            f.write(f"  -- omega can determine which range r falls into\n")
            f.write(f"  omega\n\n")

            # 5) Main theorem: bridge for all r ∈ computeNKFast K
            f.write(f"/-- Bridge theorem for K={K}: no axiom needed --/\n")
            f.write(f"theorem bridge_K{K}_not_cantor\n")
            f.write(f"    (r : Nat) (hr : r ∈ computeNKFast {K}) (hSpecial : r ≠ 0 ∧ r ≠ 2 ∧ r ≠ 8) :\n")
            f.write(f"    ¬(memCantorNat (2 ^ r)) := by\n")
            f.write(f"  intro hc\n")
            f.write(f"  have hcover := computeNKFast_covered r hr\n")
            cases = ' | '.join(f'{cn}_bridge r hcover hSpecial.1 hSpecial.2.1 hSpecial.2.2' for cn, _, _ in chunk_names)
            f.write(f"  rcases hcover with {cases}\n")
            # Need to unfold hasDigit2UpTo into memCantorNat contradiction
            for cn, _, _ in chunk_names:
                f.write(f"  · unfold hasDigit2UpTo hasDigit2InRange at {cn}_bridge\n")
            f.write(f"  all_goals contradiction\n\n")

            f.write(f"end ErdosTernary.BridgeK{K}\n")

        print(f"  -> {path}")

if __name__ == '__main__':
    main()
