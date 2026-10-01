#!/usr/bin/env python3
"""
Deep analysis of the N_K lifting structure.
Focus on: death patterns, digit-2 positions, tree structure, stabilization.
"""

from collections import defaultdict
import sys
import time

def pow2_mod(r, m):
    return pow(2, r, m)

def has_trailing_digit_2(val, K):
    v = val
    for _ in range(K):
        if v % 3 == 2:
            return True
        v //= 3
    return False

def uk(K):
    if K <= 0: return 1
    return 2 * (3 ** (K - 1))

def compute_nk(K):
    period = uk(K)
    modulus = 3 ** K
    result = []
    for r in range(period):
        p = pow2_mod(r, modulus)
        if not has_trailing_digit_2(p, K):
            result.append(r)
    return set(result)

def find_first_digit2_above(val, K, max_pos=100):
    """Find the first position >= K where the base-3 digit of val is 2."""
    v = val
    for pos in range(max_pos):
        if pos >= K and v % 3 == 2:
            return pos
        v //= 3
    return None  # No digit 2 found in positions K..max_pos

def deep_analysis():
    # Compute N_K
    print("Computing N_K for K=5..17...")
    sys.stdout.flush()
    nk = {}
    for K in range(5, 18):
        t0 = time.time()
        nk[K] = compute_nk(K)
        t1 = time.time()
        print(f"  K={K}: |N_K|={len(nk[K]):6d}  ({t1-t0:.1f}s)")
        sys.stdout.flush()
    
    # ============== DEEP ANALYSIS 1: Death pattern analysis ==============
    print("\n" + "="*80)
    print("DEEP ANALYSIS 1: What distinguishes elements that die vs survive?")
    print("="*80)
    
    for K in range(5, 17):
        period_k = uk(K)
        nk_k = nk[K]
        nk_k1 = nk[K + 1]
        
        survive_as_base = []  # pattern {0,...}: r ∈ N_{K+1}
        die = []              # pattern {1,2}: r ∉ N_{K+1}
        
        for r in sorted(nk_k):
            r_survives = r in nk_k1
            if r_survives:
                survive_as_base.append(r)
            else:
                die.append(r)
        
        print(f"\nK={K}→{K+1}:")
        print(f"  Survive as base: {len(survive_as_base)}/{len(nk_k)} ({100*len(survive_as_base)/len(nk_k):.1f}%)")
        print(f"  Die (only shifted copies survive): {len(die)}/{len(nk_k)} ({100*len(die)/len(nk_k):.1f}%)")
        
        if die:
            print(f"  Dying elements (first 10): {die[:10]}")
            # Check mod 3 of dying elements
            mod3_die = defaultdict(int)
            for r in die:
                mod3_die[r % 3] += 1
            print(f"  mod 3 of dying: {dict(sorted(mod3_die.items()))}")
        
        if survive_as_base:
            mod3_surv = defaultdict(int)
            for r in survive_as_base:
                mod3_surv[r % 3] += 1
            print(f"  mod 3 of surviving: {dict(sorted(mod3_surv.items()))}")
    
    # ============== DEEP ANALYSIS 2: Digit-2 position tracking ==============
    print("\n" + "="*80)
    print("DEEP ANALYSIS 2: First digit-2 position above K for non-special elements")
    print("="*80)
    
    special = {0, 2, 8}
    for K in range(5, 18):
        nk_k = nk[K]
        non_special = sorted(nk_k - special)
        
        # For each non-special r ∈ N_K, find the first digit 2 at position >= K
        positions = []
        max_pos_found = 0
        for r in non_special:
            p = pow2_mod(r, 3 ** 50)  # Compute mod 3^50 for digit extraction
            pos = find_first_digit2_above(p, K, 50)
            if pos is not None:
                positions.append((r, pos))
                max_pos_found = max(max_pos_found, pos)
            else:
                positions.append((r, None))
        
        found = sum(1 for _, p in positions if p is not None)
        not_found = sum(1 for _, p in positions if p is None)
        
        # Distribution of first digit-2 positions
        pos_dist = defaultdict(int)
        for _, p in positions:
            if p is not None:
                pos_dist[p] += 1
        
        print(f"\nK={K:2d}: |NS|={len(non_special):5d}  "
              f"digit2 found in K..49: {found:5d}  not found: {not_found:5d}")
        if pos_dist:
            for pos in sorted(pos_dist.keys()):
                print(f"  first digit2 at position {pos}: {pos_dist[pos]:5d}")
    
    # ============== DEEP ANALYSIS 3: The binary tree structure ==============
    print("\n" + "="*80)
    print("DEEP ANALYSIS 3: Binary tree structure — parent→child mapping")
    print("="*80)
    
    # For each r ∈ N_K, its two children in N_{K+1} are:
    # - one of: r (if survives), r+u_K, r+2u_K
    # Let's characterize which two lifts survive
    
    for K in range(5, 17):
        period_k = uk(K)
        nk_k = nk[K]
        nk_k1 = nk[K + 1]
        
        # Count lift patterns
        patterns = defaultdict(int)
        for r in nk_k:
            survives_base = r in nk_k1
            survives_s1 = (r + period_k) in nk_k1
            survives_s2 = (r + 2 * period_k) in nk_k1
            pat = (survives_base, survives_s1, survives_s2)
            patterns[pat] += 1
        
        print(f"\nK={K}→{K+1}:")
        for pat, count in sorted(patterns.items()):
            label = []
            if pat[0]: label.append("base")
            if pat[1]: label.append("+u")
            if pat[2]: label.append("+2u")
            print(f"  {{{'+'.join(label) if label else 'NONE'}}}: {count:5d}")
    
    # ============== DEEP ANALYSIS 4: Stabilization check ==============
    print("\n" + "="*80)
    print("DEEP ANALYSIS 4: Does the tree eventually force digit-2 above K?")
    print("="*80)
    
    # For each non-special r ∈ N_5, follow it through the tree
    # At each level, check if it has a digit 2 in positions K..49
    # Track the "survival path" and the digit-2 position
    
    print("\nFollowing elements of N_5 through the tree (tracking digit-2 positions):")
    
    # Build forward map: (K, r) -> children in N_{K+1}
    forward = {}
    for K in range(5, 17):
        period_k = uk(K)
        for r in nk[K]:
            children = set()
            for lr in [r, r + period_k, r + 2 * period_k]:
                if lr in nk[K + 1]:
                    children.add(lr)
            forward[(K, r)] = children
    
    # For each r ∈ N_5, find all paths through the tree to N_17
    # and check digit-2 positions at each level
    print("\nPaths from N_5 to N_17 (showing digit-2 position at each level):")
    
    for r5 in sorted(nk[5]):
        if r5 in special:
            continue
        
        # BFS through the tree
        # state: (K, r, digit2_pos_at_K)
        queue = [(5, r5)]
        paths = []
        
        while queue:
            K_cur, r_cur = queue.pop(0)
            
            p = pow2_mod(r_cur, 3 ** 50)
            d2pos = find_first_digit2_above(p, K_cur, 50)
            
            if K_cur == 17:
                paths.append((r_cur, d2pos))
                continue
            
            children = forward.get((K_cur, r_cur), set())
            for child in sorted(children):
                queue.append((K_cur + 1, child))
        
        # Summarize paths
        print(f"\n  r=5 starting from {r5}:")
        print(f"    Number of paths to N_17: {len(paths)}")
        
        # Group by final position
        final_groups = defaultdict(list)
        for r_end, d2pos in paths:
            final_groups[d2pos].append(r_end)
        
        for d2pos in sorted(final_groups.keys(), key=lambda x: (x is None, x)):
            elems = final_groups[d2pos]
            if d2pos is None:
                print(f"    No digit 2 in K..49 at K=17: {len(elems)} elements")
            else:
                print(f"    First digit2 at pos {d2pos} at K=17: {len(elems)} elements")
    
    # ============== DEEP ANALYSIS 5: Residue structure ==============
    print("\n" + "="*80)
    print("DEEP ANALYSIS 5: N_K structure modulo uK/3 and uK/9")
    print("="*80)
    
    for K in range(5, 18):
        nk_k = nk[K]
        period = uk(K)
        
        # mod 9 structure
        mod9 = defaultdict(int)
        for r in nk_k:
            mod9[r % 9] += 1
        
        # Which mod-9 residues appear?
        active = sorted(mod9.keys())
        print(f"K={K:2d}: active mod 9 residues: {active}  counts: {[mod9[a] for a in active]}")
    
    print("\n" + "="*80)
    print("DEEP ANALYSIS COMPLETE")
    print("="*80)


if __name__ == "__main__":
    deep_analysis()
