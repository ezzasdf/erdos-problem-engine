#!/usr/bin/env python3
"""
Part 1: Compute and prove 2^(uK K) ≡ 1 + c·3^K mod 3^(K+1)
Part 2: Prove exactly-two-lifts from the algebraic structure
"""

def uk(K):
    return 2 * (3 ** (K - 1))

# ============================================================
# PART 1: The exact formula for 2^(uK K) mod 3^(K+1)
# ============================================================
print("="*80)
print("PART 1: 2^(uK K) mod 3^(K+1)")
print("="*80)

print(f"\n{'K':>3} {'uK':>14} {'2^uK mod 3^(K+1)':>20} {'c':>4} {'c%3':>4} {'cube_root':>10}")
print("-"*70)

for K in range(1, 25):
    u = uk(K)
    modulus = 3 ** (K + 1)
    val = pow(2, u, modulus)
    three_k = 3 ** K
    c = ((val - 1) % modulus) // three_k
    is_cube = pow(val, 3, modulus) == 1
    print(f"{K:3d} {u:14d} {val:20d} {c:4d} {c%3:4d} {'YES' if is_cube else 'NO':>10}")

# ============================================================
# PART 2: The algebraic proof
# ============================================================
print("\n" + "="*80)
print("PART 2: The Algebraic Proof")
print("="*80)

print("""
THEOREM (Exactly-Two-Lifts):

For K ≥ 1, define u_K = 2·3^{K-1} and let c_K be the unique integer 
with 0 < c_K < 3 such that:

  2^{u_K} ≡ 1 + c_K · 3^K  (mod 3^{K+1})

Then c_K ≢ 0 (mod 3) for all K ≥ 1.

PROOF that c_K ≢ 0 (mod 3):

  We show 2^{u_K} ≢ 1 (mod 3^{K+1}).
  
  By the lifting-the-exponent lemma:
    v_3(2^{2·3^K} - 1) = v_3(2^2 - 1) + v_3(3^K) = 1 + K
  So 2^{2·3^K} ≡ 1 (mod 3^{K+1}) but 2^{2·3^K} ≢ 1 (mod 3^{K+2}).
  
  Since u_K = 2·3^{K-1} = (2·3^K)/3, we have:
    2^{3·u_K} = 2^{2·3^K} ≡ 1 (mod 3^{K+1})
  
  So 2^{u_K} is a cube root of 1 mod 3^{K+1}.
  The cube roots of 1 mod 3^{K+1} are exactly 3 elements.
  
  Write 2^{u_K} = 1 + d·3^K mod 3^{K+1}.
  Then (1 + d·3^K)^3 ≡ 1 + 3d·3^K ≡ 1 + d·3^{K+1} ≡ 1 (mod 3^{K+1}).
  This holds for ANY d.
  
  But we need 2^{u_K} ≢ 1, i.e., d ≢ 0 (mod 3).
  This follows from v_3(2^{u_K} - 1) = K (not K+1), which we can verify:
  
  v_3(2^{u_K} - 1) = v_3(2^{2·3^{K-1}} - 1)
  By LTE: v_3(2^{2·3^{K-1}} - 1) = v_3(2^2 - 1) + v_3(3^{K-1}) = 1 + (K-1) = K
  
  So 2^{u_K} - 1 is divisible by 3^K but NOT by 3^{K+1}, 
  meaning d ≢ 0 (mod 3). ∎


THEOREM (Three-Digit-Distinct):

For r ∈ N_K (so the K trailing digits of 2^r in base 3 contain no 2),
the three lifts r, r+u_K, r+2·u_K give 2^r, 2^{r+u_K}, 2^{r+2·u_K}
whose K-th ternary digits are all distinct.

PROOF:

  Write 2^r mod 3^{K+1} = a + b·3^K where 0 ≤ a < 3^K, 0 ≤ b < 3.
  The K-th digit of 2^r is b.
  
  Since r ∈ N_K, we know 2^r mod 3^K = a has no digit 2 in base 3.
  In particular, 2^r mod 3 ∈ {1, 2} (since 2^r mod 3 alternates 1,2,1,2,...),
  so a ≢ 0 (mod 3).
  
  The three lifts give K-th digits:
    d₀ = b                        (from 2^r)
    d₁ = (b + a·c_K) mod 3        (from 2^{r+u_K})
    d₂ = (b + 2·a·c_K) mod 3      (from 2^{r+2·u_K})
    
  where c_K is as above with c_K ≢ 0 (mod 3).
  
  The common difference is Δ = (a·c_K) mod 3.
  Since a ≢ 0 (mod 3) and c_K ≢ 0 (mod 3), we have Δ ≢ 0 (mod 3).
  
  Therefore d₀, d₁, d₂ = b, b+Δ, b+2Δ (mod 3) are three distinct 
  values modulo 3, hence they are exactly {0, 1, 2} in some order.
  
  Exactly one of them equals 2, so exactly one lift has a digit 2 
  at position K, so exactly two lifts survive into N_{K+1}. ∎


COROLLARY (Exponential Growth):

  |N_{K+1}| = 2·|N_K| for all K ≥ 1.
  With |N_1| = 2 (N_1 = {0, 2}), we get |N_K| = 2^K for all K ≥ 1.

  Wait — our data shows |N_5| = 16 = 2^4, not 2^5. Let me reconcile.
  
  Actually, N_1 has |N_1| = u_1/... Let me recheck.
  u_1 = 2. N_1 = {r ∈ [0,2) : 2^r mod 3 has no digit 2 in pos 0}
  = {r ∈ {0,1} : 2^r mod 3 ≠ 2}
  = {r : 2^r mod 3 ≠ 2}
  2^0 mod 3 = 1 ✓, 2^1 mod 3 = 2 ✗
  So N_1 = {0}, |N_1| = 1.
  
  Hmm, but the formula says |N_K| = 2^{K-1}. For K=1: 2^0 = 1 ✓.
  For K=5: 2^4 = 16 ✓.
""")

# Verify base cases
print("\nBase case verification:")
for K in range(1, 8):
    u = uk(K)
    modulus = 3 ** K
    nk = []
    for r in range(u):
        p = pow(2, r, modulus)
        v = p
        has2 = False
        for _ in range(K):
            if v % 3 == 2:
                has2 = True
                break
            v //= 3
        if not has2:
            nk.append(r)
    print(f"  K={K}: |N_K| = {len(nk)} = 2^{K-1}? {len(nk) == 2**(K-1)}  elements: {nk[:8]}{'...' if len(nk) > 8 else ''}")

# ============================================================
# PART 3: The c_K values and their pattern
# ============================================================
print("\n" + "="*80)
print("PART 3: The c_K values")
print("="*80)

print(f"\n{'K':>3} {'c_K':>6} {'c_K mod 3':>10} {'hex':>6}")
print("-"*30)

c_values = []
for K in range(1, 25):
    u = uk(K)
    modulus = 3 ** (K + 1)
    val = pow(2, u, modulus)
    three_k = 3 ** K
    c = ((val - 1) % modulus) // three_k
    c_values.append(c)
    print(f"{K:3d} {c:6d} {c%3:10d} {c:6x}")

# Check if c_K has a pattern
print(f"\nc_K values: {c_values[:15]}")
print(f"c_K mod 3: {[c%3 for c in c_values[:15]]}")

# Try to find recurrence
print("\nTrying to find a pattern in c_K...")
for K in range(1, 14):
    # Check if c_{K+1} relates to c_K
    ratio = c_values[K] / c_values[K-1] if c_values[K-1] != 0 else float('inf')
    diff = c_values[K] - c_values[K-1]
    print(f"  c_{K+1}/c_K = {c_values[K]}/{c_values[K-1]} = {ratio:.4f}  diff = {diff}")
