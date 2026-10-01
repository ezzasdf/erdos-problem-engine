# Erdős Ternary Conjecture: Attack Map

## The Conjecture

Every power of two has digit 2 in its ternary expansion. Equivalently, the orbit {2^n : n ≥ 1} intersects the 3-adic Cantor set C₃ = Σ₃ = {sums of distinct powers of 3} only at n = 0, 2, 8.

## What We Have Proved (Formal, Lean, 0 sorry)

| Range | Method | Status |
|-------|--------|--------|
| K=1..9 | `BridgeCompute.lean` | ✅ Verified |
| K=10..12 | `BridgeMiddle.lean` | ✅ Verified |
| K=13..14 | `BridgeK13.lean`, `BridgeK14.lean` | ✅ Verified |
| K=15..17 | `LiftEdgeK15.lean`, etc. | ✅ Verified (cloud) |
| K=18 | `BridgeK18Part1/2/3.lean` | ✅ Verified (cloud, 162 native_decide) |

## What We Know Computationally

The lifting tree is:
- N₁ = {0, 1} (size 2)
- N₂ = {0, 2, 1} (size 3)
- N_K has size 2^{K-1} for K ≥ 1
- N_K = {r < u_K : 2^r has no digit 2 in ternary positions 0..K-1}
- ∩ₖ N_K = {0, 2, 8} (verified for K up to 18)
- m_K = (2^{u_K} - 1)/3^K converges 3-adically to a limit with digits: 1, 2, 1, 0, 2, 2, 0, 1, 1, 0, 1, 2, 1, ...

## The Gap

For r ≥ u_18 = 885,732, the Erdős conjecture says 2^r always has digit 2. This is the hard part. The finite bridges K=1..18 only cover r < 885,732.

## The 3-Adic Framework (Lagarias 2009)

### Key Objects

- **C₃ = Σ₃** = 3-adic Cantor set = numbers with digits 0,1 only in base 3
- **C(1, M₁, ..., Mₖ)** = Σ₃ ∩ (1/M₁)Σ₃ ∩ ... ∩ (1/Mₖ)Σ₃ (multiplicative translates of Cantor set)
- **S(λ, ℤ₃)** = {n ≥ 1 : (λ·2^n)₃ omits digit 2} (ternary orbit hitting C₃)
- **N*(λ, ℤ₃)** = |S(λ, ℤ₃)| (cardinality of orbit hits)
- **E(λ, Z₃)** = exceptional set for the orbit

### The Conjecture in 3-Adic Language

1 ∉ E(Z₃). Equivalently, the orbit {2^n} intersects Σ₃ only finitely many times.

### What the Literature Proves

1. **Lagarias (2009)**: dim_H(E(Z₃)) ≤ 1/2
2. **Abram-Bolshakov-Lagarias (2016)**: dim_H(E(Z₃)) ≤ log₃(φ) ≈ 0.438
3. **Abram-Lagarias (2015)**: Nesting property C(M₁,...,Mₖ) ⊇ C(M₁,...,Mₖ,Mₖ₊₁)

### What Remains Open

- Is dim_H(E(Z₃)) = 0? (Conjectured yes)
- Does E(Z₃) = {0}? (This is the Erdős conjecture)
- Is there an algebraic/number-theoretic argument that forces E(Z₃) = {0}?

## Attack Strategies

### Strategy 1: Finite Automaton / Hausdorff Dimension (Most Developed)

**Idea**: Compute the Hausdorff dimension of E⁽ᵏ⁾(Z₃) = ∪₀≤m₁<...<mk C(2^{m₁}, ..., 2^{mₖ}) as k → ∞.

**Known**:
- dim_H(E⁽ᵏ⁾(Z₃)) = max_{0≤m₁<...<mk} dim_H(C(2^{m₁}, ..., 2^{mₖ}))
- dim_H(C(M₁,...,Mₖ)) = log₃(β) where β = Perron eigenvalue of adjacency matrix A
- Nesting constant Γ = lim_k dim_H(E⁽ᵏ⁾(Z₃)) ≤ log₃(φ) ≈ 0.438

**What's needed**: Prove Γ = 0. This requires showing the adjacency matrix eigenvalues shrink fast enough.

**Challenge**: The eigenvalue computation depends on the specific Mᵢ values (powers of 2). The structure of which powers of 2 are "active" at each level is complex.

### Strategy 2: Carry-Packet Analysis (Spencer 2026)

**Idea**: Study the multiplication4m = m + 3m as a ternary carry process. A carry packet is a block of consecutive digit-2 entries that propagates leftward.

**Known**:
- Primitive carry packets have finite classification
- The continuation state after a packet depends only on the next primitive pattern
- For starting digits in {0,1}, the orbit must eventually hit digit 2

**What's needed**: Prove that the set of "surviving" carry patterns (those that never produce digit 2) is finite and only includes patterns corresponding to 2^0, 2^2, 2^8.

**Challenge**: The continuation state is "free" (can be any digit in {0,1,2}), so the system is infinite-state.

### Strategy 3: 3-Adic Logarithmic Dynamics (New)

**Idea**: The map n ↦ 2n on ℤ₃* can be studied via the 3-adic logarithm. Since log₃(2) is irrational, the orbit {n · log₃(2)} is equidistributed in ℤ₃.

**Known**:
- log₃(2) exists as a 3-adic number (since log₃(1+3) = 3 - 9/2 + 27/3 - ... converges)
- The map x ↦ x + log₃(2) on ℤ₃ is ergodic with respect to Haar measure
- The Cantor set has Haar measure 0

**What's needed**: Show that the orbit of1 ∈ ℤ₃ under x ↦ x + log₃(2) must eventually leave the Cantor set.

**Critical caveat**: Ergodicity only gives almost-everywhere results. It does NOT imply that the particular orbit starting at 1 must leave Σ₃. Measure zero ≠ contains no points of this particular orbit. This argument alone cannot prove the Erdős conjecture.

### Strategy 4: S-Unit Equation Approach

**Idea**: The condition 2^n ∈ Σ₃ can be written as an equation in S-units. For example, 2^n = a₀ + a₁·3 + a₂·9 + ... with aᵢ ∈ {0,1}.

**Known**:
- S-unit equations have finitely many solutions (Evertse, Schlickewei)
- The number of solutions can be bounded effectively

**What's needed**: Formulate the Erdős conjecture as an S-unit equation and apply the effective bounds.

**Challenge**: The S-unit equation framework applies to equations in finitely many variables, but the ternary expansion has infinitely many digits.

### Strategy 5: Mahler Function Approach

**Idea**: Mahler studied Z-numbers (fractional parts of (3/2)^n in [0, 1/2)). The ternary digit problem might be reformulable as a Mahler-type functional equation.

**Known**:
- Z-numbers are connected to the Erdős conjecture (Mahler 1968)
- The set of Z-numbers is conjectured to be empty

**What's needed**: Find a functional equation satisfied by the generating function of ternary digits of 2^n and prove it has no zeros.

**Challenge**: The generating function is highly transcendental and not well understood.

### Strategy 6: Uniform Treatment via m_K Convergence (Our Contribution)

**Idea**: The convergence m_K → m_∞ in ℤ₃ gives a 3-adic limit object. The Erdős conjecture is equivalent to: for any r ∉ {0, 2, 8}, the path from r in the lifting tree eventually hits a digit-2 constraint.

**Known**:
- m_K converges 3-adically (proved in Lifting.lean)
- The offset (number of trailing digits that match) is bounded by K + O(1) (need to formalize)
- The bound is NOT a consequence of the lifting identity alone

**What's needed**: Find the right characterization of the offset and prove it's bounded.

**Note**: Computational evidence suggests a uniformly bounded post-prefix obstruction, but no proof of such a bound is currently known. Establishing it would itself constitute a major theorem.

## The Gap: Why Is This Hard?

The Erdős conjecture is equivalent to saying that the 3-adic exceptional set E(Z₃) contains only 0. But the best known result is dim_H(E(Z₃)) ≤ log₃(φ) ≈ 0.438, which is far from 0.

The difficulty is that the ternary digit structure of 2^n is "chaotic" — small changes in n can cause large changes in the ternary expansion. This makes it hard to use induction or recurrence arguments.

The finite automaton approach captures the local structure but not the global constraints. The carry-packet approach captures the propagation but not the termination. The 3-adic logarithmic approach captures the density but not the discreteness.

## What Would a Proof Look Like?

The most concrete route: **infinite survivor ⟹ infinite recurrent carry pattern ⟹ r ∈ {0,2,8}**.

This would combine:
1. **Local analysis** (carry-packet): Classify the finite set of recurrent carry patterns that never produce digit 2.
2. **Global classification**: Show that only three histories (corresponding to 2^0, 2^2, 2^8) are consistent with the lifting tree structure.

The key insight: instead of bounding the position of the eventual digit 2, ask what information an infinite survivor must carry forever.

## Research Priorities

### Priority 1: Carry-Packet / Local Obstruction → Global Classification

The lifting tree has |N_K| = 2^{K-1} with each node having exactly two surviving children. The missing theorem is:

r ∈ ∩_K N_K ⟹ r ∈ {0,2,8}

Instead of bounding the position of the eventual digit 2, ask: what information must an infinite survivor carry forever?

If the carry-packet analysis can show that every sufficiently deep survivor acquires some finite forbidden pattern unless its entire history matches one of three exceptional histories, you've got the right kind of theorem.

### Priority 2: Deep Study of Lagarias (2009) for λ=1 Specifically

Don't just ask whether dim_H E < 1 (already known, insufficient). Ask: are there stronger results specifically for λ=1 rather than arbitrary λ ∈ E(Z₃)?

A theorem saying "the exceptional set has dimension < 1" is qualitatively different from a theorem saying "1 cannot belong to the exceptional set." The latter is exactly what you need.

### Priority 3: Characterize m∞ Algebraically

The sequence m_K = (2^{u_K} - 1)/3^K converges 3-adically to m∞. Can m∞ be characterized algebraically? If it satisfies a functional equation, recurrence, or relation involving the 3-adic logarithm, that could turn the apparently chaotic carry process into something analyzable.

## Project Status

- **Finite verification**: Extremely strong (K=1..18 verified).
- **Formal infrastructure**: Very strong (NK_mono, lifting identity, unified theorem).
- **Global theorem**: Genuinely open.
- **Next objective**: Discover a theorem about infinite survivor paths, not another finite bridge.

The K=18 work is not wasted — it becomes the finite base case / verified computational laboratory for the structural theorem.

## References

1. Lagarias (2009): "Ternary expansions of powers of 2" — doi:10.1112/jlms/jdn080
2. Abram & Lagarias (2015): "Intersections of multiplicative translates of 3-adic Cantor sets"
3. Abram, Bolshakov & Lagarias (2016): "Intersections of Multiplicative Translates of 3-Adic Cantor Sets II: Two Infinite Families"
4. Spencer (2026): "A Carry-Packet Obstruction for Powers of Two with Ternary Digits in {0,1}"
5. Mahler (1968): "Arithmetische Eigenschaften der Lösungen einer Klasse von Funktionsgleichungen"
6. Erdős (1946): Original conjecture on ternary digit 2
