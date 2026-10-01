# Spec: Formalizing Narkiewicz's Counting Bound for Erdős Ternary Conjecture

## Objective
Formalize Narkiewicz's 1980 result in Lean 4: for any nonzero λ ∈ Z₃, the number of n ≤ X whose base-3 representation of λ·2ⁿ omits digit 2 is at most 2X^{α₀} where α₀ = log₃(2) ≈ 0.6309.

This bound implies the Erdős ternary conjecture for all large n: if 2ⁿ omits digit 2, then n ≤ 8.

## Background

### Statement (Theorem 1.4 from Lagarias 2009)
For λ a nonzero 3-adic integer, let Ñ_λ(X) denote the number of integers n in {0, 1, ..., ⌊X⌋-1} whose base-3 representation of λ·2ⁿ omits the digit 2. Then:

Ñ_λ(X) ≤ 2X^{α₀}

where α₀ = log₃(2).

### Proof Strategy (from Lagarias)
The proof uses the self-similar structure of 3-adic integers:

1. **Cantor set characterization**: Numbers in Z₃ whose base-3 representation uses only digits 0 and 1 form a Cantor set C₃ ⊂ Z₃.

2. **Digit restriction**: (λ·2ⁿ)₃ omits digit 2 ⟺ λ·2ⁿ ∈ C₃

3. **Key counting argument**: The set {n : λ·2ⁿ ∈ C₃} has "dimension" α₀ in a suitable sense, leading to the bound 2X^{α₀}.

4. **Proof structure**: 
   - For each n, write λ·2ⁿ in base 3
   - The condition that digit 2 is absent constrains which residues mod 3^k are possible
   - Using the structure of multiplication by 2 mod 3^k, one bounds the number of valid n

### Connection to Erdős Conjecture
If 2ⁿ omits digit 2, then (2ⁿ)₃ omits digit 2, which means 1·2ⁿ ∈ C₃. By Narkiewicz's bound, the number of such n ≤ X is at most 2X^{α₀}. For X > 8, this count exceeds X for sufficiently large X, which is a contradiction unless the count is small. Combined with computational verification up to K=40 (n ≤ 9×10¹⁷), this implies the Erdős conjecture.

## Tech Stack
- Lean 4 (leanprover/lean4:v4.12.0)
- Mathlib4 (latest)
- Dependencies: Mathlib.NumberTheory.Padics.* (PadicInt, PadicNorm)

## Project Structure
```
ErdosTernary/
├── ErdosTernary/
│   ├── SayeLemma.lean          (existing - zero sorry's)
│   ├── TernaryExp.lean         (existing)
│   ├── PowTwoDigitTwo.lean     (existing)
│   └── Narkiewicz.lean         (NEW - main formalization)
```

## Formalization Plan

### Phase 1: Infrastructure
Define the core mathematical objects.

#### 1.1 Ternary Digit Extraction
```lean
/-- The k-th digit (from least significant) of n in base 3 -/
def digit₃ (n : ℕ) (k : ℕ) : ℕ := (n / 3^k) % 3
```

#### 1.2 Cantor Set Definition  
```lean
/-- A 3-adic integer belongs to the Cantor set if all its ternary digits are in {0,1} -/
def memCantorSet₃ (x : ℤ_[3]) : Prop :=
  ∀ k : ℕ, digit₃ (x.valuation) k ≠ 2
```

### Phase 2: Core Lemma
#### 2.1 Digit Restriction Lemma
```lean
/-- The ternary representation of λ·2ⁿ omits digit 2 iff λ·2ⁿ ∈ C₃ -/
lemma digit2_absent_iff_mem_cantor {λ : ℤ_[3]} {n : ℕ} (hλ : λ ≠ 0) :
  (∀ k, digit₃ (λ * 2^n) k ≠ 2) ↔ memCantorSet₃ (λ * 2^n)
```

### Phase 3: Counting Bound
#### 3.1 Counting Function
```lean
/-- Number of n < X with (λ·2ⁿ)₃ omitting digit 2 -/
noncomputable def Ñ (λ : ℤ_[3]) (X : ℝ) : ℕ :=
  {n : ℕ | n < ⌊X⌋ ∧ ∀ k, digit₃ (λ * 2^n) k ≠ 2}.ncard
```

#### 3.2 Narkiewicz's Bound
```lean
/-- Narkiewicz's counting bound: Ñ_λ(X) ≤ 2X^{α₀} -/
theorem narkiewicz_bound {λ : ℤ_[3]} (hλ : λ ≠ 0) (X : ℝ) (hX : 1 ≤ X) :
  Ñ λ X ≤ 2 * X ^ (Real.log 2 / Real.log 3)
```

## Success Criteria
1. All definitions compile without sorry
2. Core lemma (digit restriction characterization) proved
3. Narkiewicz's bound stated and proved (or partially proved with sorry for difficult parts)
4. File integrates with existing project structure
5. `lake build` passes

## Open Questions
1. Should we formalize the full analytic proof or use a combinatorial approach?
2. What level of generality for λ (nonzero 3-adic integer vs. rational)?
3. How to handle the measure-theoretic aspects (Hausdorff dimension)?

## Risk Assessment
- **High risk**: The proof uses 3-adic analysis which may require new infrastructure
- **Mitigation**: Start with rational λ ∈ Z₃, use existing Mathlib p-adic library
- **Alternative**: Formalize only the statement + computational verification, defer full proof
