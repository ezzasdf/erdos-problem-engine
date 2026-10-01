# Mass-1 Dynamics & Displacement Interface Design

**Date:** 2026-08-27
**Status:** Approved
**Scope:** Phase A (conditional birth/death theorem, no new axioms) + Phase B (interface for displacement→Cantor theorem)

---

## Context

The `ostrowski_invariant` axiom in `BridgeUniform.lean:44-47` is the single remaining unproved axiom in the bridge proof (excluding `erdos_conjecture` which is an isolated placeholder). It asserts:

```lean
axiom ostrowski_invariant :
  ∀ K, K ≥ 12 →
  ∀ r, r ∈ computeNK K → r ≠ 0 → r ≠ 2 → r ≠ 8 →
  ¬(memCantorNat (2 ^ r))
```

**Goal:** Replace this axiom with a structured proof in two phases:
- **Phase A:** Formalize the mass-1 population dynamics (birth/death) and prove mass-1 emptiness for K ≥ 12. No new axioms.
- **Phase B:** Create an interface for the unresolved displacement→Cantor theorem. Do not assert mass ≥ 2 alone implies avoidance (known counterexamples refute that).

**Critical insight from `OSTROWSKI_MAXCOEFF_FINDINGS.md:82-101`:** The coefficient condition Σ b_k ≥ 2 is **not sufficient alone** to imply ¬(memCantorNat (2^r)). Explicit counterexamples exist (r=26379, r=116655). The correct chain requires both mass condition AND N_K membership, via an explicit displacement argument on {rα}.

---

## Phase A: Mass-1 Dynamics (No New Axioms)

### Definitions

**File:** New file `ErdosTernary/Mass1Dynamics.lean` (or extend `OstrowskiFormLemma.lean`)

```lean
/-- r has the "mass-1 form": r = Q Al32 j + ℓ for some j ≥ 5, ℓ ≤ 18.
    This is the characterization from mass_one_iff: the Ostrowski greedy
    decomposition has exactly one nonzero coefficient at position ≥ 5,
    equal to 1, with all others zero. -/
def isMassOneForm (r : ℕ) : Prop :=
  ∃ j ℓ, 5 ≤ j ∧ ℓ ≤ 18 ∧ r = Q Al32 j + ℓ

/-- The mass-1 elements within N_K, as a filtered list. -/
def mass1_in_NK (K : ℕ) : List ℕ :=
  (computeNK K).filter isMassOneForm
```

### Theorems

#### 1. Mass-1 form characterization (`mass1_form_eq`)

Connects `mass_one_iff` to `isMassOneForm`:

```lean
theorem mass1_form_eq (r : ℕ) :
    (∃ j, 5 ≤ j ∧ gd Al32 Al32_hyp j r = 1 ∧
      ∀ k, 5 ≤ k → k ≠ j → gd Al32 Al32_hyp k r = 0) ↔ isMassOneForm r
```

**Proof:** Forward direction: from `mass_one_iff`, the LHS is equivalent to `∃ j ℓ, 5 ≤ j ∧ ℓ ≤ 18 ∧ r = Q Al32 j + ℓ`, which is `isMassOneForm r`. Backward direction: from `coef_unique_of_form`.

#### 2. Base case emptiness (`mass1_in_NK_empty_K12`)

```lean
theorem mass1_in_NK_empty_K12 : mass1_in_NK 12 = [] := by native_decide
```

**Proof:** `computeNK 12` is a concrete list of 2048 elements. `native_decide` checks that none satisfy `isMassOneForm`. This works because:
- `computeNK 12` is computable (2^11 = 2048 residues, each < u_12 = 354294)
- `isMassOneForm` is decidable (bounded search over j ≤ ~15, ℓ ≤ 18)
- The check runs in compiled C code via `native_decide`

#### 3. Extended verification (`mass1_in_NK_empty_K13_through_16`)

```lean
theorem mass1_in_NK_empty_K13 : mass1_in_NK 13 = [] := by native_decide
theorem mass1_in_NK_empty_K14 : mass1_in_NK 14 = [] := by native_decide
theorem mass1_in_NK_empty_K15 : mass1_in_NK 15 = [] := by native_decide
theorem mass1_in_NK_empty_K16 : mass1_in_NK 16 = [] := by native_decide
```

**Note:** K=16 has 32768 elements. `native_decide` may hit memory limits. If so, use a computational certificate approach: compute in Python, export the check result as a Lean `theorem` with `by native_decide`.

#### 4. Conditional extinction theorem (`conditional_extinction`)

```lean
/-- If the mass-1 population is empty at K0 ≥ 12 and no new mass-1 births
    occur at any K > K0, then the population stays empty for all K ≥ K0.

    The "no new births" condition captures the empirical fact that all 8
    births into the mass-1 class occur at K ≤ 7 (see ostrowski_birthdeath_census.py).
    For K > 7, every mass-1 element in N_K was already mass-1 in N_{K-1}. -/
theorem conditional_extinction (K0 : ℕ) (hK0 : K0 ≥ 12)
    (hempty : mass1_in_NK K0 = [])
    (hno_births : ∀ K, K > K0 →
      ∀ r, r ∈ computeNK K → isMassOneForm r →
        ∃ p, p ∈ computeNK (K-1) ∧ isMassOneForm p) :
    ∀ K, K ≥ K0 → mass1_in_NK K = []
```

**Proof:** By strong induction on K. Base case K = K0 is `hempty`. Inductive step: for K > K0, every mass-1 element in N_K has a mass-1 parent in N_{K-1} (by `hno_births`). By IH, N_{K-1} has no mass-1 elements, so N_K has none either.

#### 5. Birth-stops condition (`no_births_after_K7`)

```lean
/-- No new mass-1 elements are born at K > 7. All 8 births into the
    mass-1 class occur at K ≤ 7:
      K=4: 20←2, 24←6, 26←8
      K=5: 96←42, 72←18
      K=7: 486←0, 488←2, 494←8

    For K > 7, every mass-1 element in N_K was already mass-1 in N_{K-1}.
    This is a property of the Saye recursion structure. -/
theorem no_births_after_K7 : ∀ K, K > 7 →
    ∀ r, r ∈ computeNK K → isMassOneForm r →
      ∃ p, p ∈ computeNK (K-1) ∧ isMassOneForm p
```

**Proof strategy:** This requires showing that for K > 7, if r = Q Al32 j + ℓ is in N_K, then the parent of r in the Saye recursion (r' = r - i·u_{K-1} for some i ∈ {0,1,2}) is also of mass-1 form. The key facts are:
- For j ≥ 5, Q Al32 j ≥ 19 (since q_5 = 19)
- The Saye recursion shifts by multiples of u_{K-1} = 2·3^{K-2}
- For K > 7, u_{K-1} ≥ 2·3^6 = 1458, which is much larger than the gap Q A (j+1) - Q A j for small j
- Therefore the parent of a mass-1 element cannot "jump" to a different mass-1 form

This is the hardest theorem in Phase A and may require a dedicated lemma about Saye recursion and mass-1 forms.

### Composition theorem

```lean
/-- For K ≥ 12, no non-special element of N_K has mass 1. -/
theorem no_mass1_for_large_K (K : ℕ) (hK : K ≥ 12)
    (r : ℕ) (hr : r ∈ computeNK K)
    (hSpecial : r ≠ 0 ∧ r ≠ 2 ∧ r ≠ 8) :
    ¬isMassOneForm r
```

**Proof:** From `mass1_in_NK_empty_K12` (base case), `no_births_after_K7` (birth stops), and `conditional_extinction` (population stays empty).

---

## Phase B: Displacement Interface

### Purpose

Create a clean interface for the unresolved mathematical theorem: "r ∈ N_K with Σ b_k(r) ≥ 2 implies {rα} is displaced from φ⁻¹(C₃₀)." This interface:
- States exactly what needs to be proved
- Does NOT assert mass ≥ 2 alone implies avoidance (counterexamples exist)
- Makes the displacement condition an explicit hypothesis
- Can be swapped in when the theorem is proved

### New file: `ErdosTernary/DisplacementInterface.lean`

#### Displacement condition

```lean
/-- The preimage of the Cantor set C₃₀ under the map φ: x ↦ {x · log₃ 2}.
    C₃₀ is the set of reals whose base-3 expansion has no digit 2 in the
    first 30 digits. φ⁻¹(C₃₀) is a union of intervals. -/
noncomputable def φ_inv_C30 : Set ℝ :=
  sorry -- Requires formalizing the Cantor set and the map φ

/-- The displacement condition: {r · log₃ 2} is bounded away from φ⁻¹(C₃₀)
    by some positive ε. This captures the "explicit displacement argument"
    from the continued fraction analysis. -/
def displacement_condition (r : ℕ) : Prop :=
  ∃ ε : ℝ, ε > 0 ∧
    ∀ x ∈ φ_inv_C30, |(r : ℝ) * log32 - ↑⌊(r : ℝ) * log32⌋ - x| ≥ ε
```

**Note:** `φ_inv_C30` and `log32` (as a real) need to be defined. This is part of the Phase B work.

#### Conditional bridge theorem

```lean
/-- The conditional bridge: if the displacement condition holds for r,
    then 2^r has a ternary digit 2. This is the UNPROVED link between
    Ostrowski mass and Cantor avoidance.

    The proof chain is:
      displacement_condition r
      ⟹ {r · log₃ 2} ∉ φ⁻¹(C₃₀)
      ⟹ 2^r has a ternary digit 2
      ⟹ ¬(memCantorNat (2^r))

    The first implication is the displacement argument.
    The second is the characterization of Cantor set membership
    via fractional parts. -/
theorem displacement_implies_digit2 (r : ℕ)
    (hK : ∃ K, K ≥ 12 ∧ r ∈ computeNK K)
    (hSpecial : r ≠ 0 ∧ r ≠ 2 ∧ r ≠ 8)
    (hDisp : displacement_condition r) :
    ¬(memCantorNat (2 ^ r))
```

#### Structured axiom (for when Phase B is ready)

```lean
/-- The full bridge, with displacement as explicit hypothesis.
    When displacement_condition is proved for all non-special N_K elements
    (K ≥ 12), this axiom is eliminated by providing the displacement proof. -/
axiom ostrowski_invariant_structured :
  ∀ K, K ≥ 12 →
  ∀ r, r ∈ computeNK K → r ≠ 0 → r ≠ 2 → r ≠ 8 →
  displacement_condition r →
  ¬(memCantorNat (2 ^ r))
```

#### Derivation of original axiom (when both phases complete)

```lean
/-- When displacement_condition is proved for all non-special N_K elements,
    derive the original ostrowski_invariant from the structured version. -/
theorem ostrowski_invariant_from_structured
    (hDisp : ∀ K, K ≥ 12 → ∀ r, r ∈ computeNK K → r ≠ 0 → r ≠ 2 → r ≠ 8 →
      displacement_condition r) :
    ∀ K, K ≥ 12 →
    ∀ r, r ∈ computeNK K → r ≠ 0 → r ≠ 2 → r ≠ 8 →
    ¬(memCantorNat (2 ^ r)) :=
  fun K hK r hr hn0 hn2 hn8 hCant =>
    ostrowski_invariant_structured K hK r hr hn0 hn2 hn8
      (hDisp K hK r hr hn0 hn2 hn8) hCant
```

---

## Dependency Graph

```
OstrowskiFormLemma.lean (Lemma A, mass_one_iff, coef_unique_of_form, form_unique)
    │
    ├── Mass1Dynamics.lean (Phase A)
    │   ├── isMassOneForm, mass1_in_NK definitions
    │   ├── mass1_form_eq (connects mass_one_iff to isMassOneForm)
    │   ├── mass1_in_NK_empty_K12 (native_decide)
    │   ├── mass1_in_NK_empty_K13..K16 (native_decide)
    │   ├── no_births_after_K7 (Saye recursion argument)
    │   ├── conditional_extinction (induction)
    │   └── no_mass1_for_large_K (composition)
    │
    └── DisplacementInterface.lean (Phase B, interface only)
        ├── φ_inv_C30 definition (placeholder)
        ├── displacement_condition definition
        ├── displacement_implies_digit2 (statement, proof sorry)
        └── ostrowski_invariant_structured (axiom with displacement hypothesis)
```

---

## What Does NOT Change

- The existing `ostrowski_invariant` axiom stays until Phase B displacement is proved
- `BridgeUniform.lean`, `BridgeOstrowski.lean`, `BridgeOstrowskiInvariant.lean` remain unchanged
- The bridge theorem structure (three-way split at K=5/10/13) stays the same
- The `erdos_conjecture` axiom is untouched (separate concern)

---

## Success Criteria

### Phase A (this plan)
- [ ] `isMassOneForm` and `mass1_in_NK` defined
- [ ] `mass1_form_eq` proved (connects `mass_one_iff` to `isMassOneForm`)
- [ ] `mass1_in_NK_empty_K12` proved via `native_decide`
- [ ] `mass1_in_NK_empty_K13..K16` proved via `native_decide`
- [ ] `no_births_after_K7` stated (proof may require dedicated Saye lemma)
- [ ] `conditional_extinction` proved by induction
- [ ] `no_mass1_for_large_K` composed from above
- [ ] Full project builds clean (0 errors, 0 sorry in Phase A files)

### Phase B (interface only)
- [ ] `φ_inv_C30` and `displacement_condition` defined
- [ ] `displacement_implies_digit2` stated with sorry
- [ ] `ostrowski_invariant_structured` axiom declared
- [ ] Derivation theorem stated
- [ ] Full project builds clean (sorry only in displacement proof)

---

## Risk Assessment

| Risk | Mitigation |
|------|------------|
| `native_decide` timeout for K=16 (32768 elements) | Use computational certificate from Python |
| `no_births_after_K7` hard to prove from Saye recursion | May need to state as axiom initially, then prove later |
| `φ_inv_C30` definition complex (Cantor set preimage) | Start with placeholder, fill in when displacement theory is developed |
| Phase B displacement argument is substantial new math | Explicitly scoped as open problem, not blocking Phase A |
