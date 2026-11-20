# Archive: 3-Adic Lifting Dynamics & Carry-Machine Architecture (Phases 3–5)

## 1. Overview & Research Context
This directory preserves the complete formalization and experimental work developed during **Phases 3 through 5** of the Erdős ternary conjecture investigation.

Rather than deleting abandoned approaches, this archive preserves the structural proofs and explicitly documents the **mathematical obstructions and barrier theorems** that proved why 3-adic Hensel lifting and finite-window prefix induction cannot unconditionally resolve the conjecture.

---

## 2. The Investigated Method
The core strategy attempted to prove that $2^r$ has a digit 2 in base 3 for all $r \notin \{0, 2, 8\}$ by:
1. Decomposing any exponent as $r = s + q \cdot u_K$, where $s \in \{0, 2, 8\}$ are the three known powers of 2 and $u_K = \phi(3^K) = 2 \cdot 3^{K-1}$ is Euler's totient period.
2. Applying **strong induction on the quotient $q$** via 3-adic Hensel lifting (`LiftingDynamics.lean`).
3. Formulating a "Critical Invariant" over a finite window of ternary digits (positions 15..59) to force $q = 0$ (`CriticalInvariant.lean`).
4. Modeling addition carry propagation via finite-state carry automata (`CarryMachineTotal.lean`).
5. Analyzing 2-adic and 3-adic valuations $v_d$ for odd exponents (`OddCaseDigit2.lean`, `VdBound.lean`).

---

## 3. The Proven Mathematical Barriers & Counterexamples

This approach was retired after the research group uncovered two insurmountable mathematical obstructions (documented in `CriticalInvariant.lean` and `paper/phase3_bridge_report.md`):

### Barrier 1: Refutation of Finite-Window Digit-2 Forcing
- **Hypothesis:** It was conjectured that if digits 15..59 of $2^{P \cdot m}$ avoid digit 2, then $m$ must be 0 modulo $3^{45}$.
- **Counterexample Found:**
  $$m = 19,563,520,461,291,867 \in [3^{15}, 3^{45})$$
  Direct modular and full-precision verification showed that for this $m$, digits 15 through 59 of $2^{P \cdot m}$ are **strictly in $\{0, 1\}$** (zero occurrences of digit 2), and the very first digit 2 only appears at position 60!
- **Structural Cause:** $m \mapsto (b_0, b_1, b_2)$ is a bijection $[0, 3^{45}) \to [0, 3^{15})^3$. The digit positions 15..59 act as free affine coordinates, yielding exactly $(2^{15})^3 = 2^{45}$ "all-clean" residues in $[0, 3^{45})$. No fixed finite window of digits can ever force $m = 0$.

### Barrier 2: Theorem G8 (Full 2-Way Binary Tree Branching)
- Formalized in `CriticalInvariant.lean` Part G8:
  At every prefix depth $j$, the clean-prefix tree has **exactly two clean children per node**.
- Therefore, the set of surviving quotients branches as a full binary tree with $2^j$ survivors at level $j$.
- In `LiftingDynamics.lean` line 725, when $q \equiv 1 \pmod 3$ with $q > 1$, the state $s' = s + u_K$ permanently leaves $\{0, 2, 8\}$ ($s' \ge 486$). The strong induction hypothesis cannot fire, creating an unclosable induction loop.

---

## 4. Preserved Files in this Archive

| File | Lines | Core Mathematical Content |
|---|:---:|---|
| `LiftingDynamics.lean` | 1,012 | Hensel lifting identities, `pow2_uK_mod3K_plus2..5`, `digit_pos_of_lift` |
| `CriticalInvariant.lean` | 1,320 | Affine window coordinates, Theorem G8 (2-way branching), prefix determinism |
| `CarryMachineTotal.lean` | 297 | State transition system for base-3 carry addition |
| `OddCaseDigit2.lean` | 898 | Parity decomposition and odd-branch digit-2 analysis |
| `VdBound.lean` | 375 | Valuation bounds for odd-exponent branches |
| `ErdosFinal.lean` | 150 | Early bridge assembly from Phase 5 |
| `TestDigit.lean` | 13 | Digit verification test harness |

---

## 5. Relation to the Active Engine
These findings directly motivated the complete paradigm shift in **Phases 6–12**:
- Replacing 3-adic Hensel quotient induction with the **Saye Survivor Tree** ($N_K$).
- Replacing finite windowing with the **First-Period Bridge Theorem** (`BridgeCompute.lean`, `ErdosSurvivorFinal.lean`).
- Introducing **Ostrowski Numeration** ($\alpha = \log_3 2$) and the **Cantor Multiplier Dynamical System** (`CantorMultiplier.lean`, `TimeReversal.lean`, `PeriodicOrbit.lean`).
