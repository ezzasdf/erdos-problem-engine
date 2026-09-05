/-
  Displacement Interface: Phase B interface for the Ostrowski→Cantor bridge.

  Defines the leading-digit forbidden set C30Lead and displacement as exclusion
  from that set. The N_K structure is level-indexed: displacement_condition takes
  K as an explicit parameter and uses α = log₃(2) specifically (not quantified
  over all irrational α).

  C30Lead = {x ∈ [0,1) : ⌊3^{x+29}⌋ has no digit 2 in base 3}

  The key bridge (representation theory, Piece A):
    memCantorNat(2^r) ⟹ {r·α} ∈ C30Lead
    (contrapositive: {rα} ∉ C30Lead ⟹ ¬memCantorNat(2^r))

  The remaining open problem (number theory, Piece B):
    r ∈ N_K \ {0,2,8} ⟹ {r·α} ∉ C30Lead
    (this is the hard Diophantine displacement argument)
-/

import Mathlib.Tactic
import Mathlib.Data.Real.Irrational
import ErdosTernary.Narkiewicz
import ErdosTernary.BridgeCompute
import ErdosTernary.LeadingDigits

open Narkiewicz
open ErdosTernary.BridgeCompute
open ErdosTernary.LeadingDigits

namespace ErdosTernary.DisplacementInterface

/-! ## Forbidden Set C₃₀ (Trailing-Digit) as Finite Union of Ternary Cylinders -/

/-- A natural number a has valid Cantor digits in the first n positions
    (i.e., no digit equals 2). This mirrors `memCantorNat` but bounded to n digits. -/
def validCantorDigits (a n : ℕ) : Prop :=
  ∀ k ∈ Finset.range n, digit₃ a k ≠ 2

@[simp] theorem validCantorDigits_zero : validCantorDigits a 0 :=
  fun k hk => absurd hk (by simp [Finset.range])

/-- The forbidden set C₃₀: union of all ternary cylinders [a/3³⁰, (a+1)/3³⁰)
    where a has no digit 2 in its first 30 ternary positions.

    This is a finite set of at most 2³⁰ intervals, each of width 1/3³⁰. -/
noncomputable def C30 : Set ℝ :=
  ⋃ (a : ℕ) (_ : a < 3 ^ 30 ∧ validCantorDigits a 30),
    Set.Ico (a / (3 ^ 30 : ℝ)) ((a + 1) / (3 ^ 30 : ℝ))

/-! ## Displacement Condition (Level-Indexed, using α = log₃(2)) -/

/-- The displacement condition at level K for element r ∈ N_K:
    the fractional part {r · log₃(2)} lies outside C30Lead.

    This uses α = log₃(2) SPECIFICALLY, not quantified over all irrational α.
    K is an explicit parameter, not existentially quantified.

    The theorem has the honest shape:
        ∀ K ≥ 12, ∀ r ∈ N_K \ {0,2,8}, displacement_condition K r

    Status: OPEN PROBLEM. Not asserted as an axiom until proved. -/
def displacement_condition (_K r : ℕ) : Prop :=
  ¬LeadingDigits.C30Lead (Int.fract ((r : ℝ) * LeadingDigits.α))

/-- The conditional bridge: if the displacement condition holds for r at level K,
    then 2^r has a ternary digit 2.

    Proof chain (Piece A = representation theory, COMPLETE modulo digit correspondence):
      displacement_condition K r
      ⟹ {r · log₃(2)} ∉ C30Lead
      ⟹ 2^r has a ternary digit 2   [by not_mem_C30Lead_not_cantor from LeadingDigits.lean]
      ⟹ ¬(memCantorNat (2 ^ r))

    Status: PROOF COMPLETE (modulo digit correspondence sorry in LeadingDigits.lean). -/
theorem displacement_implies_digit2 (K r : ℕ)
    (hK : K ≥ 12) (hr : r ∈ computeNK K)
    (hSpecial : r ≠ 0 ∧ r ≠ 2 ∧ r ≠ 8)
    (hDisp : displacement_condition K r) :
    ¬(memCantorNat (2 ^ r)) :=
  LeadingDigits.not_mem_C30Lead_not_cantor r hDisp

/-- The full bridge, with displacement as explicit hypothesis.
    When displacement_condition K r is proved for all non-special N_K elements
    (K ≥ 12), this is eliminated by providing the displacement proof.

    Status: PROVED via displacement_implies_digit2. -/
theorem ostrowski_invariant_structured :
  ∀ K, K ≥ 12 →
  ∀ r, r ∈ computeNK K → r ≠ 0 → r ≠ 2 → r ≠ 8 →
  displacement_condition K r →
  ¬(memCantorNat (2 ^ r)) :=
  fun K hK r hr hn0 hn2 hn8 hDisp =>
    displacement_implies_digit2 K r hK hr ⟨hn0, hn2, hn8⟩ hDisp

/-- Derivation of the original ostrowski_invariant from the structured version.

    Status: COMPLETE (no sorry). This is a pure logical derivation. -/
theorem ostrowski_invariant_from_structured
    (hDisp : ∀ K, K ≥ 12 → ∀ r, r ∈ computeNK K → r ≠ 0 → r ≠ 2 → r ≠ 8 →
      displacement_condition K r) :
    ∀ K, K ≥ 12 →
    ∀ r, r ∈ computeNK K → r ≠ 0 → r ≠ 2 → r ≠ 8 →
    ¬(memCantorNat (2 ^ r)) :=
  fun K hK r hr hn0 hn2 hn8 =>
    ostrowski_invariant_structured K hK r hr hn0 hn2 hn8
      (hDisp K hK r hr hn0 hn2 hn8)

end ErdosTernary.DisplacementInterface
