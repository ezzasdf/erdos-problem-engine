/-
  ErdosFinalGlue.lean — Final glue: full digit-form conjecture

  Imports ErdosSurvivorFinal (compiled, 0 sorry) and LargeBridge (1 sorry).
  The single sorry in this file IS the one sorry in LargeBridge.
-/

import ErdosTernary.ErdosSurvivorFinal
import ErdosTernary.LargeBridge

open ErdosTernary.BridgeCompute
open Narkiewicz

private lemma uK13_gt_8 : uK 13 > 8 := by unfold uK; norm_num
private lemma uK13_gt_2 : uK 13 > 2 := by unfold uK; norm_num

/-- The Erdős Digit-Form Conjecture (Full).
    If 2^r is Cantor (no digit 2 in ternary), then r ∈ {0, 2, 8}.

    Proof: splits on r < uK 13 (finite bridge) vs r ≥ uK 13 (large bridge).
    The large bridge uses the eventuality lemma + pow2_not_cantor_for_large_K.
    The single sorry comes from LargeBridge.lean. -/
theorem erdos_cantor_classification (r : Nat)
    (hc : memCantorNat (2 ^ r)) :
    r = 0 ∨ r = 2 ∨ r = 8 := by
  by_cases hr_small : r < uK 13
  · exact erdos_digit2_conjecture_small r hr_small hc
  · push_neg at hr_small
    have hne0 : r ≠ 0 := by have := uK13_gt_8; omega
    have hne2 : r ≠ 2 := by have := uK13_gt_2; omega
    have hne8 : r ≠ 8 := by have := uK13_gt_8; omega
    obtain ⟨K₀, h_eventual⟩ := memCantorNat_2pow_eventual r hc
    let K := max (K₀ + 1) 18
    have hKgt : K > K₀ := Nat.lt_of_lt_of_le (by omega) (le_max_left _ _)
    have hK18 : K ≥ 18 := le_max_right _ _
    have hmem : r ∈ computeNK K := h_eventual K hKgt
    have hmem_f : r ∈ computeNKFast K := by rw [computeNKFast_eq]; exact hmem
    have hbridge : ¬ memCantorNat (2 ^ r) :=
      pow2_not_cantor_for_large_K K hK18 r hmem_f ⟨hne0, hne2, hne8⟩
    exact absurd hc hbridge
