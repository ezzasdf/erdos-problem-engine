import ErdosTernary.CriticalInvariant

private theorem test_single_residue :
    ∀ k ∈ Finset.range 59049, 0 + 162 * k ≥ 69 →
      ∃ j ∈ Finset.range 38, digitMod (0 + 162 * k) (j + 5) = 2 := by
  native_decide
