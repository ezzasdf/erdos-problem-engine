import ErdosTernary.CriticalInvariant

set_option linter.unusedVariables false in
private theorem test_7pos :
    ∀ s ∈ (ErdosTernary.CriticalInvariant.N5_even_set),
    ∀ k ∈ Finset.range 59049,
      s + 162 * k ≥ 69 →
      ∃ j ∈ Finset.range 7, digitMod (s + 162 * k) (j + 5) = 2 := by
  native_decide
