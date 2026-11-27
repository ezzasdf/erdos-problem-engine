/-
Copyright (c) 2026 Ezzeldin Ashraf Mohamed Shafey Wahba. All rights reserved.
Released under the PolyForm Strict License 1.0.0 as described in the file LICENSE-CODE.
Authors: Ezzeldin Ashraf Mohamed Shafey Wahba
-/

import ErdosTernary.CriticalInvariant

private theorem test_single_residue :
    ∀ k ∈ Finset.range 59049, 0 + 162 * k ≥ 69 →
      ∃ j ∈ Finset.range 38, digitMod (0 + 162 * k) (j + 5) = 2 := by
  native_decide
