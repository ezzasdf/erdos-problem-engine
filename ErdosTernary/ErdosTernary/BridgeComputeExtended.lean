/-
  Bridge Theorem: Extended Computational Verification

  Proves the first-period bridge theorem for n=48..1000.
  For each n, verifies that 2^n has digit 2 in first 30 ternary digits.

  This extends the precomputed range from N=47 to N=1000,
  pushing the axiom split in BridgeUniform.lean from r=48 to r=1001.
-/

import Mathlib.Tactic
import ErdosTernary.BridgeCompute

open ErdosTernary.BridgeCompute

namespace ErdosTernary.BridgeComputeExtended

/-- Batch verification: all n in [48, 1000] have digit 2 in first 30 digits. -/
theorem check_leading_48_to_1000 :
    List.all ((List.range 1001).filter (· ≥ 48))
      (fun n => hasLeadingDigit2 (2 ^ n) 30) = true := by
  native_decide

end ErdosTernary.BridgeComputeExtended
