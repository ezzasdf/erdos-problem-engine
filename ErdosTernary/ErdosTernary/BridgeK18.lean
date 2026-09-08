/-
  Bridge Theorem: K=18 Chunked Bridge Verification
  Proved by: checkBridgeCantorPow2_of_chunked 18 1594323 162
  Split into 3 parts (54 chunks each) to avoid stack overflow.
-/

import ErdosTernary.BridgeCantorChunked
import ErdosTernary.BridgeK18Part1
import ErdosTernary.BridgeK18Part2
import ErdosTernary.BridgeK18Part3

open ErdosTernary.BridgeCantorChunked
open ErdosTernary.BridgeCompute

namespace ErdosTernary.BridgeCantorChunkedProofs

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 1000000 in
theorem checkBridgeCantorPow2_K18 :
    checkBridgeCantorPow2 18 = true := by
  apply checkBridgeCantorPow2_of_chunked 18 1594323 162
  · exact (by norm_num : 0 < 1594323)
  · native_decide
  · intro j hj
    have : j < 54 ∨ 54 ≤ j ∧ j < 108 ∨ 108 ≤ j ∧ j < 162 := by omega
    rcases this with (h1 | ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩)
    · exact BridgeK18Part1.batch1 j h1
    · have h := BridgeK18Part2.batch2 (j - 54) (by omega)
      have heq : (54 + (j - 54)) * 1594323 = j * 1594323 := by omega
      rw [heq] at h
      exact h
    · have h := BridgeK18Part3.batch3 (j - 108) (by omega)
      have heq : (108 + (j - 108)) * 1594323 = j * 1594323 := by omega
      rw [heq] at h
      exact h

end ErdosTernary.BridgeCantorChunkedProofs
