/-
  Bridge Theorem: K=18 Chunked Bridge Verification
  Proved by: checkBridgeCantorPow2_of_chunked 18 1594323 162
  Split into 3 parts (54 chunks each) to avoid stack overflow.
-/

import Mathlib.Tactic
import ErdosTernary.BridgeCantorChunked
import ErdosTernary.BridgeK18Part1
import ErdosTernary.BridgeK18Part2
import ErdosTernary.BridgeK18Part3

open ErdosTernary.BridgeCantorChunked

namespace ErdosTernary.BridgeCantorChunkedProofs

private theorem all_chunks_18 :
    (∀ j < 54, rangeCheck 18 (j * 1594323) 1594323 = true) →
    (∀ j < 54, rangeCheck 18 ((54 + j) * 1594323) 1594323 = true) →
    (∀ j < 54, rangeCheck 18 ((108 + j) * 1594323) 1594323 = true) →
    ∀ j < 162, rangeCheck 18 (j * 1594323) 1594323 = true := by
  intro h1 h2 h3 j hj
  have h162 : j < 54 ∨ (54 ≤ j ∧ j < 108) ∨ (108 ≤ j ∧ j < 162) := by omega
  rcases h162 with (h162 | ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩)
  · exact h1 j h162
  · have := h2 (j - 54) (by omega)
      simp [show (54 + (j - 54)) * 1594323 = j * 1594323 from by omega] at this
      exact this
  · have := h3 (j - 108) (by omega)
      simp [show (108 + (j - 108)) * 1594323 = j * 1594323 from by omega] at this
      exact this

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 1000000 in
theorem checkBridgeCantorPow2_K18 :
    checkBridgeCantorPow2 18 = true := by
  apply checkBridgeCantorPow2_of_chunked 18 1594323 162
  · exact (by norm_num : 0 < 1594323)
  · native_decide
  · exact all_chunks_18 BridgeK18Part1.batch1 BridgeK18Part2.batch2 BridgeK18Part3.batch3

end ErdosTernary.BridgeCantorChunkedProofs
