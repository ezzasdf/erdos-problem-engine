/-
  Bridge Theorem: Verification for K ∈ [5, 18] and Uniform Extension (Re-export)

  This file re-exports the bridge theorem from BridgeUniform.lean:
  1. `bridge_first_period_verified_ostrowski`: Unconditionally verified for all
     5 ≤ K ≤ 18 via computational certificates (native_decide).
  2. `bridge_first_period_all_ostrowski`: Full bridge theorem for all K ≥ 5,
     relying on verified computations for K ≤ 18 and the explicit `ostrowski_invariant`
     axiom for the open asymptotic range K > 18.
-/

import Mathlib.Tactic
import ErdosTernary.BridgeUniform

open ErdosTernary.BridgeUniform
open ErdosTernary.BridgeCompute
open ErdosTernary.BridgeMiddle
open Narkiewicz

namespace ErdosTernary.BridgeOstrowskiInvariant

/-- ComputeNK equals NK_K_for for K=10..12 (by construction). -/
theorem computeNK_eq_NK_K_for (K : Nat) (hK : K = 10 ∨ K = 11 ∨ K = 12) :
    computeNK K = NK_K_for K := by
  rcases hK with rfl | rfl | rfl
  · native_decide
  · native_decide
  · native_decide

/-- The finite bridge theorem computationally verified for all 5 ≤ K ≤ 18.
    Combines:
    - K=5..9: BridgeCompute.lean (native_decide)
    - K=10..12: BridgeMiddle.lean (native_decide on middle window mod 3^50)
    - K=13..18: BridgeK13-K18, BridgeCandidates, BridgeCantorChunkedProofs (native_decide on low 50 mod 3^50)
    Uses zero unproved axioms (purely kernel + native_decide certificates). -/
theorem bridge_first_period_verified_ostrowski :
    ∀ K, 5 ≤ K → K ≤ 18 →
    ∀ r, r ∈ computeNK K → r ≠ 0 → r ≠ 2 → r ≠ 8 →
    ¬(memCantorNat (2 ^ r)) :=
  fun K hK5 hK18 r hr hn0 hn2 hn8 =>
    bridge_first_period_verified K hK5 hK18 r (by rwa [computeNKFast_eq]) ⟨hn0, hn2, hn8⟩

/-- The finite First-Period Bridge Theorem (Exact Set Equivalence / Iff Formulation):
    For each 5 ≤ K ≤ 18, a power 2^r in the first period r ∈ computeNK K
    belongs to the Cantor set if and only if r ∈ {0, 2, 8}. -/
theorem bridge_first_period_iff_ostrowski :
    ∀ K, 5 ≤ K → K ≤ 18 →
    ∀ r, r ∈ computeNK K →
    (memCantorNat (2 ^ r) ↔ (r = 0 ∨ r = 2 ∨ r = 8)) :=
  fun K hK5 hK18 r hr =>
    bridge_first_period_iff K hK5 hK18 r (by rwa [computeNKFast_eq])

/-- The conditional full bridge theorem for all K ≥ 5.
    Combines verified computations for K ≤ 18 with the explicit
    `ostrowski_invariant` axiom for K > 18. -/
theorem bridge_first_period_all_ostrowski :
    ∀ K, K ≥ 5 →
    ∀ r, r ∈ computeNK K → r ≠ 0 → r ≠ 2 → r ≠ 8 →
    ¬(memCantorNat (2 ^ r)) :=
  fun K hK r hr hn0 hn2 hn8 =>
    bridge_first_period_all K hK r (by rwa [computeNKFast_eq]) ⟨hn0, hn2, hn8⟩

end ErdosTernary.BridgeOstrowskiInvariant
