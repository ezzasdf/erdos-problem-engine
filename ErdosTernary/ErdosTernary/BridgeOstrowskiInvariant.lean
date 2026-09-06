/-
  Bridge Theorem: Uniform Proof for All K ≥ 5 (Re-export)

  This file re-exports the bridge theorem from BridgeUniform.lean,
  which uses the Ostrowski invariant axiom instead of erdos_conjecture.

  The erdos_conjecture axiom is kept as an isolated placeholder for the
  full conjecture (n > 8 ⟹ 2^n has digit 2). It is NOT used in this bridge proof.
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

/-- The full bridge theorem for all K ≥ 5.
    Combines:
    - K=5..9: BridgeCompute.lean (native_decide)
    - K=10..12: BridgeMiddle.lean (native_decide on mod 3^50)
    - K≥13: Ostrowski invariant (axiom, verified computationally for K=13..15)

    Note: erdos_conjecture axiom is NOT used in this proof. -/
theorem bridge_first_period_all_ostrowski :
    ∀ K, K ≥ 5 →
    ∀ r, r ∈ computeNK K → r ≠ 0 → r ≠ 2 → r ≠ 8 →
    ¬(memCantorNat (2 ^ r)) :=
  fun K hK r hr hn0 hn2 hn8 =>
    bridge_first_period_all K hK r (by rwa [computeNKFast_eq]) ⟨hn0, hn2, hn8⟩

end ErdosTernary.BridgeOstrowskiInvariant
