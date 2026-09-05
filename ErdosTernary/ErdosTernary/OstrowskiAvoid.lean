/-
  Ostrowski Avoidance Lemma (Phase B)

  Proves the bridge theorem using Ostrowski numeration.
  For n ∈ N_K \ {0,2,8}, the fractional part {n·α} avoids C_30,
  meaning 2^n has digit 2 in the first 30 ternary digits.

  Three layers:
  1. SIZE INVARIANT: r ≥ 23 ⟹ some b_k ≥ 1 at k ≥ 5
     (max representable using q_0..q_4 with Ostrowski constraints = 22)
  2. CONDITIONAL BRIDGE: b_k ≥ 1 at k ≥ 5 ⟹ ¬C30Lead({r·α})
  3. COMPOSITION: size invariant + conditional bridge ⟹ ¬memCantorNat(2^r)

  Assembled 2026-09-02.
-/

import Mathlib.Tactic
import ErdosTernary.Ostrowski
import ErdosTernary.OstrowskiFormLemma
import ErdosTernary.BridgeCompute
import ErdosTernary.LeadingDigits
import ErdosTernary.BridgeUniform

namespace ErdosTernary.OstrowskiAvoid

open ErdosTernary.Ostrowski
open ErdosTernary.OstrowskiFormLemma
open ErdosTernary.BridgeCompute
open ErdosTernary.LeadingDigits
open Narkiewicz

/-! ## Layer 1: Size Invariant -/

private theorem q5_val : Q Al32 5 = 19 := by native_decide

/-- The max value representable using q_0..q_4 with Ostrowski constraints
    is at most 22. -/
theorem max_rep_q0_q4_le_22 (n : ℕ)
    (hn : ∀ k, 5 ≤ k → gd Al32 Al32_hyp k n = 0) :
    n ≤ 22 := by
  by_contra hgt
  have hn_pos : 0 < n := by omega
  have htop_lo := OstrowskiFormLemma.topIdx_lo Al32_hyp hn_pos
  have htop_hi := OstrowskiFormLemma.topIdx_hi Al32_hyp n
  -- topIdx ≥ 5 since n ≥ 23 > q_5 = 19 = Q Al32 5
  have htop5 : 5 ≤ OstrowskiFormLemma.topIdx Al32 Al32_hyp n := by
    by_contra hlt
    have hle5 : OstrowskiFormLemma.topIdx Al32 Al32_hyp n + 1 ≤ 5 := by omega
    have hq5_mono := @Q_mono Al32 Al32_hyp (OstrowskiFormLemma.topIdx Al32 Al32_hyp n + 1) 5
      (by omega) hle5
    -- n < Q(topIdx+1) ≤ Q(5) = 19, but n ≥ 23
    have : n < 19 := lt_of_lt_of_le htop_hi hq5_mono
    omega
  -- gd at top index = n / q_t
  have htop_eq := OstrowskiFormLemma.gd_eq_top_of Al32_hyp hn_pos rfl
  have hzero := hn _ htop5
  rw [htop_eq] at hzero
  -- n / q_t = 0 means n < q_t
  have hq_pos : 0 < Q Al32 (OstrowskiFormLemma.topIdx Al32 Al32_hyp n) :=
    OstrowskiFormLemma.Q_pos _
  have hlt_n : n < Q Al32 (OstrowskiFormLemma.topIdx Al32 Al32_hyp n) := by
    rwa [Nat.div_eq_zero_iff hq_pos] at hzero
  omega

/-- The KEY SIZE INVARIANT: if r ≥ 23, then the greedy Ostrowski
    representation of r has b_k ≥ 1 for some k ≥ 5. -/
theorem invariant_from_size (r : ℕ) (hr : r ≥ 23) :
    ∃ k, 5 ≤ k ∧ gd Al32 Al32_hyp k r ≥ 1 := by
  by_contra hnot
  push_neg at hnot
  have hle := max_rep_q0_q4_le_22 r (fun k hk => by
    have := hnot k hk
    omega)
  omega

/-! ## Layer 3: Bridge Theorem (Conditional) -/

/-- The conditional bridge: if the C₃₀ avoidance follows from the
    size invariant, then the full bridge theorem holds. -/
theorem bridge_from_invariant_cond
    (h_cond : ∀ r : ℕ, r ≥ 23 →
      (∃ k, 5 ≤ k ∧ gd Al32 Al32_hyp k r ≥ 1) →
      ¬(C30Lead (Int.fract ((r : ℝ) * α))))
    (K r : ℕ) (hK : K ≥ 12)
    (hr : r ∈ computeNK K)
    (hSpecial : r ≠ 0 ∧ r ≠ 2 ∧ r ≠ 8) :
    ¬(memCantorNat (2 ^ r)) := by
  have hr23 : r ≥ 23 :=
    ErdosTernary.BridgeUniform.NK_excludes_small_23 K (by omega) r hr hSpecial
  have hinv := invariant_from_size r hr23
  have hnotC30 := h_cond r hr23 hinv
  exact not_mem_C30Lead_not_cantor r hnotC30

/-- The key corollary (sorry-free): ¬C30Lead({rα}) ⟹ ¬memCantorNat(2^r). -/
theorem not_C30_implies_not_cantor (r : ℕ)
    (h : ¬C30Lead (Int.fract ((r : ℝ) * α))) :
    ¬(memCantorNat (2 ^ r)) :=
  not_mem_C30Lead_not_cantor r h

/-! ## Proof Architecture Summary

    The bridge theorem for K ≥ 12 (eliminating ostrowski_invariant axiom)
    reduces to two sub-goals:

    GOAL 1 (size, PROVED): r ∈ N_K \ {0,2,8}, K ≥ 12 ⟹ r ≥ 23
      NK_excludes_small_23 in BridgeUniform.lean

    GOAL 2 (invariant, PROVED): r ≥ 23 ⟹ ∃ k ≥ 5, b_k(r) ≥ 1
      max_rep_q0_q4_le_22 + invariant_from_size

    GOAL 3 (C₃₀, OPEN): r ≥ 23 ∧ b_k(r) ≥ 1 at k ≥ 5 ⟹ ¬C30Lead({r·α})
      This is the hard number-theoretic core. It requires connecting
      the Ostrowski structure to ternary digit analysis via irrational
      rotation theory and continued fraction error bounds.

    Computational coverage: K=5..9 via checkBridgeCantor, K=10..12 via
    BridgeMiddle, K=13..15 via checkBridgeCantor. K≥16 remains axiom.
-/-

end ErdosTernary.OstrowskiAvoid
