/-
  Lagarias's Hausdorff-Dimension Results on Ternary Expansions of Powers of 2.

  Definitions and theorem/conjecture statements from
  J. C. Lagarias, "Ternary expansions of powers of 2",
  J. London Math. Soc. 79 (2009) 562-588.

  This file defines the 3-adic and real exceptional sets and states the
  Hausdorff-dimension results.  It does NOT prove the dimension theorems;
  the OPEN conjectures are explicitly labeled as such.

  Reference numbering (published version):
    Thm 1.3  : dimH E^T(R^+) = log_3 2          (truncated real exceptional set)
    Thm 1.6  : dimH bounds for E^(k)(Z_3), k = 1, 2, 3
    Conj 1.4 : dimH E(R^+) = 0                  (real untruncated; OPEN)
    Conj 1.7 : dimH E(Z_3) = 0                  (3-adic; OPEN)
-/

import ErdosTernary.Narkiewicz
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Topology.Instances.CantorSet
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

open scoped ENNReal NNReal

namespace LagariasHausdorff

/-! ## 3-adic Cantor set and exceptional sets -/

/-- Membership in the 3-adic Cantor set Σ_{3,2} ⊆ ℤ_[3]: every prefix of the
  3-adic expansion omits the digit 2, i.e. for every n the residue of `lam`
  modulo `3^n` equals some `r < 3^n` whose ternary digits are all 0 or 1
  (`Narkiewicz.memCantorNat r`) and whose 3-adic distance from `lam` is at
  most `3^(-n)`.  (Lagarias §1.4, eq. (1.15).) -/
def memSigma₃₂ (lam : ℤ_[3]) : Prop :=
  ∀ n : ℕ, ∃ r : ℕ, r < 3 ^ n ∧ Narkiewicz.memCantorNat r ∧
    ‖lam - (r : ℤ_[3])‖ ≤ (3 : ℝ) ^ (- (n : ℤ))

/-- E^(k)(ℤ₃): at least `k` distinct `m` with `lam·2^m ∈ Σ_{3,2}`.  (Lagarias
  eq. (1.11).) -/
def memEk (k : ℕ) (lam : ℤ_[3]) : Prop :=
  ∃ s : Finset ℕ, s.card = k ∧ ∀ m ∈ s, memSigma₃₂ (lam * (2 : ℤ_[3]) ^ m)

/-- E(ℤ₃) = E*(ℤ₃): infinitely many `m` with `lam·2^m ∈ Σ_{3,2}`.  (Lagarias
  eq. (1.10); the design spec's `E*` coincides with `E`, since "the set of m is
  infinite" is identical to "infinitely many m".) -/
def memE (lam : ℤ_[3]) : Prop :=
  Set.Infinite { m : ℕ | memSigma₃₂ (lam * (2 : ℤ_[3]) ^ m) }

/-- Hausdorff dimension on `ℤ_[3]`.  (mathlib's `dimH` takes its metric space
  directly and self-borelizes.) -/
noncomputable def dimH₃ (s : Set (ℤ_[3])) : ℝ≥0∞ := dimH s

/-- log₃2 = log 2 / log 3, as an extended nonnegative real. -/
noncomputable def log3two : ℝ≥0∞ := ENNReal.ofReal (Real.log 2 / Real.log 3)

/-- E^(k)(ℤ₃) as a set, as a family over k. -/
noncomputable def Ek (k : ℕ) : Set (ℤ_[3]) := { lam : ℤ_[3] | memEk k lam }

/-- E(ℤ₃) as a set. -/
noncomputable def EZ3 : Set (ℤ_[3]) := { lam : ℤ_[3] | memE lam }

/-! ## Real truncated and untruncated exceptional sets -/

/-- A real `x` omits the digit 2 in its (full) ternary expansion iff its
  integer part has ternary digits all in {0,1} (`Narkiewicz.memCantorNat`) and
  its fractional part has ternary digits all in {0,1}, which holds iff twice
  the fractional part lies in the middle-thirds Cantor set `cantorSet` (whose
  ternary digits are {0,2}; doubling maps digit-{0,1} numbers to digit-{0,2}
  numbers with no carries). -/
def RealOmitsTwo (x : ℝ) : Prop :=
  Narkiewicz.memCantorNat (Nat.floor x) ∧ 2 * (x - (Nat.floor x : ℝ)) ∈ cantorSet

/-- E^T(R⁺): infinitely many `⌊lam·2^n⌋` omit the digit 2.  (Lagarias
  eq. (1.7).) -/
def memETrunc (lam : ℝ) : Prop :=
  Set.Infinite { n : ℕ | Narkiewicz.memCantorNat (Nat.floor (lam * 2 ^ n)) }

/-- E^T(R⁺) as a set. -/
noncomputable def ETrunc : Set ℝ := { lam : ℝ | 0 < lam ∧ memETrunc lam }

/-- E(R⁺): infinitely many full ternary expansions `(lam·2^n)` omit the digit
  2.  (Lagarias eq. (1.8).) -/
def memEReal (lam : ℝ) : Prop :=
  Set.Infinite { n : ℕ | RealOmitsTwo (lam * 2 ^ n) }

/-- E(R⁺) as a set. -/
noncomputable def EReal : Set ℝ := { lam : ℝ | 0 < lam ∧ memEReal lam }

/-! ## Theorem and conjecture statements (never axioms) -/

/-- Theorem 1.3 (proved in Lagarias): the truncated real exceptional set has
  Hausdorff dimension log₃2. -/
noncomputable def thm_1_3 : Prop := dimH ETrunc = log3two

/-- Theorem 1.6(i) (proved in Lagarias): dimH E^(1)(ℤ₃) = log₃2. -/
noncomputable def thm_1_6_i : Prop := dimH₃ (Ek 1) = log3two

/-- Theorem 1.6(ii) (proved in Lagarias): ½·log₃2 ≤ dimH E^(2)(ℤ₃) ≤ ½. -/
noncomputable def thm_1_6_ii : Prop :=
  ENNReal.ofReal ((1 : ℝ) / 2 * Real.log 2 / Real.log 3) ≤ dimH₃ (Ek 2) ∧
    dimH₃ (Ek 2) ≤ ENNReal.ofReal ((1 : ℝ) / 2)

/-- Theorem 1.6(iii) (proved in Lagarias): ⅙·log₃2 ≤ dimH E^(3)(ℤ₃) ≤
  dimH E^(2)(ℤ₃). -/
noncomputable def thm_1_6_iii : Prop :=
  ENNReal.ofReal ((1 : ℝ) / 6 * Real.log 2 / Real.log 3) ≤ dimH₃ (Ek 3) ∧
    dimH₃ (Ek 3) ≤ dimH₃ (Ek 2)

/-- Conjecture 1.4 (Lagarias Conjecture A): the real untruncated exceptional
  set has Hausdorff dimension zero.  **OPEN** — not proved. -/
noncomputable def conj_1_4 : Prop := dimH EReal = 0

/-- Conjecture 1.7 (Lagarias Conjecture B): the 3-adic exceptional set has
  Hausdorff dimension zero.  **OPEN** — not proved. -/
noncomputable def conj_1_7 : Prop := dimH₃ EZ3 = 0

/-! ## Trivial proved lemmas -/

/-- E^(k+1) ⊆ E^(k): dropping any one of the k+1 witnessing powers of 2 leaves
  k witnesses. -/
theorem memEk_mono {k lam} (h : memEk (k + 1) lam) : memEk k lam := by
  rcases h with ⟨s, hcard, hmem⟩
  have hne : s.Nonempty := by
    exact Finset.card_pos.mp (by omega)
  let e := s.min' hne
  refine ⟨s.erase e, ?_, ?_⟩
  · simp [hcard, Finset.card_erase_of_mem (Finset.min'_mem s hne)]
  · intro m hm
    exact hmem m (Finset.mem_of_mem_erase hm)

/-- E^(k+1)(ℤ₃) ⊆ E^(k)(ℤ₃) as set inclusion. -/
theorem E_mono {k : ℕ} : Ek (k + 1) ⊆ Ek k := by
  intro lam hlam
  exact memEk_mono hlam

end LagariasHausdorff
