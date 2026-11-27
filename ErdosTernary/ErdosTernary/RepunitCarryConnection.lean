/-
Copyright (c) 2026 Ezzeldin Ashraf Mohamed Shafey Wahba. All rights reserved.
Released under the PolyForm Strict License 1.0.0 as described in the file LICENSE-CODE.
Authors: Ezzeldin Ashraf Mohamed Shafey Wahba
-/

import Mathlib
import ErdosTernary.CantorMultiplier
import ErdosTernary.RepunitCarryPacket

/-!
# Structural Connection Lemma: Carry Automata and Safe-Multiplier SFTs

This module formalizes spectral and recurrence identities for the two-state
transfer system $A = \begin{pmatrix} 1 & 1 \\ 1 & 0 \end{pmatrix}$ and connects
them to the subshift of finite type (SFT) for the safe multiplier $M = 4$
($a=1, b=2$ in Family 2).

The interpretation of this transfer recurrence as the population growth of
valid paths in the discrete carry automaton (`RepunitCarryPacket.lean`) is an
analytical comparison presented in the manuscript, rather than a formally
proved path-count theorem.

## Key Results
1. `phi_eq`: The algebraic golden ratio definitions in `CantorMultiplier` and
   `RepunitCarryPacket` coincide identically.
2. `carry_charpoly_eq_perronPoly`: The characteristic polynomial of the transfer
   matrix $A = \begin{pmatrix} 1 & 1 \\ 1 & 0 \end{pmatrix}$ equals the Perron
   polynomial of $M = 4$ (`perronPoly 2 t`) for all $t \in \mathbb{R}$.
3. `lambda_SFT_one_two_eq_carry_phi`: The Perron-Frobenius eigenvalue $\lambda_{\mathrm{SFT}}(1, 2)$
   identically equals the transfer spectral radius $\phi = (1 + \sqrt{5})/2$.
4. `orbitCount_sum_eq_goldenWordCount`: The population size of the transfer recurrence
   at step $n$ matches the SFT word count $\mathrm{fib}(n+2)$ identically for all $n$.
-/

namespace ErdosTernary.RepunitCarryConnection

open ErdosTernary.CantorMultiplier
open ErdosTernary.RepunitCarryPacket

/-- The golden ratio definitions in CantorMultiplier and RepunitCarryPacket agree identically. -/
theorem phi_eq : CantorMultiplier.phi = RepunitCarryPacket.phi := by
  rfl

/-- The exact equality of the characteristic polynomial:
    The determinant of the carry automaton charMatrix equals the Perron polynomial
    of the safe multiplier M = 4 (b = 2) for all t ∈ ℝ. -/
theorem carry_charpoly_eq_perronPoly (t : ℝ) :
    (charMatrix t).det = perronPoly 2 t := by
  rw [charMatrix_det]
  dsimp [perronPoly]
  ring

/-- The single-column Perron root of the safe multiplier M = 4 ((a, b) = (1, 2))
    in CantorMultiplier identically equals the golden ratio φ in RepunitCarryPacket. -/
theorem lambda_SFT_one_two_eq_carry_phi :
    lambda_SFT 1 2 = RepunitCarryPacket.phi := by
  dsimp [lambda_SFT]
  exact phi_eq

/-- Two-state transfer action on population vectors:
    v_{n+1} = A v_n corresponds to [x, y] ↦ [x + y, x]. -/
def transferAction (v : ℕ × ℕ) : ℕ × ℕ :=
  (v.1 + v.2, v.1)

def orbitCount : ℕ → ℕ × ℕ
  | 0 => (1, 0)
  | n + 1 => transferAction (orbitCount n)

/-- The orbit component-wise: (orbitCount n) = (fib (n + 1), fib n). -/
theorem orbitCount_eq_fib_pair (n : ℕ) :
    orbitCount n = (Nat.fib (n + 1), Nat.fib n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp [orbitCount, transferAction]
    rw [ih]
    dsimp
    rw [Nat.fib_add_two]
    rw [add_comm (Nat.fib (n + 1)) (Nat.fib n)]

/-- The total population of the two-state transfer recurrence at step n
    equals the Fibonacci number fib(n + 2) (matching the analytical golden shift word count). -/
theorem orbitCount_sum_eq_fib (n : ℕ) :
    (orbitCount n).1 + (orbitCount n).2 = Nat.fib (n + 2) := by
  rw [orbitCount_eq_fib_pair]
  dsimp
  rw [Nat.fib_add_two]
  rw [add_comm]

/-- Word count recurrence for the Golden Mean shift (forbidden block 11):
    N(0) = 1, N(1) = 2, N(n+2) = N(n+1) + N(n). -/
def goldenWordCount : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | n + 2 => goldenWordCount (n + 1) + goldenWordCount n

/-- The word count in the golden shift is identically the shifted Fibonacci number:
    N(n) = fib(n + 2). -/
theorem goldenWordCount_eq_fib (n : ℕ) :
    goldenWordCount n = Nat.fib (n + 2) := by
  induction' n using Nat.strong_induction_on with n ih
  rcases n with _ | _ | n
  · rfl
  · rfl
  · have ih1 := ih (n + 1) (by omega)
    have ih0 := ih n (by omega)
    dsimp [goldenWordCount]
    rw [ih1, ih0]
    have heq1 : n + 1 + 2 = n + 2 + 1 := by omega
    have heq2 : n + 2 + 2 = (n + 2) + 2 := by omega
    rw [heq1, heq2]
    rw [add_comm]
    exact (Nat.fib_add_two).symm

/-- The carry automaton path population matches the SFT word count identically. -/
theorem orbitCount_sum_eq_goldenWordCount (n : ℕ) :
    (orbitCount n).1 + (orbitCount n).2 = goldenWordCount n := by
  rw [orbitCount_sum_eq_fib, goldenWordCount_eq_fib]

end ErdosTernary.RepunitCarryConnection
