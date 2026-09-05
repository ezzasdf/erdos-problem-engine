/-
  Bridge Theorem: Computational Verification via native_decide

  Proves the first-period bridge theorem for K=5..9 by direct computation.
  For each K, we compute N_K (trailing 2-free residues) and verify that
  for all r ∈ N_K \ {0,2,8}, the first L=30 digits of 2^r contain a digit 2.

  K=10..11 are not feasible with native_decide because:
  1. hasLeadingDigit2 requires computing 2^r as a full big integer (r ~39000 → ~12000 digits)
  2. This OOMs the kernel during native_decide evaluation

  The full bridge theorem for ALL K ≥ 5 is proved in BridgeUniform.lean
  via the r < 48 / r ≥ 48 split, independent of these native_decide results.
-/

import Mathlib.Tactic
import ErdosTernary.SayeLemma
import ErdosTernary.Narkiewicz

open ErdosTernary.SayeLemma
open Narkiewicz

namespace ErdosTernary.BridgeCompute

/-- The period u_K = 2 * 3^(K-1). -/
def uK (K : Nat) : Nat :=
  2 * 3 ^ (K - 1)

/-- Auxiliary: modular exponentiation via binary method, O(log n) stack depth. -/
def pow2ModAux (n : Nat) (base m : Nat) : Nat :=
  if n == 0 then 1 % m
  else if n % 2 == 0 then
    let half := pow2ModAux (n / 2) base m
    (half * half) % m
  else
    (base * pow2ModAux (n - 1) base m) % m
termination_by n
decreasing_by
  all_goals (simp [beq_iff_eq] at *; omega)

private theorem pow2ModAux_eq (n base m : Nat) :
    pow2ModAux n base m = base ^ n % m := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    unfold pow2ModAux
    split
    · next h_eq => simp [beq_iff_eq] at h_eq; subst h_eq; simp [Nat.pow_zero]
    · next h_neq =>
      simp only [beq_iff_eq] at h_neq
      split
      · -- n even
        next h_even =>
        simp only [beq_iff_eq] at h_even
        have h_div : n / 2 < n := Nat.div_lt_self (by omega) (by norm_num)
        rw [ih (n / 2) h_div]
        rw [← Nat.mul_mod, ← Nat.pow_two, ← Nat.pow_mul]
        rw [Nat.div_mul_cancel (by omega : 2 ∣ n)]
      · -- n odd
        next h_odd =>
        simp only [beq_iff_eq] at h_odd
        have h_sub : n - 1 < n := by omega
        rw [ih (n - 1) h_sub]
        rw [Nat.mul_mod_mod, Nat.mul_comm base (base ^ (n - 1)), ← Nat.pow_succ]
        have h_eq : (n - 1).succ = n := by omega
        rw [h_eq]

/-- Efficient modular exponentiation: 2^e % m. -/
def pow2Mod (e m : Nat) : Nat :=
  pow2ModAux e 2 m

/-- pow2Mod agrees with naive 2^e % m. -/
theorem pow2Mod_eq (e m : Nat) : pow2Mod e m = 2 ^ e % m := by
  simp [pow2Mod, pow2ModAux_eq]

/-- Check if val has digit 2 in its last K ternary digits. -/
def hasTrailingDigit2 (val K : Nat) : Bool :=
  (List.range K).any fun i => (val / 3 ^ i) % 3 == 2

/-- Check if val has digit 2 in ternary positions lo..hi-1. -/
def hasDigit2InRange (val lo hi : Nat) : Bool :=
  (List.range (hi - lo)).any fun i => (val / 3 ^ (lo + i)) % 3 == 2

/-- Check if val has digit 2 in its first maxDigits ternary digits. -/
def hasDigit2UpTo (val maxDigits : Nat) : Bool :=
  hasDigit2InRange val 0 maxDigits

/-- Compute N_K: residues r ∈ [0, u_K) without digit 2 in 2^r mod 3^K. -/
def computeNK (K : Nat) : List Nat :=
  let period := uK K
  let modulus := 3 ^ K
  (List.range period).filter fun r =>
    let pow2r := 2 ^ r % modulus
    !(hasTrailingDigit2 pow2r K)

/-- Get the ternary digits of n, most significant first. -/
def toTernaryDigitsAux : Nat → List Nat → List Nat
  | 0, acc => acc
  | v + 1, acc => toTernaryDigitsAux ((v + 1) / 3) (((v + 1) % 3) :: acc)
termination_by v => v

/-- Get the ternary digits of n, most significant first. -/
def toTernaryDigits (n : Nat) : List Nat :=
  if n == 0 then [0]
  else toTernaryDigitsAux n []

/-- Check if val has digit 2 in its first L ternary digits. -/
def hasLeadingDigit2 (val L : Nat) : Bool :=
  let digits := toTernaryDigits val
  digits.take L |>.any (· == 2)

/-- Check bridge theorem: for all r in N_K \ {0,2,8}, 2^r has digit 2 in first L digits. -/
def checkBridge (K L : Nat) : Bool :=
  let nK := computeNK K
  nK.all fun r =>
    r == 0 || r == 2 || r == 8 || hasLeadingDigit2 (2 ^ r) L

/-- K=5: bridge theorem verified. -/
theorem bridge_K5 : checkBridge 5 30 = true := by native_decide

/-- K=6: bridge theorem verified. -/
theorem bridge_K6 : checkBridge 6 30 = true := by native_decide

/-- K=7: bridge theorem verified. -/
theorem bridge_K7 : checkBridge 7 30 = true := by native_decide

/-- K=8: bridge theorem verified. -/
theorem bridge_K8 : checkBridge 8 30 = true := by native_decide

/-- K=9: bridge theorem verified. -/
theorem bridge_K9 : checkBridge 9 30 = true := by native_decide

/-- Fast computeNK using pow2Mod (O(log n) per exponentiation vs O(n)). -/
def computeNKFast (K : Nat) : List Nat :=
  let period := uK K
  let modulus := 3 ^ K
  (List.range period).filter fun r =>
    let pow2r := pow2Mod r modulus
    !(hasTrailingDigit2 pow2r K)

/-- pow2Mod agrees with naive 2^e % m, so computeNKFast agrees with computeNK. -/
theorem computeNKFast_eq (K : Nat) : computeNKFast K = computeNK K := by
  unfold computeNKFast computeNK
  congr 1
  apply List.filter_congr
  intro r _
  rw [pow2Mod_eq]

/-- Bridge check using pow2Mod for trailing digits AND leading digits. -/
def checkBridgeCantorPow2 (K : Nat) : Bool :=
  (computeNKFast K).all fun r =>
    r == 0 || r == 2 || r == 8 || hasDigit2UpTo (pow2Mod r (3 ^ 50)) 50

/-! ## pow2Mod-based helpers for BridgeMiddle/BridgeMiddle16 -/

/-- Digit i of n equals digit i of n % 3^M, for i < M. -/
theorem digit_eq_of_modPow (n i M : Nat) (hi : i < M) :
    (n / 3 ^ i) % 3 = (n % 3 ^ M / 3 ^ i) % 3 := by
  have hlt : i + 1 ≤ M := Nat.succ_le_of_lt hi
  have h3i : 3 ^ i > 0 := Nat.pow_pos (by omega)
  have h3mi : 3 ^ (M - i) > 0 := Nat.pow_pos (by omega)
  have hsplit : 3 ^ i * 3 ^ (M - i) = 3 ^ M := by
    rw [← Nat.pow_add, Nat.add_sub_cancel' (Nat.le_of_lt hi)]
  have hmod1 : n % 3 ^ M / 3 ^ i = n / 3 ^ i % 3 ^ (M - i) := by
    have := Nat.mod_mul_right_div_self n (3 ^ i) (3 ^ (M - i))
    rw [hsplit] at this; exact this
  have hmod2 : n / 3 ^ i % 3 = n / 3 ^ i % 3 ^ (M - i) % 3 := by
    symm
    apply Nat.mod_mod_of_dvd
    exact Nat.pow_dvd_pow 3 (Nat.succ_le_of_lt (Nat.sub_pos_of_lt hi))
  rw [hmod1, hmod2]

end ErdosTernary.BridgeCompute
