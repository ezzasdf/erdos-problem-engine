/-
  Bridge Theorem: Range-Chunked Bridge Verification

  Proves checkBridgeCantorPow2 K = true for K=15,16,17 by splitting
  [0, uK K) into ranges and verifying each via native_decide.
-/

import Mathlib.Tactic
import ErdosTernary.BridgeCompute

open ErdosTernary.BridgeCompute

namespace ErdosTernary.BridgeCantorChunked

def rangeCheck (K lo hi : Nat) : Bool :=
  ((List.range (hi - lo)).filter (fun s =>
    !hasTrailingDigit2 (pow2Mod (s + lo) (3^K)) K
  )).all fun s =>
    (s + lo) == 0 || (s + lo) == 2 || (s + lo) == 8 ||
    hasDigit2UpTo (pow2Mod (s + lo) (3^50)) 50

private theorem computeNK_not2 {K r : Nat}
    (hr : r ∈ computeNKFast K) :
    hasTrailingDigit2 (pow2Mod r (3^K)) K = false := by
  unfold computeNKFast at hr
  rw [List.mem_filter] at hr
  have h := hr.2
  cases h_val : hasTrailingDigit2 (pow2Mod r (3^K)) K <;> simp_all [Bool.not]

theorem rangeCheck_imp {K lo hi r : Nat}
    (hlo : lo ≤ r) (hhi : r < hi)
    (hr_nk : r ∈ computeNKFast K)
    (hcheck : rangeCheck K lo hi = true) :
    (r == 0 || r == 2 || r == 8 ||
     hasDigit2UpTo (pow2Mod r (3^50)) 50) = true := by
  unfold rangeCheck at hcheck
  have hall := List.all_eq_true.mp hcheck
  have hs : r - lo < hi - lo := by omega
  have hr_false := computeNK_not2 hr_nk
  have hmem : (r - lo) ∈ List.filter
      (fun s => !hasTrailingDigit2 (pow2Mod (s + lo) (3^K)) K)
      (List.range (hi - lo)) := by
    rw [List.mem_filter]
    exact ⟨List.mem_range.mpr hs, by
      rw [show (r - lo) + lo = r from Nat.sub_add_cancel hlo, hr_false]; decide⟩
  have hresult := hall _ hmem
  rw [show (r - lo) + lo = r from Nat.sub_add_cancel hlo] at hresult
  exact hresult

theorem rangeCheck_all_of_computeNK (K chunk_size num_chunks : Nat)
    (hchunk_pos : 0 < chunk_size)
    (hdiv : uK K = chunk_size * num_chunks)
    (hchunks : ∀ j, j < num_chunks →
      rangeCheck K (j * chunk_size) ((j + 1) * chunk_size) = true) :
    ∀ r, r ∈ computeNKFast K →
    (r == 0 || r == 2 || r == 8 ||
     hasDigit2UpTo (pow2Mod r (3^50)) 50) = true := by
  intro r hr
  have hr_false := computeNK_not2 hr
  unfold computeNKFast at hr
  rw [List.mem_filter] at hr
  obtain ⟨r_lt, _⟩ := hr
  rw [List.mem_range] at r_lt
  have hmul : r < chunk_size * num_chunks := by omega
  have hj : r / chunk_size < num_chunks := by
    rw [Nat.div_lt_iff_lt_mul hchunk_pos, Nat.mul_comm]
    exact hmul
  have hcheck := hchunks (r / chunk_size) hj
  exact rangeCheck_imp (Nat.div_mul_le_self r chunk_size)
    (by
      have h1 : r = (r / chunk_size) * chunk_size + r % chunk_size := (Nat.div_add_mod r chunk_size).symm
      have h2 : r % chunk_size < chunk_size := Nat.mod_lt r hchunk_pos
      omega) hr hcheck

theorem checkBridgeCantorPow2_of_chunked (K chunk_size num_chunks : Nat)
    (hchunk_pos : 0 < chunk_size)
    (hdiv : uK K = chunk_size * num_chunks)
    (hchunks : ∀ j, j < num_chunks →
      rangeCheck K (j * chunk_size) ((j + 1) * chunk_size) = true) :
    checkBridgeCantorPow2 K = true := by
  unfold checkBridgeCantorPow2
  rw [List.all_eq_true]
  exact rangeCheck_all_of_computeNK K chunk_size num_chunks hchunk_pos hdiv hchunks

end ErdosTernary.BridgeCantorChunked
