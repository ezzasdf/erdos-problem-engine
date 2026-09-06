/-
  Bridge Theorem: Range-Chunked Bridge Verification
-/

import Mathlib.Tactic
import ErdosTernary.BridgeCompute

open ErdosTernary.BridgeCompute

namespace ErdosTernary.BridgeCantorChunked

def rangeCheck (K lo size : Nat) : Bool :=
  ((List.range size).filter (fun s =>
    !hasTrailingDigit2 (pow2Mod (s + lo) (3^K)) K
  )).all fun s =>
    (s + lo) == 0 || (s + lo) == 2 || (s + lo) == 8 ||
    hasDigit2UpTo (pow2Mod (s + lo) (3^50)) 50

private theorem computeNK_not2 {K r : Nat}
    (hr : r ∈ computeNKFast K) :
    hasTrailingDigit2 (pow2Mod r (3^K)) K = false := by
  unfold computeNKFast at hr
  rw [List.mem_filter] at hr
  cases h_val : hasTrailingDigit2 (pow2Mod r (3^K)) K <;> simp_all [Bool.not]

private theorem mod_div_cancel (r n : Nat) : r % n + r / n * n = r := by
  rw [Nat.add_comm]; exact (Nat.div_add_mod r n).symm

theorem checkBridgeCantorPow2_of_chunked (K chunk_size num_chunks : Nat)
    (hchunk_pos : 0 < chunk_size)
    (hdiv : uK K = chunk_size * num_chunks)
    (hchunks : ∀ j, j < num_chunks →
      rangeCheck K (j * chunk_size) chunk_size = true) :
    checkBridgeCantorPow2 K = true := by
  unfold checkBridgeCantorPow2
  rw [List.all_eq_true]
  intro r hr
  have hr_false := computeNK_not2 hr
  unfold computeNKFast at hr
  rw [List.mem_filter] at hr
  obtain ⟨r_lt, _⟩ := hr
  rw [List.mem_range] at r_lt
  have hmul : r < chunk_size * num_chunks := by omega
  have hj : r / chunk_size < num_chunks := by omega
  have hcheck := hchunks (r / chunk_size) hj
  unfold rangeCheck at hcheck
  have hall := List.all_eq_true.mp hcheck
  have hmod : r % chunk_size < chunk_size := Nat.mod_lt r hchunk_pos
  have hmem : r % chunk_size ∈ List.filter
      (fun s => !hasTrailingDigit2 (pow2Mod (s + r / chunk_size * chunk_size) (3^K)) K)
      (List.range chunk_size) := by
    rw [List.mem_filter]
    exact ⟨List.mem_range.mpr hmod, by
      rw [mod_div_cancel r chunk_size, hr_false]; decide⟩
  have hresult := hall _ hmem
  rw [mod_div_cancel r chunk_size] at hresult
  exact hresult

end ErdosTernary.BridgeCantorChunked
