/-
  Bridge Theorem: Range-Chunked Bridge Verification
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
  cases h_val : hasTrailingDigit2 (pow2Mod r (3^K)) K <;> simp_all [Bool.not]

private theorem chunk_range_len (r chunk_size : Nat) :
    (r / chunk_size + 1) * chunk_size - r / chunk_size * chunk_size = chunk_size := by
  rw [Nat.succ_mul, Nat.add_comm, Nat.add_sub_cancel_right]

theorem checkBridgeCantorPow2_of_chunked (K chunk_size num_chunks : Nat)
    (hchunk_pos : 0 < chunk_size)
    (hdiv : uK K = chunk_size * num_chunks)
    (hchunks : ∀ j, j < num_chunks →
      rangeCheck K (j * chunk_size) ((j + 1) * chunk_size) = true) :
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
  have hj : r / chunk_size < num_chunks := by
    rw [Nat.div_lt_iff_lt_mul hchunk_pos, Nat.mul_comm]; exact hmul
  have hcheck := hchunks (r / chunk_size) hj
  unfold rangeCheck at hcheck
  have hall := List.all_eq_true.mp hcheck
  have hlo : r / chunk_size * chunk_size ≤ r := Nat.div_mul_le_self r chunk_size
  have hr_eq : r - r / chunk_size * chunk_size + r / chunk_size * chunk_size = r := by omega
  have hs : r - r / chunk_size * chunk_size < chunk_size := by omega
  have hmem : (r - r / chunk_size * chunk_size) ∈ List.filter
      (fun s => !hasTrailingDigit2 (pow2Mod (s + r / chunk_size * chunk_size) (3^K)) K)
      (List.range ((r / chunk_size + 1) * chunk_size - r / chunk_size * chunk_size)) := by
    rw [List.mem_filter, chunk_range_len]
    refine ⟨List.mem_range.mpr hs, by rw [hr_eq, hr_false]; decide⟩
  have hresult := hall _ hmem
  simp only [hr_eq] at hresult
  exact hresult

end ErdosTernary.BridgeCantorChunked
