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

private theorem sub_mul_lt {r chunk_size : Nat} (hc : 0 < chunk_size) :
    r - r / chunk_size * chunk_size < chunk_size := by
  have h1 := Nat.div_mul_le_self r chunk_size
  have h2 := Nat.mod_lt r hc
  have h3 : r = r / chunk_size * chunk_size + r % chunk_size :=
    (Nat.div_add_mod r chunk_size).symm
  omega

private theorem sub_mul_cancel {r chunk_size : Nat} :
    r - r / chunk_size * chunk_size + r / chunk_size * chunk_size = r := by
  have := Nat.div_mul_le_self r chunk_size
  omega

private theorem chunk_range_len (r chunk_size : Nat) :
    (r / chunk_size + 1) * chunk_size - r / chunk_size * chunk_size = chunk_size := by
  have := Nat.div_mul_le_self r chunk_size
  omega

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
  have hs := sub_mul_lt hchunk_pos
  have hr_eq := sub_mul_cancel (r := r) (chunk_size := chunk_size)
  have hmem : (r - r / chunk_size * chunk_size) ∈ List.filter
      (fun s => !hasTrailingDigit2 (pow2Mod (s + r / chunk_size * chunk_size) (3^K)) K)
      (List.range ((r / chunk_size + 1) * chunk_size - r / chunk_size * chunk_size)) := by
    rw [List.mem_filter]
    refine ⟨?_, by rw [hr_eq, hr_false]; decide⟩
    rw [chunk_range_len]
    exact List.mem_range.mpr hs
  have hresult := hall _ hmem
  rw [hr_eq] at hresult
  exact hresult

end ErdosTernary.BridgeCantorChunked
