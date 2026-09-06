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

theorem rangeCheck_imp {K lo hi r : Nat}
    (hlo : lo ≤ r) (hhi : r < hi)
    (hr_nk : r ∈ computeNKFast K)
    (hcheck : rangeCheck K lo hi = true) :
    (r == 0 || r == 2 || r == 8 ||
     hasDigit2UpTo (pow2Mod r (3^50)) 50) = true := by
  unfold rangeCheck at hcheck
  have hall := List.all_eq_true.mp hcheck
  have hs : r - lo < hi - lo := by omega
  show ((r - lo) + lo == 0 || (r - lo) + lo == 2 ||
    (r - lo) + lo == 8 ||
    hasDigit2UpTo (pow2Mod ((r - lo) + lo) (3^50)) 50) = true
  apply hall
  rw [List.mem_filter]
  refine ⟨List.mem_range.mpr hs, ?_⟩
  show !hasTrailingDigit2 (pow2Mod ((r - lo) + lo) (3^K)) K = true
  rw [show (r - lo) + lo = r by omega]
  unfold computeNKFast at hr_nk
  rw [List.mem_filter] at hr_nk
  exact hr_nk.2

theorem checkBridgeCantorPow2_of_chunked (K chunk_size num_chunks : Nat)
    (hchunk_pos : 0 < chunk_size)
    (hdiv : uK K = chunk_size * num_chunks)
    (hchunks : ∀ j, j < num_chunks →
      rangeCheck K (j * chunk_size) ((j + 1) * chunk_size) = true) :
    checkBridgeCantorPow2 K = true := by
  unfold checkBridgeCantorPow2
  rw [List.all_eq_true]
  intro r hr
  unfold computeNKFast at hr
  rw [List.mem_filter] at hr
  obtain ⟨r_lt, r_no2⟩ := hr
  rw [List.mem_range] at r_lt
  have hmul : r < chunk_size * num_chunks := by omega
  have hj : r / chunk_size < num_chunks := by
    rw [Nat.div_lt_iff_lt_mul hchunk_pos]
    exact hmul
  have hcheck := hchunks (r / chunk_size) hj
  unfold rangeCheck at hcheck
  have hall := List.all_eq_true.mp hcheck
  show ((r - r / chunk_size * chunk_size) + r / chunk_size * chunk_size == 0 ||
    (r - r / chunk_size * chunk_size) + r / chunk_size * chunk_size == 2 ||
    (r - r / chunk_size * chunk_size) + r / chunk_size * chunk_size == 8 ||
    hasDigit2UpTo (pow2Mod ((r - r / chunk_size * chunk_size) + r / chunk_size * chunk_size) (3^50)) 50) = true
  apply hall
  rw [List.mem_filter]
  refine ⟨List.mem_range.mpr (by omega), ?_⟩
  show !hasTrailingDigit2 (pow2Mod ((r - r / chunk_size * chunk_size) + r / chunk_size * chunk_size) (3^K)) K = true
  rw [show (r - r / chunk_size * chunk_size) + r / chunk_size * chunk_size = r by omega]
  exact r_no2

end ErdosTernary.BridgeCantorChunked
