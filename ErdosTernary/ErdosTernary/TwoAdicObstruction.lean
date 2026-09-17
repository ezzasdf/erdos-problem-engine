import Mathlib.Tactic

/-!
# Two-Adic Obstruction for a_d = 1

When a binary polynomial of degree d-1 has leading coefficient a_d = 1,
the representation P(3) = 2^r requires:
  3^d + evalBit(d, lower bits) ≡ 0 (mod 2^{d+4}).
This is impossible for all d ≤ 23.

Key computational fact: v2(S + 3^d) ≤ d + 3 for ALL d (verified up to d=50).
The bound is tight only at d=5 (v2=8=d+3). For d ≥ 6, max v2 ≤ d+2.
-/

namespace TwoAdicObstruction

def evalBit : ℕ → ℕ → ℕ
| 0, _ => 0
| d + 1, n => (if n.testBit d then 3 ^ d else 0) + evalBit d n

-- evalBit only reads the lower d bits of n
lemma mod_two_pow (d n : ℕ) : n % 2 ^ (d + 1) % 2 ^ d = n % 2 ^ d := by
  rw [Nat.mod_mod_of_dvd n (show 2 ^ d ∣ 2 ^ (d + 1) from ⟨2, by ring⟩)]

theorem evalBit_mod (d n : ℕ) : evalBit d n = evalBit d (n % 2 ^ d) := by
  induction d generalizing n with
  | zero => simp [evalBit]
  | succ d ih =>
    simp only [evalBit]
    have htb : (n % 2 ^ (d + 1)).testBit d = n.testBit d := by
      rw [Nat.testBit_mod_two_pow]; simp [Nat.lt_succ_self]
    rw [htb, ih n, ih (n % 2 ^ (d + 1)), mod_two_pow]

-- native_decide certificates: for each d, all 2^d bit patterns fail
private theorem obs0 : ∀ i : Fin 1, ¬(2^4 ∣ 1 + evalBit 0 i) := by native_decide
private theorem obs1 : ∀ i : Fin 2, ¬(2^5 ∣ 3 + evalBit 1 i) := by native_decide
private theorem obs2 : ∀ i : Fin 4, ¬(2^6 ∣ 9 + evalBit 2 i) := by native_decide
private theorem obs3 : ∀ i : Fin 8, ¬(2^7 ∣ 27 + evalBit 3 i) := by native_decide
private theorem obs4 : ∀ i : Fin 16, ¬(2^8 ∣ 81 + evalBit 4 i) := by native_decide
private theorem obs5 : ∀ i : Fin 32, ¬(2^9 ∣ 243 + evalBit 5 i) := by native_decide
private theorem obs6 : ∀ i : Fin 64, ¬(2^10 ∣ 729 + evalBit 6 i) := by native_decide
private theorem obs7 : ∀ i : Fin 128, ¬(2^11 ∣ 2187 + evalBit 7 i) := by native_decide
private theorem obs8 : ∀ i : Fin 256, ¬(2^12 ∣ 6561 + evalBit 8 i) := by native_decide
private theorem obs9 : ∀ i : Fin 512, ¬(2^13 ∣ 19683 + evalBit 9 i) := by native_decide
private theorem obs10 : ∀ i : Fin 1024, ¬(2^14 ∣ 59049 + evalBit 10 i) := by native_decide
private theorem obs11 : ∀ i : Fin 2048, ¬(2^15 ∣ 177147 + evalBit 11 i) := by native_decide
private theorem obs12 : ∀ i : Fin 4096, ¬(2^16 ∣ 531441 + evalBit 12 i) := by native_decide

-- Extended certificates: d=13..20
private theorem obs13 : ∀ i : Fin 8192, ¬(2^17 ∣ 1594323 + evalBit 13 i) := by native_decide
private theorem obs14 : ∀ i : Fin 16384, ¬(2^18 ∣ 4782969 + evalBit 14 i) := by native_decide
private theorem obs15 : ∀ i : Fin 32768, ¬(2^19 ∣ 14348907 + evalBit 15 i) := by native_decide
private theorem obs16 : ∀ i : Fin 65536, ¬(2^20 ∣ 43046721 + evalBit 16 i) := by native_decide
private theorem obs17 : ∀ i : Fin 131072, ¬(2^21 ∣ 129140163 + evalBit 17 i) := by native_decide
private theorem obs18 : ∀ i : Fin 262144, ¬(2^22 ∣ 387420489 + evalBit 18 i) := by native_decide
private theorem obs19 : ∀ i : Fin 524288, ¬(2^23 ∣ 1162261467 + evalBit 19 i) := by native_decide
private theorem obs20 : ∀ i : Fin 1048576, ¬(2^24 ∣ 3486784401 + evalBit 20 i) := by native_decide
private theorem obs21 : ∀ i : Fin 2097152, ¬(2^25 ∣ 10460353203 + evalBit 21 i) := by native_decide
private theorem obs22 : ∀ i : Fin 4194304, ¬(2^26 ∣ 31381059609 + evalBit 22 i) := by native_decide
private theorem obs23 : ∀ i : Fin 8388608, ¬(2^27 ∣ 94143178827 + evalBit 23 i) := by native_decide
-- private theorem obs24 : ∀ i : Fin 16777216, ¬(2^28 ∣ 282429536481 + evalBit 24 i) := by native_decide

-- Numeric certificates: 3^d and 2^{d+4} as concrete values
-- d: 0  1   2    3     4      5       6        7         8          9           10            11              12
-- 3^d: 1  3   9   27    81    243     729     2187      6561      19683       59049        177147          531441
-- 2^{d+4}: 16 32 64 128  256   512    1024     2048      4096      8192       16384        32768           65536

-- Bridge: after rcases rfl, convert 3^d → concrete, apply obs theorem
private lemma nat3_pow_0 : (3^0 : ℕ) = 1 := by norm_num
private lemma nat3_pow_1 : (3^1 : ℕ) = 3 := by norm_num
private lemma nat3_pow_2 : (3^2 : ℕ) = 9 := by norm_num
private lemma nat3_pow_3 : (3^3 : ℕ) = 27 := by norm_num
private lemma nat3_pow_4 : (3^4 : ℕ) = 81 := by norm_num
private lemma nat3_pow_5 : (3^5 : ℕ) = 243 := by norm_num
private lemma nat3_pow_6 : (3^6 : ℕ) = 729 := by norm_num
private lemma nat3_pow_7 : (3^7 : ℕ) = 2187 := by norm_num
private lemma nat3_pow_8 : (3^8 : ℕ) = 6561 := by norm_num
private lemma nat3_pow_9 : (3^9 : ℕ) = 19683 := by norm_num
private lemma nat3_pow_10 : (3^10 : ℕ) = 59049 := by norm_num
private lemma nat3_pow_11 : (3^11 : ℕ) = 177147 := by norm_num
private lemma nat3_pow_12 : (3^12 : ℕ) = 531441 := by norm_num

private lemma nat2_pow_4 : (2^4 : ℕ) = 16 := by norm_num
private lemma nat2_pow_5 : (2^5 : ℕ) = 32 := by norm_num
private lemma nat2_pow_6 : (2^6 : ℕ) = 64 := by norm_num
private lemma nat2_pow_7 : (2^7 : ℕ) = 128 := by norm_num
private lemma nat2_pow_8 : (2^8 : ℕ) = 256 := by norm_num
private lemma nat2_pow_9 : (2^9 : ℕ) = 512 := by norm_num
private lemma nat2_pow_10 : (2^10 : ℕ) = 1024 := by norm_num
private lemma nat2_pow_11 : (2^11 : ℕ) = 2048 := by norm_num
private lemma nat2_pow_12 : (2^12 : ℕ) = 4096 := by norm_num
private lemma nat2_pow_13 : (2^13 : ℕ) = 8192 := by norm_num
private lemma nat2_pow_14 : (2^14 : ℕ) = 16384 := by norm_num
private lemma nat2_pow_15 : (2^15 : ℕ) = 32768 := by norm_num
private lemma nat2_pow_16 : (2^16 : ℕ) = 65536 := by norm_num

private lemma nat3_pow_13 : (3^13 : ℕ) = 1594323 := by norm_num
private lemma nat3_pow_14 : (3^14 : ℕ) = 4782969 := by norm_num
private lemma nat3_pow_15 : (3^15 : ℕ) = 14348907 := by norm_num
private lemma nat3_pow_16 : (3^16 : ℕ) = 43046721 := by norm_num
private lemma nat3_pow_17 : (3^17 : ℕ) = 129140163 := by norm_num
private lemma nat3_pow_18 : (3^18 : ℕ) = 387420489 := by norm_num
private lemma nat3_pow_19 : (3^19 : ℕ) = 1162261467 := by norm_num
private lemma nat3_pow_20 : (3^20 : ℕ) = 3486784401 := by norm_num

private lemma nat3_pow_21 : (3^21 : ℕ) = 10460353203 := by norm_num
private lemma nat3_pow_22 : (3^22 : ℕ) = 31381059609 := by norm_num
private lemma nat3_pow_23 : (3^23 : ℕ) = 94143178827 := by norm_num
-- private lemma nat3_pow_24 : (3^24 : ℕ) = 282429536481 := by norm_num

private lemma nat2_pow_17 : (2^17 : ℕ) = 131072 := by norm_num
private lemma nat2_pow_18 : (2^18 : ℕ) = 262144 := by norm_num
private lemma nat2_pow_19 : (2^19 : ℕ) = 524288 := by norm_num
private lemma nat2_pow_20 : (2^20 : ℕ) = 1048576 := by norm_num
private lemma nat2_pow_21 : (2^21 : ℕ) = 2097152 := by norm_num
private lemma nat2_pow_22 : (2^22 : ℕ) = 4194304 := by norm_num
private lemma nat2_pow_23 : (2^23 : ℕ) = 8388608 := by norm_num
private lemma nat2_pow_24 : (2^24 : ℕ) = 16777216 := by norm_num

private lemma nat2_pow_25 : (2^25 : ℕ) = 33554432 := by norm_num
private lemma nat2_pow_26 : (2^26 : ℕ) = 67108864 := by norm_num
private lemma nat2_pow_27 : (2^27 : ℕ) = 134217728 := by norm_num
-- private lemma nat2_pow_28 : (2^28 : ℕ) = 268435456 := by norm_num

-- Per-case proof: for each d, after rcases rfl + rw evalBit_mod,
-- bridge from 3^d notation to concrete number, apply obs, close.
private lemma case0 (n : ℕ) (k : ℕ)
    (hk : 3^0 + evalBit 0 (n % 2^0) = 2^(0+4) * k) : False := by
  rw [nat3_pow_0, nat2_pow_4] at hk
  exact absurd ⟨k, hk⟩ (obs0 ⟨0, by omega⟩)

private lemma case1 (n : ℕ) (k : ℕ)
    (hk : 3^1 + evalBit 1 (n % 2^1) = 2^(1+4) * k) : False := by
  rw [nat3_pow_1, nat2_pow_5] at hk
  exact absurd ⟨k, hk⟩ (obs1 ⟨n % 2, Nat.mod_lt _ (by omega)⟩)

private lemma case2 (n : ℕ) (k : ℕ)
    (hk : 3^2 + evalBit 2 (n % 2^2) = 2^(2+4) * k) : False := by
  rw [nat3_pow_2, nat2_pow_6] at hk
  exact absurd ⟨k, hk⟩ (obs2 ⟨n % 4, Nat.mod_lt _ (by omega)⟩)

private lemma case3 (n : ℕ) (k : ℕ)
    (hk : 3^3 + evalBit 3 (n % 2^3) = 2^(3+4) * k) : False := by
  rw [nat3_pow_3, nat2_pow_7] at hk
  exact absurd ⟨k, hk⟩ (obs3 ⟨n % 8, Nat.mod_lt _ (by omega)⟩)

private lemma case4 (n : ℕ) (k : ℕ)
    (hk : 3^4 + evalBit 4 (n % 2^4) = 2^(4+4) * k) : False := by
  rw [nat3_pow_4, nat2_pow_8] at hk
  exact absurd ⟨k, hk⟩ (obs4 ⟨n % 16, Nat.mod_lt _ (by omega)⟩)

private lemma case5 (n : ℕ) (k : ℕ)
    (hk : 3^5 + evalBit 5 (n % 2^5) = 2^(5+4) * k) : False := by
  rw [nat3_pow_5, nat2_pow_9] at hk
  exact absurd ⟨k, hk⟩ (obs5 ⟨n % 32, Nat.mod_lt _ (by omega)⟩)

private lemma case6 (n : ℕ) (k : ℕ)
    (hk : 3^6 + evalBit 6 (n % 2^6) = 2^(6+4) * k) : False := by
  rw [nat3_pow_6, nat2_pow_10] at hk
  exact absurd ⟨k, hk⟩ (obs6 ⟨n % 64, Nat.mod_lt _ (by omega)⟩)

private lemma case7 (n : ℕ) (k : ℕ)
    (hk : 3^7 + evalBit 7 (n % 2^7) = 2^(7+4) * k) : False := by
  rw [nat3_pow_7, nat2_pow_11] at hk
  exact absurd ⟨k, hk⟩ (obs7 ⟨n % 128, Nat.mod_lt _ (by omega)⟩)

private lemma case8 (n : ℕ) (k : ℕ)
    (hk : 3^8 + evalBit 8 (n % 2^8) = 2^(8+4) * k) : False := by
  rw [nat3_pow_8, nat2_pow_12] at hk
  exact absurd ⟨k, hk⟩ (obs8 ⟨n % 256, Nat.mod_lt _ (by omega)⟩)

private lemma case9 (n : ℕ) (k : ℕ)
    (hk : 3^9 + evalBit 9 (n % 2^9) = 2^(9+4) * k) : False := by
  rw [nat3_pow_9, nat2_pow_13] at hk
  exact absurd ⟨k, hk⟩ (obs9 ⟨n % 512, Nat.mod_lt _ (by omega)⟩)

private lemma case10 (n : ℕ) (k : ℕ)
    (hk : 3^10 + evalBit 10 (n % 2^10) = 2^(10+4) * k) : False := by
  rw [nat3_pow_10, nat2_pow_14] at hk
  exact absurd ⟨k, hk⟩ (obs10 ⟨n % 1024, Nat.mod_lt _ (by omega)⟩)

private lemma case11 (n : ℕ) (k : ℕ)
    (hk : 3^11 + evalBit 11 (n % 2^11) = 2^(11+4) * k) : False := by
  rw [nat3_pow_11, nat2_pow_15] at hk
  exact absurd ⟨k, hk⟩ (obs11 ⟨n % 2048, Nat.mod_lt _ (by omega)⟩)

private lemma case12 (n : ℕ) (k : ℕ)
    (hk : 3^12 + evalBit 12 (n % 2^12) = 2^(12+4) * k) : False := by
  rw [nat3_pow_12, nat2_pow_16] at hk
  exact absurd ⟨k, hk⟩ (obs12 ⟨n % 4096, Nat.mod_lt _ (by omega)⟩)

private lemma case13 (n : ℕ) (k : ℕ)
    (hk : 3^13 + evalBit 13 (n % 2^13) = 2^(13+4) * k) : False := by
  rw [nat3_pow_13, nat2_pow_17] at hk
  exact absurd ⟨k, hk⟩ (obs13 ⟨n % 8192, Nat.mod_lt _ (by omega)⟩)

private lemma case14 (n : ℕ) (k : ℕ)
    (hk : 3^14 + evalBit 14 (n % 2^14) = 2^(14+4) * k) : False := by
  rw [nat3_pow_14, nat2_pow_18] at hk
  exact absurd ⟨k, hk⟩ (obs14 ⟨n % 16384, Nat.mod_lt _ (by omega)⟩)

private lemma case15 (n : ℕ) (k : ℕ)
    (hk : 3^15 + evalBit 15 (n % 2^15) = 2^(15+4) * k) : False := by
  rw [nat3_pow_15, nat2_pow_19] at hk
  exact absurd ⟨k, hk⟩ (obs15 ⟨n % 32768, Nat.mod_lt _ (by omega)⟩)

private lemma case16 (n : ℕ) (k : ℕ)
    (hk : 3^16 + evalBit 16 (n % 2^16) = 2^(16+4) * k) : False := by
  rw [nat3_pow_16, nat2_pow_20] at hk
  exact absurd ⟨k, hk⟩ (obs16 ⟨n % 65536, Nat.mod_lt _ (by omega)⟩)

private lemma case17 (n : ℕ) (k : ℕ)
    (hk : 3^17 + evalBit 17 (n % 2^17) = 2^(17+4) * k) : False := by
  rw [nat3_pow_17, nat2_pow_21] at hk
  exact absurd ⟨k, hk⟩ (obs17 ⟨n % 131072, Nat.mod_lt _ (by omega)⟩)

private lemma case18 (n : ℕ) (k : ℕ)
    (hk : 3^18 + evalBit 18 (n % 2^18) = 2^(18+4) * k) : False := by
  rw [nat3_pow_18, nat2_pow_22] at hk
  exact absurd ⟨k, hk⟩ (obs18 ⟨n % 262144, Nat.mod_lt _ (by omega)⟩)

private lemma case19 (n : ℕ) (k : ℕ)
    (hk : 3^19 + evalBit 19 (n % 2^19) = 2^(19+4) * k) : False := by
  rw [nat3_pow_19, nat2_pow_23] at hk
  exact absurd ⟨k, hk⟩ (obs19 ⟨n % 524288, Nat.mod_lt _ (by omega)⟩)

private lemma case20 (n : ℕ) (k : ℕ)
    (hk : 3^20 + evalBit 20 (n % 2^20) = 2^(20+4) * k) : False := by
  rw [nat3_pow_20, nat2_pow_24] at hk
  exact absurd ⟨k, hk⟩ (obs20 ⟨n % 1048576, Nat.mod_lt _ (by omega)⟩)

private lemma case21 (n : ℕ) (k : ℕ)
    (hk : 3^21 + evalBit 21 (n % 2^21) = 2^(21+4) * k) : False := by
  rw [nat3_pow_21, nat2_pow_25] at hk
  exact absurd ⟨k, hk⟩ (obs21 ⟨n % 2097152, Nat.mod_lt _ (by omega)⟩)

private lemma case22 (n : ℕ) (k : ℕ)
    (hk : 3^22 + evalBit 22 (n % 2^22) = 2^(22+4) * k) : False := by
  rw [nat3_pow_22, nat2_pow_26] at hk
  exact absurd ⟨k, hk⟩ (obs22 ⟨n % 4194304, Nat.mod_lt _ (by omega)⟩)

private lemma case23 (n : ℕ) (k : ℕ)
    (hk : 3^23 + evalBit 23 (n % 2^23) = 2^(23+4) * k) : False := by
  rw [nat3_pow_23, nat2_pow_27] at hk
  exact absurd ⟨k, hk⟩ (obs23 ⟨n % 8388608, Nat.mod_lt _ (by omega)⟩)

-- private lemma case24 (n : ℕ) (k : ℕ)
--     (hk : 3^24 + evalBit 24 (n % 2^24) = 2^(24+4) * k) : False := by
--   rw [nat3_pow_24, nat2_pow_28] at hk
--   exact absurd ⟨k, hk⟩ (obs24 ⟨n % 16777216, Nat.mod_lt _ (by omega)⟩)

-- The main theorem: for d ≤ 22, no binary encoding can hit the obstruction
-- The main theorem: for d ≤ 20, no binary encoding can hit the obstruction
theorem obstruction_le20 (d : ℕ) (hd : d ≤ 20) (n : ℕ) :
    ¬(2 ^ (d + 4) ∣ 3 ^ d + evalBit d n) := by
  intro ⟨k, hk⟩
  rw [evalBit_mod d n] at hk
  have hc : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨
            d = 6 ∨ d = 7 ∨ d = 8 ∨ d = 9 ∨ d = 10 ∨ d = 11 ∨ d = 12 ∨
            d = 13 ∨ d = 14 ∨ d = 15 ∨ d = 16 ∨ d = 17 ∨ d = 18 ∨ d = 19 ∨ d = 20 := by omega
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact case0 n k hk
  · exact case1 n k hk
  · exact case2 n k hk
  · exact case3 n k hk
  · exact case4 n k hk
  · exact case5 n k hk
  · exact case6 n k hk
  · exact case7 n k hk
  · exact case8 n k hk
  · exact case9 n k hk
  · exact case10 n k hk
  · exact case11 n k hk
  · exact case12 n k hk
  · exact case13 n k hk
  · exact case14 n k hk
  · exact case15 n k hk
  · exact case16 n k hk
  · exact case17 n k hk
  · exact case18 n k hk
  · exact case19 n k hk
  · exact case20 n k hk

-- Extended: for d ≤ 23, no binary encoding can hit the obstruction
theorem obstruction_le23 (d : ℕ) (hd : d ≤ 23) (n : ℕ) :
    ¬(2 ^ (d + 4) ∣ 3 ^ d + evalBit d n) := by
  intro ⟨k, hk⟩
  rw [evalBit_mod d n] at hk
  rcases show d ≤ 20 ∨ d = 21 ∨ d = 22 ∨ d = 23 by omega with hd20 | rfl | rfl | rfl
  · exact absurd ⟨k, hk⟩ (obstruction_le20 d hd20 (n % 2 ^ d))
  · exact case21 n k hk
  · exact case22 n k hk
  · exact case23 n k hk

-- Backward-compatible alias
theorem obstruction_le22 (d : ℕ) (hd : d ≤ 22) (n : ℕ) :
    ¬(2 ^ (d + 4) ∣ 3 ^ d + evalBit d n) :=
  obstruction_le23 d (by omega) n

-- Backward-compatible alias
theorem obstruction_le12 (d : ℕ) (hd : d ≤ 12) (n : ℕ) :
    ¬(2 ^ (d + 4) ∣ 3 ^ d + evalBit d n) :=
  obstruction_le20 d (by omega) n

end TwoAdicObstruction
