import Mathlib.Tactic

theorem digit_mod_preserved (val p K : Nat) (hp : p < K) :
    (val % 3 ^ K / 3 ^ p) % 3 = (val / 3 ^ p) % 3 := by
  have hpk : p ≤ K := by omega
  have hp_pos : 0 < 3 ^ p := Nat.pow_pos (by omega)
  have h3k : 3 ^ K = 3 ^ p * 3 ^ (K - p) := by
    rw [show K = p + (K - p) from (Nat.add_sub_cancel' hpk).symm, Nat.pow_add]
  have h := Nat.div_add_mod val (3 ^ K)
  rw [h3k] at h ⊢
  have hdvd : 3 ^ p ∣ val / (3 ^ p * 3 ^ (K - p)) * (3 ^ p * 3 ^ (K - p)) := by
    exact ⟨val / (3 ^ p * 3 ^ (K - p)) * 3 ^ (K - p), by ring⟩
  sorry
