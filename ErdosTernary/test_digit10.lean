import Mathlib.Tactic

-- Helper: 0 < 3^i
private lemma pow3_pos (i : ℕ) : 0 < 3^i :=
  Nat.pow_pos (by norm_num : (0 : ℕ) < 3)

-- Helper: w % 3^(i+1) / 3^i < 3
private lemma mod3_pow3_lt (w i : ℕ) : w % 3^(i+1) / 3^i < 3 := by
  have h := Nat.mod_lt (3^(i+1)) (pow3_pos (i+1))
  rw [show 3^(i+1) = 3^i * 3 from by rw [Nat.pow_succ]; ring] at h
  exact (Nat.div_lt_iff_lt_mul (pow3_pos i)).mpr h

-- Key lemma: w / 3^i % 3 = (w % 3^(i+1)) / 3^i
private lemma div_mod_eq (w i : ℕ) : w / 3^i % 3 = w % 3^(i+1) / 3^i := by
  have h31 : 3^(i+1) = 3^i * 3 := by rw [Nat.pow_succ]; ring
  have h := Nat.div_add_mod w (3^(i+1))
  -- h : w / 3^(i+1) * 3^(i+1) + w % 3^(i+1) = w
  -- Rewrite 3^(i+1) = 3^i * 3 in h
  rw [h31] at h
  -- h : w / (3^i * 3) * (3^i * 3) + w % (3^i * 3) = w
  -- Let a = w % (3^i * 3), b = w / (3^i * 3)
  -- w = a + b * (3^i * 3) = a + (b * 3) * 3^i
  have hw : w = w % 3^(i+1) + (w / 3^(i+1) * 3) * 3^i := by
    rw [h31]; linarith [h]
  -- Apply Nat.add_mul_div_right to get w / 3^i
  rw [hw, Nat.add_mul_div_right _ (pow3_pos i)]
  -- Goal: (w % 3^(i+1) + w / 3^(i+1) * 3 * 3^i) / 3^i % 3 
  --     = ... wait, the rw should have resolved
  -- Goal should now be: (w / 3^(i+1) * 3 + w % 3^(i+1) / 3^i) % 3 = w % 3^(i+1) / 3^i
  rw [Nat.add_mod]
  -- Show (w / 3^(i+1) * 3) % 3 = 0
  have : (w / 3^(i+1) * 3) % 3 = 0 := Nat.mul_mod_right _ _
  rw [this, Nat.zero_add]
  -- Now need: w % 3^(i+1) / 3^i % 3 = w % 3^(i+1) / 3^i
  exact Nat.mod_eq_of_lt (mod3_pow3_lt w i)

-- Digit equality: for i < n, (v % 3^n) / 3^i % 3 = v / 3^i % 3
private lemma digit_of_mod (v n i : ℕ) (hi : i < n) :
    (v % 3^n) / 3^i % 3 = v / 3^i % 3 := by
  rw [div_mod_eq, ← div_mod_eq]
  -- Need: (v % 3^n) % 3^(i+1) = v % 3^(i+1)
  rw [Nat.mod_mod_of_dvd]
  exact Nat.pow_dvd_pow _ (by omega : i + 1 ≤ n)

-- Trailing digit subset: if no digit 2 in K digits, no digit 2 in K-1 digits
-- After modding by 3^(K-1)
private lemma hasTrailingDigit2_def (val K : ℕ) :
    ErdosTernary.BridgeCompute.hasTrailingDigit2 val K =
      (List.range K).any fun i => (val / 3 ^ i) % 3 == 2 := rfl

private lemma trail_subset (v K : ℕ) (hK : K ≥ 1) :
    ErdosTernary.BridgeCompute.hasTrailingDigit2 v K = false →
    ErdosTernary.BridgeCompute.hasTrailingDigit2 (v % 3^(K-1)) (K-1) = false := by
  intro h
  unfold ErdosTernary.BridgeCompute.hasTrailingDigit2 at h ⊢
  simp only [Bool.not_eq_true] at h
  rw [List.any_eq_true] at h ⊢
  intro ⟨i, hi_mem, hi_eq⟩
  rw [List.mem_range] at hi_mem
  apply h
  refine ⟨i, List.mem_range.mpr (by omega), ?_⟩
  rw [bne_iff_ne] at hi_eq ⊢
  intro heq
  apply hi_eq
  rw [digit_of_mod v (K-1) i (by omega), heq]

#check @Nat.mul_mod_right
