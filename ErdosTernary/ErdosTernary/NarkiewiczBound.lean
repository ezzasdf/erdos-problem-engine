import Mathlib.Tactic
import ErdosTernary.Narkiewicz
import ErdosTernary.SayeLemma

open ErdosTernary.SayeLemma

/-!
  Narkiewicz's 1980 counting bound `N(x) ≤ 4·x^(log₃2)`.

  - Task 2c.1: low ternary digits are preserved by reducing modulo `3^K`.
  - Task 2c.2: the order of `2` modulo `3^k` is exactly `u k = 2·3^(k-1)`.
-/

namespace NarkiewiczBound

open Narkiewicz
open ErdosTernary.SayeLemma

/-- Low ternary digits of `m` are preserved by `m % 3^K` for indices below `K`. -/
theorem digit₃_mod_pow (m K i : ℕ) (hi : i < K) :
    digit₃ (m % 3 ^ K) i = digit₃ m i := by
  unfold digit₃
  have hpow : 3 ^ K = 3 ^ i * 3 ^ (K - i) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [hpow]
  rw [Nat.mod_mul_right_div_self]
  rw [Nat.mod_mod_of_dvd (m / 3 ^ i) (by simpa using pow_dvd_pow 3 (by omega : 1 ≤ K - i))]

/-- High ternary digits of `m % 3^K` (indices at least `K`) are all zero. -/
theorem digit₃_mod_pow_high (m K i : ℕ) (hiK : K ≤ i) :
    digit₃ (m % 3 ^ K) i = 0 := by
  unfold digit₃
  have hlt : m % 3 ^ K < 3 ^ i :=
    lt_of_lt_of_le (Nat.mod_lt m (by positivity : 0 < 3 ^ K))
      (pow_le_pow_right (by norm_num : 1 ≤ (3 : ℕ)) hiK)
  rw [Nat.div_eq_of_lt hlt]

/-- Reducing a Cantor-set number modulo `3^K` keeps it in the Cantor set. -/
theorem cantor_mod_pow (m K : ℕ) (hm : memCantorNat m) :
    memCantorNat (m % 3 ^ K) := by
  unfold memCantorNat
  intro i
  by_cases hi : i < K
  · have h := hm i
    have hd : digit₃ (m % 3 ^ K) i = digit₃ m i := digit₃_mod_pow m K i hi
    rwa [← hd] at h
  · have hiK : K ≤ i := by omega
    rw [digit₃_mod_pow_high m K i hiK]
    norm_num

end NarkiewiczBound

section Task_2c_2

open NarkiewiczBound

/-- `1 % 3^k = 1` for `k ≥ 1`. -/
theorem one_mod_pow_three (k : ℕ) (hk : k ≥ 1) : 1 % 3 ^ k = 1 := by
  apply Nat.mod_eq_of_lt
  have hle : 3 ≤ 3 ^ k := by
    simpa using (pow_le_pow_right (by norm_num : 1 ≤ (3 : ℕ)) (by omega : 1 ≤ k))
  omega

/-- For `1 ≤ j ≤ 2`, `1` is not congruent to `1 + j·3^k` modulo `3^(k+1)`. -/
theorem not_one_add_mod_three_pow (k j : ℕ) (hk : k ≥ 1) (hj : 1 ≤ j) (hj2 : j ≤ 2) :
    ¬ (1 ≡ 1 + j * 3 ^ k [MOD 3 ^ (k + 1)]) := by
  intro h
  rw [Nat.ModEq] at h
  rw [one_mod_pow_three (k + 1) (by omega)] at h
  rw [show (1 + j * 3 ^ k) % 3 ^ (k + 1) = 1 + j * 3 ^ k from by
    apply Nat.mod_eq_of_lt
    have hx1 : 1 < 3 ^ k := by
      have hle : 3 ≤ 3 ^ k := by
        simpa using (pow_le_pow_right (by norm_num : 1 ≤ (3 : ℕ)) (by omega : 1 ≤ k))
      omega
    rw [pow_succ]
    nlinarith] at h
  have hpos : 0 < j * 3 ^ k := Nat.mul_pos (by omega : 0 < j) (by positivity : 0 < 3 ^ k)
  omega

/-- `2^(u k) ≡ 1 + 3^k` modulo `3^(k+1)`. -/
theorem pow_u_mod_strong_modEq (k : ℕ) (hk : k ≥ 1) :
    2 ^ u k ≡ 1 + 3 ^ k [MOD 3 ^ (k + 1)] := by
  rw [Nat.ModEq]
  rw [show (1 + 3 ^ k) % 3 ^ (k + 1) = 1 + 3 ^ k from by
    apply Nat.mod_eq_of_lt
    have hle : 3 ≤ 3 ^ k := by
      simpa using (pow_le_pow_right (by norm_num : 1 ≤ (3 : ℕ)) (by omega : 1 ≤ k))
    rw [pow_succ]
    omega]
  exact pow_u_mod_strong k hk

/-- `2^(u k) ≡ 1` modulo `3^k`. -/
theorem pow_u_mod_modEq (k : ℕ) (hk : k ≥ 1) :
    2 ^ u k ≡ 1 [MOD 3 ^ k] := by
  rw [Nat.ModEq]
  rw [one_mod_pow_three k hk]
  exact pow_u_mod k hk

/-- `u (k+1) = 3·u k`. -/
theorem u_succ (k : ℕ) (hk : k ≥ 1) : u (k + 1) = 3 * u k := by
  unfold u
  rw [show (k + 1) - 1 = k by omega]
  have hk' : k = (k - 1) + 1 := by omega
  have hpow2 : 3 ^ k = 3 ^ (k - 1) * 3 := by
    rw [show 3 ^ k = 3 ^ ((k - 1) + 1) from congrArg (fun n => 3 ^ n) hk']
    rw [pow_add]
    norm_num
  rw [hpow2, mul_comm (3 ^ (k - 1)) 3]
  ring

/-- Block congruence: `2^(a·u k + b) ≡ 2^b` modulo `3^k`. -/
theorem pow_mod_block (k a b : ℕ) (hk : k ≥ 1) :
    2 ^ (a * u k + b) ≡ 2 ^ b [MOD 3 ^ k] := by
  rw [show 2 ^ (a * u k + b) = (2 ^ u k) ^ a * 2 ^ b from by
    rw [pow_add]
    rw [mul_comm a (u k)]
    rw [pow_mul]]
  simpa using (Nat.ModEq.mul (Nat.ModEq.pow a (pow_u_mod_modEq k hk)) (Nat.ModEq.refl (2 ^ b)))

/-- Minimality of the period: no `0 < m < u k` is a period of `2` modulo `3^k`. -/
theorem not_pow_mod_period (k : ℕ) (hk : k ≥ 1) :
    ∀ m : ℕ, 0 < m → m < u k → ¬ (2 ^ m ≡ 1 [MOD 3 ^ k]) := by
  induction k with
  | zero => omega
  | succ k ih =>
    intro m hm hlt hcong
    by_cases hk0 : k ≥ 1
    · have ihk : ∀ m : ℕ, 0 < m → m < u k → ¬ (2 ^ m ≡ 1 [MOD 3 ^ k]) := ih hk0
      have hcongk : 2 ^ m ≡ 1 [MOD 3 ^ k] :=
        Nat.ModEq.of_dvd (by simpa using Nat.pow_dvd_pow 3 (by omega : k ≤ k + 1)) hcong
      have hge : u k ≤ m := by
        by_contra hlt'
        exact (ihk m hm (by omega : m < u k)) hcongk
      rcases Nat.exists_eq_add_of_le hge with ⟨r, hr⟩
      have hu : u (k + 1) = 3 * u k := u_succ k hk0
      have hrlt : r < 2 * u k := by
        have hm3 : m < 3 * u k := by
          rw [← hu]
          exact hlt
        rw [hr] at hm3
        omega
      have hstrong : 2 ^ u k ≡ 1 + 3 ^ k [MOD 3 ^ (k + 1)] := pow_u_mod_strong_modEq k hk0
      have hcong2 : (1 + 3 ^ k) * 2 ^ r ≡ 1 [MOD 3 ^ (k + 1)] := by
        have hpm : 2 ^ m ≡ (1 + 3 ^ k) * 2 ^ r [MOD 3 ^ (k + 1)] := by
          rw [hr]
          rw [show 2 ^ (u k + r) = 2 ^ (u k) * 2 ^ r from by rw [pow_add]]
          exact Nat.ModEq.mul hstrong (Nat.ModEq.refl (2 ^ r))
        exact hpm.symm.trans hcong
      have hcongr : 2 ^ r ≡ 1 [MOD 3 ^ k] := by
        have hred := Nat.ModEq.of_dvd (by simpa using Nat.pow_dvd_pow 3 (by omega : k ≤ k + 1)) hcong2
        have hone : 1 + 3 ^ k ≡ 1 [MOD 3 ^ k] := by
          have h3 : 3 ^ k ≡ 0 [MOD 3 ^ k] := by
            rw [Nat.ModEq]
            simp
          exact (Nat.ModEq.add (Nat.ModEq.refl 1) h3)
        have hmult : (1 + 3 ^ k) * 2 ^ r ≡ 2 ^ r [MOD 3 ^ k] := by
          simpa only [one_mul] using (Nat.ModEq.mul hone (Nat.ModEq.refl (2 ^ r)))
        exact hmult.symm.trans hred
      by_cases hr0 : r = 0
      · subst r
        have hm' : m = u k := by simpa using hr
        rw [hm'] at hcong
        have hcon : 1 ≡ 1 + 1 * 3 ^ k [MOD 3 ^ (k + 1)] := by
          simpa using (hcong.symm.trans hstrong)
        exact not_one_add_mod_three_pow k 1 hk0 (by norm_num) (by norm_num) hcon
      · have hge2 : u k ≤ r := by
          by_contra hlt2
          have h0 : 0 < r := by omega
          exact (ihk r h0 (by omega : r < u k)) hcongr
        rcases Nat.exists_eq_add_of_le hge2 with ⟨s, hs⟩
        have hslt : s < u k := by
          rw [hs] at hrlt
          omega
        have hcongs : 2 ^ s ≡ 1 [MOD 3 ^ k] := by
          have h2s : 2 ^ r ≡ 2 ^ s [MOD 3 ^ k] := by
            rw [hs]
            rw [show 2 ^ (u k + s) = 2 ^ (u k) * 2 ^ s from by rw [pow_add]]
            simpa using (Nat.ModEq.mul (pow_u_mod_modEq k hk0) (Nat.ModEq.refl (2 ^ s)))
          exact h2s.symm.trans hcongr
        have hs0 : s = 0 := by
          by_contra hs0'
          have h0 : 0 < s := by omega
          exact (ihk s h0 hslt) hcongs
        subst s
        have hm2 : m = 2 * u k := by omega
        rw [hm2] at hcong
        have hsq : 2 ^ (2 * u k) ≡ 1 + 2 * 3 ^ k [MOD 3 ^ (k + 1)] := by
          have hsq1 : 2 ^ (2 * u k) ≡ (1 + 3 ^ k) ^ 2 [MOD 3 ^ (k + 1)] := by
            rw [show 2 * u k = u k * 2 by omega]
            rw [pow_mul]
            exact Nat.ModEq.pow 2 hstrong
          have hsq2 : (1 + 3 ^ k) ^ 2 ≡ 1 + 2 * 3 ^ k [MOD 3 ^ (k + 1)] := by
            have hbin : (1 + 3 ^ k) ^ 2 = 1 + 2 * 3 ^ k + (3 ^ k) ^ 2 := by ring
            rw [hbin]
            have hsq : (3 ^ k) ^ 2 = 3 ^ (2 * k) := by
              rw [← pow_mul]
              congr 1
              omega
            rw [hsq]
            have h3 : 3 ^ (2 * k) ≡ 0 [MOD 3 ^ (k + 1)] := by
              rw [Nat.ModEq]
              rw [Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 3 (by omega : k + 1 ≤ 2 * k))]
              simp
            have hsum : (1 + 2 * 3 ^ k) + 3 ^ (2 * k) ≡ (1 + 2 * 3 ^ k) + 0 [MOD 3 ^ (k + 1)] :=
              Nat.ModEq.add (Nat.ModEq.refl (1 + 2 * 3 ^ k)) h3
            simpa using hsum
          exact hsq1.trans hsq2
        have hcon : 1 ≡ 1 + 2 * 3 ^ k [MOD 3 ^ (k + 1)] := hcong.symm.trans hsq
        exact not_one_add_mod_three_pow k 2 hk0 (by norm_num) (by norm_num) hcon
    · have hk0' : k = 0 := by omega
      subst hk0'
      have hu1 : u 1 = 2 := by norm_num [u]
      have hlt2 : m < 2 := by simpa [hu1] using hlt
      have hm1 : m = 1 := by omega
      rw [hm1] at hcong
      rw [Nat.ModEq] at hcong
      norm_num at hcong

/-- Block-injectivity: `a ↦ 2^a mod 3^k` is injective on the block `[0, u k)`. -/
theorem pow_mod_injective (k : ℕ) (hk : k ≥ 1) :
    ∀ a b : ℕ, a < u k → b < u k → 2 ^ a ≡ 2 ^ b [MOD 3 ^ k] → a = b := by
  intro a b ha hb h
  by_contra hab
  by_cases hlt : a < b
  · have hmpos : 0 < a + (u k - b) := by
      have hb1 : 1 ≤ u k - b := by omega
      omega
    have hmlt : a + (u k - b) < u k := by omega
    have hmul : 2 ^ a * 2 ^ (u k - b) ≡ 2 ^ b * 2 ^ (u k - b) [MOD 3 ^ k] :=
      Nat.ModEq.mul h (Nat.ModEq.refl (2 ^ (u k - b)))
    have hcongm : 2 ^ (a + (u k - b)) ≡ 1 [MOD 3 ^ k] := by
      have h1 : 2 ^ a * 2 ^ (u k - b) = 2 ^ (a + (u k - b)) := by rw [pow_add]
      rw [h1] at hmul
      have h2 : 2 ^ b * 2 ^ (u k - b) ≡ 1 [MOD 3 ^ k] := by
        have hb' : b + (u k - b) = u k := by omega
        rw [show 2 ^ b * 2 ^ (u k - b) = 2 ^ (b + (u k - b)) by rw [pow_add]]
        rw [hb']
        exact pow_u_mod_modEq k hk
      exact hmul.trans h2
    exact (not_pow_mod_period k hk (a + (u k - b)) hmpos hmlt) hcongm
  · have hba2 : b < a := by omega
    have hmpos : 0 < b + (u k - a) := by
      have ha1 : 1 ≤ u k - a := by omega
      omega
    have hmlt : b + (u k - a) < u k := by omega
    have hmul : 2 ^ b * 2 ^ (u k - a) ≡ 2 ^ a * 2 ^ (u k - a) [MOD 3 ^ k] :=
      Nat.ModEq.mul h.symm (Nat.ModEq.refl (2 ^ (u k - a)))
    have hcongm : 2 ^ (b + (u k - a)) ≡ 1 [MOD 3 ^ k] := by
      have h1 : 2 ^ b * 2 ^ (u k - a) = 2 ^ (b + (u k - a)) := by rw [pow_add]
      rw [h1] at hmul
      have h2 : 2 ^ a * 2 ^ (u k - a) ≡ 1 [MOD 3 ^ k] := by
        have ha' : a + (u k - a) = u k := by omega
        rw [show 2 ^ a * 2 ^ (u k - a) = 2 ^ (a + (u k - a)) by rw [pow_add]]
        rw [ha']
        exact pow_u_mod_modEq k hk
      exact hmul.trans h2
    exact (not_pow_mod_period k hk (b + (u k - a)) hmpos hmlt) hcongm

/-- The order of `2` modulo `3^k` is exactly `u k = 2·3^(k-1)`. -/
theorem pow_one_mod_order (k : ℕ) (hk : k ≥ 1) :
    orderOf (2 : ZMod (3 ^ k)) = u k := by
  have hu1 : 0 < u k := by unfold u; positivity
  have hdvd : orderOf (2 : ZMod (3 ^ k)) ∣ u k := by
    rw [orderOf_dvd_iff_pow_eq_one]
    simpa using (ZMod.natCast_eq_natCast_iff (2 ^ u k) 1 (3 ^ k)).mpr (pow_u_mod_modEq k hk)
  have hopos : 0 < orderOf (2 : ZMod (3 ^ k)) := Nat.pos_of_dvd_of_pos hdvd hu1
  have hnot : ¬ orderOf (2 : ZMod (3 ^ k)) < u k := by
    intro ho
    have hperiod : 2 ^ (orderOf (2 : ZMod (3 ^ k))) ≡ 1 [MOD 3 ^ k] := by
      rw [← ZMod.natCast_eq_natCast_iff (2 ^ (orderOf (2 : ZMod (3 ^ k)))) 1 (3 ^ k)]
      simpa using (pow_orderOf_eq_one (2 : ZMod (3 ^ k)))
    exact (not_pow_mod_period k hk (orderOf (2 : ZMod (3 ^ k))) hopos ho) hperiod
  have hle : orderOf (2 : ZMod (3 ^ k)) ≤ u k := Nat.le_of_dvd hu1 hdvd
  omega

end Task_2c_2

section Task_2c_3

open Narkiewicz
open NarkiewiczBound

/-- Periodicity of `2^n` mod `3^k` in `n mod u k`: `2^n ≡ 2^(n mod u k) (mod 3^k)`. -/
theorem two_pow_mod_period (n k : ℕ) (hk : k ≥ 1) :
    2 ^ n % 3 ^ k = 2 ^ (n % u k) % 3 ^ k := by
  have hdiv : n = (n / u k) * u k + n % u k := by
    rw [mul_comm]
    exact (Nat.div_add_mod n (u k)).symm
  have h := pow_mod_block k (n / u k) (n % u k) hk
  rw [← hdiv] at h
  exact h

/-- The number of `n ≤ x` with `n % m = r` is at most `x/m + 1`. -/
theorem count_residue_le (x r m : ℕ) :
    ((Finset.range (x + 1)).filter (fun n => n % m = r)).card ≤ x / m + 1 := by
  let A := (Finset.range (x + 1)).filter (fun n => n % m = r)
  let Q := Finset.range (x / m + 1)
  have hinj : Set.InjOn (fun n : ℕ => n / m) (↑A : Set ℕ) := by
    intro a ha b hb hab
    change a / m = b / m at hab
    have ha_mem : a ∈ A := by simpa [A] using ha
    have hb_mem : b ∈ A := by simpa [A] using hb
    have ha_div : a = (a / m) * m + a % m := by
      rw [mul_comm]
      exact (Nat.div_add_mod a m).symm
    have hb_div : b = (b / m) * m + b % m := by
      rw [mul_comm]
      exact (Nat.div_add_mod b m).symm
    have ha_r : a % m = r := (Finset.mem_filter.mp ha_mem).2
    have hb_r : b % m = r := (Finset.mem_filter.mp hb_mem).2
    rw [ha_div, hb_div, hab, ha_r, hb_r]
  have himg : ∀ a : ℕ, a ∈ A → a / m ∈ Q := by
    intro a ha
    have haA : a ∈ A := by simpa [A] using ha
    have ha_lt : a < x + 1 := Finset.mem_range.mp (Finset.mem_filter.mp haA).1
    have ha_le : a ≤ x := by omega
    have hq : a / m ≤ x / m := Nat.div_le_div_right ha_le
    exact Finset.mem_range.mpr (by omega)
  calc
    A.card ≤ Q.card := Finset.card_le_card_of_injOn (fun n : ℕ => n / m) himg hinj
    _ = x / m + 1 := by dsimp [Q]; simp

/-- `N(x)`: the number of `n ≤ x` with `2^n` in the Cantor set. -/
noncomputable def N (x : ℕ) : ℕ := by
  classical
  exact ((Finset.range (x + 1)).filter (fun n => memCantorNat (2 ^ n))).card

/-- Fiber-partition bound (Task 2c.3): `N(x) ≤ 2^k·(⌊x/uₖ⌋ + 1)`. -/
theorem narkiewicz_fiber_bound (x k : ℕ) (hk : k ≥ 1) :
    N x ≤ 2 ^ k * (x / u k + 1) := by
  classical
  let Good : Finset ℕ := (Finset.range (x + 1)).filter (fun n => memCantorNat (2 ^ n))
  let Fiber : ℕ → Finset ℕ := fun v => (Finset.range (x + 1)).filter (fun n => 2 ^ n % 3 ^ k = v)
  let Sf : Finset ℕ := (Finset.range (3 ^ k)).filter (fun v => memCantorNat v)
  have hSf_card : Sf.card ≤ 2 ^ k := by
    rw [← Set.ncard_coe_Finset]
    have hS : (↑Sf : Set ℕ) = {v : ℕ | v < 3 ^ k ∧ memCantorNat v} := by
      ext v
      constructor
      · intro hv
        exact ⟨Finset.mem_range.mp ((Finset.mem_filter.mp hv).1), (Finset.mem_filter.mp hv).2⟩
      · intro hv
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hv.1, hv.2⟩
    rw [hS]
    exact cantor_set_mod3k_card k
  have hN : N x = Good.card := by
    dsimp [Good]
    rfl
  have hGood_sub : Good ⊆ Sf.biUnion Fiber := by
    intro n hn
    have hn_range : n ∈ Finset.range (x + 1) := (Finset.mem_filter.mp hn).1
    have hn_cant : memCantorNat (2 ^ n) := (Finset.mem_filter.mp hn).2
    let v := 2 ^ n % 3 ^ k
    have hv_lt : v < 3 ^ k := by dsimp [v]; exact Nat.mod_lt _ (by positivity : 0 < 3 ^ k)
    have hv_cant : memCantorNat v := by
      dsimp [v]
      exact cantor_mod_pow (2 ^ n) k hn_cant
    refine Finset.mem_biUnion.mpr ⟨v, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hv_lt, hv_cant⟩
    · exact Finset.mem_filter.mpr ⟨hn_range, rfl⟩
  have hGood_le : Good.card ≤ (Sf.biUnion Fiber).card := Finset.card_le_card hGood_sub
  have hUnion_le : (Sf.biUnion Fiber).card ≤ ∑ v in Sf, (Fiber v).card :=
    Finset.card_biUnion_le (s := Sf) (t := Fiber)
  have hu_pos : 0 < u k := by unfold u; positivity
  have hFiber_le : ∀ v : ℕ, (Fiber v).card ≤ x / u k + 1 := by
    intro v
    by_cases hnon : (Fiber v).Nonempty
    · rcases hnon with ⟨n, hn⟩
      let r := n % u k
      have hFiber_sub : Fiber v ⊆ (Finset.range (x + 1)).filter (fun m => m % u k = r) := by
        intro m hm
        have hm_range : m ∈ Finset.range (x + 1) := (Finset.mem_filter.mp hm).1
        have hm_eq : 2 ^ m % 3 ^ k = v := (Finset.mem_filter.mp hm).2
        refine Finset.mem_filter.mpr ⟨hm_range, ?_⟩
        have hperiod_m : 2 ^ m % 3 ^ k = 2 ^ (m % u k) % 3 ^ k := two_pow_mod_period m k hk
        have hperiod_n : 2 ^ n % 3 ^ k = 2 ^ (n % u k) % 3 ^ k := two_pow_mod_period n k hk
        have hn_eq : 2 ^ n % 3 ^ k = v := (Finset.mem_filter.mp hn).2
        have hmr : 2 ^ (m % u k) % 3 ^ k = v := (hperiod_m.symm).trans hm_eq
        have hnr : 2 ^ (n % u k) % 3 ^ k = v := (hperiod_n.symm).trans hn_eq
        have hinj : m % u k = n % u k :=
          pow_mod_injective k hk (m % u k) (n % u k) (Nat.mod_lt _ hu_pos) (Nat.mod_lt _ hu_pos) (by
            change 2 ^ (m % u k) % 3 ^ k = 2 ^ (n % u k) % 3 ^ k
            rw [hmr, hnr])
        simpa [r] using hinj
      have hA : ((Finset.range (x + 1)).filter (fun m => m % u k = r)).card ≤ x / u k + 1 :=
        count_residue_le x r (u k)
      exact le_trans (Finset.card_le_card hFiber_sub) hA
    · have hcard0 : (Fiber v).card = 0 :=
        Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hnon)
      rw [hcard0]
      positivity
  have hSum_le : (∑ v in Sf, (Fiber v).card) ≤ Sf.card * (x / u k + 1) := by
    simpa using (Finset.sum_le_card_nsmul Sf (fun v => (Fiber v).card) (x / u k + 1) (by
      intro v _
      exact hFiber_le v))
  calc
    N x = Good.card := hN
    _ ≤ (Sf.biUnion Fiber).card := hGood_le
    _ ≤ ∑ v in Sf, (Fiber v).card := hUnion_le
    _ ≤ Sf.card * (x / u k + 1) := hSum_le
    _ ≤ 2 ^ k * (x / u k + 1) := by
      exact Nat.mul_le_mul_right _ hSf_card

end Task_2c_3

section Task_2c_4

/-- Discrete power bound (Task 2c.4): if `3^(k-1) ≤ x < 3^k` then `N(x) ≤ 2^(k+1)`. -/
theorem narkiewicz_discrete_bound (x k : ℕ) (hk : k ≥ 1) (_hx1 : 3 ^ (k - 1) ≤ x)
    (hx2 : x < 3 ^ k) : N x ≤ 2 ^ (k + 1) := by
  have hk' : k = (k - 1) + 1 := by omega
  have hpow : 3 ^ k = 3 * 3 ^ (k - 1) := by
    rw [hk']
    rw [pow_succ]
    exact Nat.mul_comm (3 ^ (k - 1)) 3
  have hlt : 3 ^ k < 2 * u k := by
    unfold u
    rw [hpow]
    ring_nf
    rw [Nat.mul_lt_mul_left (by positivity : 0 < 3 ^ (k - 1))]
    norm_num
  have hxlt : x < 2 * u k := lt_trans hx2 hlt
  have hdiv : x / u k ≤ 1 := by
    have hq : x / u k < 2 := Nat.div_lt_of_lt_mul (by simpa [mul_comm] using hxlt)
    omega
  have hplus : x / u k + 1 ≤ 2 := by omega
  have hfiber := narkiewicz_fiber_bound x k hk
  calc
    N x ≤ 2 ^ k * (x / u k + 1) := hfiber
    _ ≤ 2 ^ k * 2 := by exact Nat.mul_le_mul_left _ hplus
    _ = 2 ^ (k + 1) := by rw [← pow_succ]

end Task_2c_4

section Task_2c_5

/-- Real-exponent Narkiewicz bound (Task 2c.5): `N(x) ≤ 4·x^(log 2 / log 3)`. -/
theorem narkiewicz_real_bound (x : ℕ) (hx : 1 ≤ x) :
    (N x : ℝ) ≤ 4 * (x : ℝ) ^ (Real.log 2 / Real.log 3) := by
  classical
  let alpha : ℝ := Real.log 2 / Real.log 3
  have halpha : 0 < alpha := by
    dsimp [alpha]
    exact div_pos (Real.log_pos (by norm_num : 1 < (2 : ℝ))) (Real.log_pos (by norm_num : 1 < (3 : ℝ)))
  have hthree : (3 : ℝ) ^ alpha = 2 := by
    dsimp [alpha]
    rw [Real.rpow_def_of_pos (by norm_num : 0 < (3 : ℝ))]
    rw [← Real.exp_log (by norm_num : 0 < (2 : ℝ))]
    congr 1
    have hne : Real.log (3 : ℝ) ≠ 0 := by
      have : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num : 1 < (3 : ℝ))
      linarith
    field_simp [hne]
  have hgrows : ∃ k : ℕ, x < 3 ^ k := ⟨x, Nat.lt_pow_self (by norm_num : 1 < 3) x⟩
  let k : ℕ := Nat.find hgrows
  have hk_spec : x < 3 ^ k := by
    simpa [k] using (Nat.find_spec (p := fun m : ℕ => x < 3 ^ m) hgrows)
  have hk0 : 0 < k := by
    by_contra hk0'
    have hk_eq : k = 0 := by omega
    have hbad : x < 1 := by
      rw [hk_eq] at hk_spec
      have hb : x < 3 ^ 0 := hk_spec
      simpa using hb
    omega
  have hk1 : 1 ≤ k := hk0
  have hx1 : 3 ^ (k - 1) ≤ x := by
    have hnot : ¬ x < 3 ^ (k - 1) := by
      simpa [k] using (Nat.find_min (p := fun m : ℕ => x < 3 ^ m) hgrows (by omega : k - 1 < k))
    omega
  have hx2 : x < 3 ^ k := hk_spec
  have hdisc := narkiewicz_discrete_bound x k hk1 hx1 hx2
  have hdiscR : (N x : ℝ) ≤ (2 ^ (k + 1) : ℝ) := by exact_mod_cast hdisc
  have hle2 : (2 ^ (k - 1) : ℝ) ≤ (x : ℝ) ^ alpha := by
    have h3le : (3 ^ (k - 1) : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx1
    have h3nonneg : 0 ≤ (3 : ℝ) ^ (k - 1) := by positivity
    calc
      (2 ^ (k - 1) : ℝ) = (2 : ℝ) ^ ((k - 1 : ℕ) : ℝ) := by
        rw [← Real.rpow_natCast]
      _ = ((3 : ℝ) ^ alpha) ^ ((k - 1 : ℕ) : ℝ) := by rw [hthree]
      _ = (3 : ℝ) ^ (alpha * ((k - 1 : ℕ) : ℝ)) := by
        exact (Real.rpow_mul (by norm_num : 0 ≤ (3 : ℝ)) alpha ((k - 1 : ℕ) : ℝ)).symm
      _ = (3 : ℝ) ^ (((k - 1 : ℕ) : ℝ) * alpha) := by congr 1; ring
      _ = ((3 : ℝ) ^ ((k - 1 : ℕ) : ℝ)) ^ alpha := by
        exact Real.rpow_mul (by norm_num : 0 ≤ (3 : ℝ)) ((k - 1 : ℕ) : ℝ) alpha
      _ = (3 ^ (k - 1) : ℝ) ^ alpha := by
        rw [← Real.rpow_natCast]
      _ ≤ (x : ℝ) ^ alpha := by
        exact Real.rpow_le_rpow h3nonneg h3le halpha.le
  have hpow4 : (2 ^ (k + 1) : ℝ) = 4 * (2 ^ (k - 1) : ℝ) := by
    have hk2 : k + 1 = (k - 1) + 2 := by omega
    rw [hk2, pow_add]
    ring
  calc
    (N x : ℝ) ≤ (2 ^ (k + 1) : ℝ) := hdiscR
    _ = 4 * (2 ^ (k - 1) : ℝ) := hpow4
    _ ≤ 4 * (x : ℝ) ^ alpha := by
      exact mul_le_mul_of_nonneg_left hle2 (by norm_num : 0 ≤ (4 : ℝ))
    _ = 4 * (x : ℝ) ^ (Real.log 2 / Real.log 3) := by
      dsimp [alpha]

end Task_2c_5

section Task_2c_6

open Narkiewicz
open Filter

/-- The `k`-th ternary digit of `2^n` is zero when `n < k`. -/
theorem digit₃_small_pow_lt (n k : ℕ) (hk : n < k) : digit₃ (2 ^ n) k = 0 := by
  rw [digit₃]
  have hlt : 2 ^ n < 3 ^ k := by
    by_cases hn0 : n = 0
    · subst hn0
      have hk1 : k ≠ 0 := by omega
      exact one_lt_pow (by norm_num : (1 : ℕ) < 3) hk1
    · have hn1 : n ≠ 0 := hn0
      have h1 : 2 ^ n < 3 ^ n := Nat.pow_lt_pow_left (by norm_num : (2 : ℕ) < 3) hn1
      have h2 : 3 ^ n ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num : (3 : ℕ) > 0) (by omega : n ≤ k)
      exact lt_of_lt_of_le h1 h2
  rw [Nat.div_eq_of_lt hlt]

/-- `2^n` is in the Cantor set iff all of its ternary digits up to `n` are not `2`. -/
theorem cantor_iff_small_digits (n : ℕ) :
    memCantorNat (2 ^ n) ↔ ∀ k ≤ n, digit₃ (2 ^ n) k ≠ 2 := by
  constructor
  · intro h k _hk
    exact h k
  · intro h k
    by_cases hk : k ≤ n
    · exact h k hk
    · have hkn : n < k := by omega
      rw [digit₃_small_pow_lt n k hkn]
      norm_num

/-- The count of `n < m` with `2^n` in the Cantor set is at most `N (m - 1)`. -/
theorem count_le_N (m : ℕ) (hm : 1 ≤ m) :
    ((Finset.range m).filter (fun n => ∀ k ≤ n, digit₃ (2 ^ n) k ≠ 2)).card ≤ N (m - 1) := by
  classical
  change (@Finset.filter ℕ (fun n => ∀ k ≤ n, digit₃ (2 ^ n) k ≠ 2)
      (fun n => @Nat.decidableBallLE n (fun k _ => digit₃ (2 ^ n) k ≠ 2)
        (fun k _ => @instDecidableNot (digit₃ (2 ^ n) k = 2) (instDecidableEqNat (digit₃ (2 ^ n) k) 2)))
      (Finset.range m)).card ≤ N (m - 1)
  have hsub : (m - 1) + 1 = m := by omega
  have hNdef : N (m - 1) = ((Finset.range m).filter (fun n => memCantorNat (2 ^ n))).card := by
    unfold N
    rw [hsub]
  have hsubset : @Finset.filter ℕ (fun n => ∀ k ≤ n, digit₃ (2 ^ n) k ≠ 2)
      (fun n => @Nat.decidableBallLE n (fun k _ => digit₃ (2 ^ n) k ≠ 2)
        (fun k _ => @instDecidableNot (digit₃ (2 ^ n) k = 2) (instDecidableEqNat (digit₃ (2 ^ n) k) 2)))
      (Finset.range m)
      ⊆ (Finset.range m).filter (fun n => memCantorNat (2 ^ n)) := by
    intro n hn
    simp only [Finset.mem_filter] at hn
    exact Finset.mem_filter.mpr ⟨hn.1, (cantor_iff_small_digits n).mpr hn.2⟩
  have hle : (@Finset.filter ℕ (fun n => ∀ k ≤ n, digit₃ (2 ^ n) k ≠ 2)
      (fun n => @Nat.decidableBallLE n (fun k _ => digit₃ (2 ^ n) k ≠ 2)
        (fun k _ => @instDecidableNot (digit₃ (2 ^ n) k = 2) (instDecidableEqNat (digit₃ (2 ^ n) k) 2)))
      (Finset.range m)).card
      ≤ ((Finset.range m).filter (fun n => memCantorNat (2 ^ n))).card :=
    Finset.card_le_card hsubset
  calc
    (@Finset.filter ℕ (fun n => ∀ k ≤ n, digit₃ (2 ^ n) k ≠ 2)
      (fun n => @Nat.decidableBallLE n (fun k _ => digit₃ (2 ^ n) k ≠ 2)
        (fun k _ => @instDecidableNot (digit₃ (2 ^ n) k = 2) (instDecidableEqNat (digit₃ (2 ^ n) k) 2)))
      (Finset.range m)).card
        ≤ ((Finset.range m).filter (fun n => memCantorNat (2 ^ n))).card := hle
    _ = N (m - 1) := hNdef.symm

/-- Density-zero corollary (Task 2c.6): the density of `n ≤ m` with `2^n` in the Cantor set tends to `0`. -/
theorem narkiewicz_density_zero :
    ∀ ε > 0, ∃ N₀, ∀ m ≥ N₀,
      (((Finset.range m).filter (fun n => ∀ k ≤ n, digit₃ (2 ^ n) k ≠ 2)).card : ℝ) / ↑m < ε := by
  intro ε hε
  classical
  let alpha : ℝ := Real.log 2 / Real.log 3
  have halpha_pos : 0 < alpha := by
    dsimp [alpha]
    exact div_pos (Real.log_pos (by norm_num : 1 < (2 : ℝ))) (Real.log_pos (by norm_num : 1 < (3 : ℝ)))
  have halpha_lt : alpha < 1 := by
    dsimp [alpha]
    have h3pos : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num : 1 < (3 : ℝ))
    rw [div_lt_one h3pos]
    exact Real.log_lt_log (by norm_num : 0 < (2 : ℝ)) (by norm_num : (2 : ℝ) < 3)
  have hpow : Filter.Tendsto (fun x : ℝ => x ^ (alpha - 1)) atTop (nhds 0) := by
    have h := tendsto_rpow_neg_atTop (by linarith : 0 < 1 - alpha)
    rw [show alpha - 1 = -(1 - alpha) by linarith]
    exact h
  have hquad : Filter.Tendsto (fun n : ℕ => 4 * (n : ℝ) ^ (alpha - 1)) atTop (nhds 0) := by
    simpa using (hpow.comp tendsto_natCast_atTop_atTop).const_mul 4
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp (hquad.eventually (Iio_mem_nhds hε))
  refine ⟨max N₀ 2, fun m hm => ?_⟩
  have hm2 : 2 ≤ m := le_trans (Nat.le_max_right _ _) hm
  have hm1 : 1 ≤ m := by omega
  have hm0 : N₀ ≤ m := le_trans (Nat.le_max_left _ _) hm
  have hbd : 4 * (m : ℝ) ^ (alpha - 1) < ε := hN₀ m hm0
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  let cnt : Finset ℕ := @Finset.filter ℕ (fun n => ∀ k ≤ n, digit₃ (2 ^ n) k ≠ 2)
      (fun n => @Nat.decidableBallLE n (fun k _ => digit₃ (2 ^ n) k ≠ 2)
        (fun k _ => @instDecidableNot (digit₃ (2 ^ n) k = 2) (instDecidableEqNat (digit₃ (2 ^ n) k) 2)))
      (Finset.range m)
  change (cnt.card : ℝ) / (m : ℝ) < ε
  have hcnt_le : (cnt.card : ℝ) ≤ (N (m - 1) : ℝ) := by
    exact_mod_cast count_le_N m hm1
  have hratio : (N (m - 1) : ℝ) / (m : ℝ) ≤ 4 * (m : ℝ) ^ (alpha - 1) := by
    have hnb := narkiewicz_real_bound (m - 1) (by omega : 1 ≤ m - 1)
    have hcast : (N (m - 1) : ℝ) ≤ 4 * ((m - 1 : ℕ) : ℝ) ^ alpha := by
      simpa using hnb
    have hle : ((m - 1 : ℕ) : ℝ) ^ alpha ≤ (m : ℝ) ^ alpha := by
      exact Real.rpow_le_rpow (by positivity : 0 ≤ ((m - 1 : ℕ) : ℝ))
        (by exact_mod_cast (by omega : m - 1 ≤ m)) halpha_pos.le
    have hle' : (N (m - 1) : ℝ) ≤ 4 * (m : ℝ) ^ alpha := by
      calc
        (N (m - 1) : ℝ) ≤ 4 * ((m - 1 : ℕ) : ℝ) ^ alpha := hcast
        _ ≤ 4 * (m : ℝ) ^ alpha := by exact mul_le_mul_of_nonneg_left hle (by norm_num : 0 ≤ (4 : ℝ))
    have hdiv : (N (m - 1) : ℝ) / (m : ℝ) ≤ (4 * (m : ℝ) ^ alpha) / (m : ℝ) := by
      exact div_le_div_of_nonneg_right hle' (le_of_lt hmpos)
    have hrew2 : (4 * (m : ℝ) ^ alpha) / (m : ℝ) = 4 * (m : ℝ) ^ (alpha - 1) := by
      have hsub : (m : ℝ) ^ alpha / (m : ℝ) = (m : ℝ) ^ (alpha - 1) := by
        nth_rewrite 2 [← Real.rpow_one (m : ℝ)]
        exact (Real.rpow_sub (by positivity : 0 < (m : ℝ)) alpha 1).symm
      rw [mul_div_assoc, hsub]
    rwa [hrew2] at hdiv
  have hdiv2 : (cnt.card : ℝ) / (m : ℝ)
      ≤ (N (m - 1) : ℝ) / (m : ℝ) := by
    exact div_le_div_of_nonneg_right hcnt_le (le_of_lt hmpos)
  have hmid : (cnt.card : ℝ) / (m : ℝ)
      ≤ 4 * (m : ℝ) ^ (alpha - 1) := by
    calc
      (cnt.card : ℝ) / (m : ℝ)
          ≤ (N (m - 1) : ℝ) / (m : ℝ) := hdiv2
      _ ≤ 4 * (m : ℝ) ^ (alpha - 1) := hratio
  exact lt_of_le_of_lt hmid hbd

end Task_2c_6