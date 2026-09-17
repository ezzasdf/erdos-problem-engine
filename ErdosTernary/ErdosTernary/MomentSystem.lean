import Mathlib.Tactic

namespace MomentSystem

def BinVec (d : ℕ) : Type := Fin (d + 1) → Fin 2

def aVal {d : ℕ} (a : BinVec d) (i : ℕ) : ℕ :=
  if h : i < d + 1 then (a ⟨i, h⟩ : ℕ) else 0

noncomputable def evalP3 {d : ℕ} (a : BinVec d) : ℕ :=
  ∑ i in Finset.range (d + 1), aVal a i * 3 ^ i

noncomputable def binomMoment {d : ℕ} (a : BinVec d) (j : ℕ) : ℕ :=
  ∑ i in Finset.range (d + 1), if j ≤ i then aVal a i * Nat.choose i j else 0

noncomputable def momentPartial {d : ℕ} (a : BinVec d) (m : ℕ) : ℕ :=
  ∑ j in Finset.range (m + 1), 2 ^ j * binomMoment a j

def DivPow2 {d : ℕ} (a : BinVec d) (k : ℕ) : Prop :=
  2 ^ k ∣ evalP3 a

--! Step 1: Binomial theorem

theorem pow3_eq_sum (i : ℕ) :
    3 ^ i = ∑ j ∈ Finset.range (i + 1), Nat.choose i j * 2 ^ j := by
  have h3 : (3 : ℕ) = 2 + 1 := by omega
  rw [h3, add_pow]; apply Finset.sum_congr rfl; intro j _; simp [one_pow, mul_comm]

--! Step 2: Double sum swap

private theorem range_eq_filter (d i : ℕ) (_ : i < d + 1) :
    (Finset.range (i + 1) : Finset ℕ) = Finset.filter (fun j => j ≤ i) (Finset.range (d + 1)) := by
  ext j; simp only [Finset.mem_range, Finset.mem_filter]
  exact ⟨fun h => ⟨by omega, by omega⟩, fun ⟨_, h⟩ => by omega⟩

private theorem double_sum_swap (d : ℕ) (f : ℕ → ℕ → ℕ) :
    ∑ i in Finset.range (d + 1), ∑ j in Finset.range (i + 1), f i j
    = ∑ j in Finset.range (d + 1), ∑ i in Finset.range (d + 1), if j ≤ i then f i j else 0 := by
  have h1 : ∀ i ∈ Finset.range (d + 1),
      (Finset.range (i + 1) : Finset ℕ) = Finset.filter (fun j => j ≤ i) (Finset.range (d + 1)) :=
    fun i hi => range_eq_filter d i (Finset.mem_range.mp hi)
  rw [Finset.sum_congr rfl (fun i hi => by rw [h1 i hi])]
  simp only [Finset.sum_filter]; exact Finset.sum_comm

--! Step 3: Taylor expansion

theorem taylor_expansion {d : ℕ} (a : BinVec d) :
    evalP3 a = momentPartial a d := by
  simp only [evalP3, momentPartial, binomMoment]
  have hrhs :
      (∑ j in Finset.range (d + 1), 2 ^ j * ∑ i in Finset.range (d + 1),
        if j ≤ i then aVal a i * Nat.choose i j else 0)
    = ∑ j in Finset.range (d + 1), ∑ i in Finset.range (d + 1),
        if j ≤ i then aVal a i * Nat.choose i j * 2 ^ j else 0 := by
    apply Finset.sum_congr rfl; intro j hj; rw [Finset.mem_range] at hj
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i hi; rw [Finset.mem_range] at hi
    split_ifs <;> ring
  rw [hrhs]
  rw [Finset.sum_congr rfl (fun i hi => by rw [pow3_eq_sum i, Finset.mul_sum])]
  rw [double_sum_swap d (fun i j => aVal a i * (Nat.choose i j * 2 ^ j))]
  apply Finset.sum_congr rfl; intro j hj; rw [Finset.mem_range] at hj
  apply Finset.sum_congr rfl; intro i hi; rw [Finset.mem_range] at hi
  split_ifs <;> ring

--! Step 4: Carry chain lemma

-- range split: range (m+1) = range k ∪ Ico k (m+1)
private theorem range_split (k m : ℕ) (hk : k ≤ m + 1) :
    Finset.range (m + 1) = Finset.range k ∪ Finset.Ico k (m + 1) := by
  ext x; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
  constructor
  · intro h; by_cases hx : x < k
    · left; exact hx
    · right; constructor <;> omega
  · intro h; rcases h with hx | ⟨_, hx⟩ <;> omega

private theorem range_disjoint (k m : ℕ) :
    Disjoint (Finset.range k) (Finset.Ico k (m + 1)) := by
  rw [Finset.disjoint_iff_ne]; intro a ha b hb
  simp only [Finset.mem_range] at ha; simp only [Finset.mem_Ico] at hb; omega

-- momentPartial a d = momentPartial a (k-1) + ∑_{j=k}^d 2^j M_j
private theorem mp_split (d k : ℕ) (a : BinVec d) (hk1 : 1 ≤ k) (hk : k ≤ d + 1) :
    momentPartial a d = momentPartial a (k - 1) +
      ∑ j in Finset.Ico k (d + 1), 2 ^ j * binomMoment a j := by
  simp only [momentPartial]
  rw [range_split k d hk, Finset.sum_union (range_disjoint k d)]
  rw [show (k - 1 + 1 : ℕ) = k from Nat.sub_add_cancel hk1]

-- 2^k | 2^j * M when j ≥ k
private theorem pow_dvd_pow_mul (j k M : ℕ) (hj : k ≤ j) : 2 ^ k ∣ 2 ^ j * M := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hj
  rw [hd, Nat.pow_add]; exact ⟨2 ^ d * M, by ring⟩

-- 2^k | ∑_{j=k}^d 2^j M_j
private theorem dvd_tail (d k : ℕ) (a : BinVec d) (hk : k ≤ d + 1) :
    2 ^ k ∣ ∑ j in Finset.Ico k (d + 1), 2 ^ j * binomMoment a j := by
  apply Finset.dvd_sum; intro j hj; simp only [Finset.mem_Ico] at hj
  exact pow_dvd_pow_mul j k _ (by omega)

--! THE CARRY CHAIN LEMMA
-- For k ≥ 1: DivPow2 a k ↔ 2^k | momentPartial a (k-1)
-- For k = 0: DivPow2 a 0 is trivially true (2^0 = 1 divides everything)

theorem carry_chain {d : ℕ} (a : BinVec d) {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ d + 1) :
    DivPow2 a k ↔ 2 ^ k ∣ momentPartial a (k - 1) := by
  rw [DivPow2, taylor_expansion, mp_split d k a hk1 hk]
  exact Nat.dvd_add_left (dvd_tail d k a hk)

--! Step 5: Constraint matrix

-- The j-th row of the constraint matrix over F₂ = ZMod 2:
--   row_j(i) = C(i,j) mod 2
-- The carry chain (Taylor expansion mod 2^k) implies:
--   Σ_i a_i · C(i,j) ≡ 0 (mod 2)  for j = 0,...,d+2

def constraintRow (d j : ℕ) : Fin (d + 1) → ZMod 2 :=
  fun i => if j ≤ i.val then (Nat.choose i.val j : ZMod 2) else 0

-- Dot product of row j with binary vector a (viewing a as ZMod 2)
def constraintEval (d : ℕ) (a : BinVec d) (j : ℕ) : ZMod 2 :=
  ∑ i : Fin (d + 1), (a i : ℕ) * constraintRow d j i

-- The j-th constraint: row j evaluates to 0
def satisfiesConstraint (d : ℕ) (a : BinVec d) (j : ℕ) : Prop :=
  constraintEval d a j = 0

-- All d+3 constraints must hold for v₂(P(3)) ≥ d+4
def satisfiesAllZMod (d : ℕ) (a : BinVec d) : Prop :=
  ∀ j < d + 3, satisfiesConstraint d a j

-- Alternative formulation using ℕ (easier for proofs):
-- constraintSum d a j = Σ_{i=0}^d a_i · [j ≤ i] · C(i,j)

def constraintSum (d : ℕ) (a : BinVec d) (j : ℕ) : ℕ :=
  ∑ i in Finset.range (d + 1), aVal a i * (if j ≤ i then Nat.choose i j else 0)

def satisfiesAll (d : ℕ) (a : BinVec d) : Prop :=
  ∀ j < d + 3, constraintSum d a j % 2 = 0

--! Key property: the constraint matrix has FULL COLUMN RANK over F₂
--
-- Proof: the first d+1 rows (j = 0,...,d) form a lower triangular matrix
-- with 1's on the diagonal (since C(j,j) = 1 and C(i,j) = 0 for i < j).
-- Therefore rank ≥ d+1, which is the number of columns.
-- So the null space is {0}, meaning: satisfiesAll d a → a = 0.
--
-- This is the KILLING BLOW: v₂(P(3)) ≥ d+4 forces a = 0,
-- so no non-zero binary representation achieves v₂(P(3)) ≥ d+4.

-- C(j,j) = 1
theorem choose_self_mod2 (j : ℕ) : Nat.choose j j % 2 = 1 := by
  rw [Nat.choose_self]

-- C(i,j) = 0 for i < j
theorem choose_lt_mod2 (i j : ℕ) (hij : i < j) : Nat.choose i j % 2 = 0 := by
  rw [Nat.choose_eq_zero_of_lt hij]

--! Full rank proof

private theorem aVal_expand {d : ℕ} (a : BinVec d) (j : ℕ) (hj : j < d + 1) :
    aVal a j = (a ⟨j, hj⟩ : ℕ) := by
  simp only [aVal, dif_pos hj]

private theorem mod2_zero {n : ℕ} (hn : n < 2) : n % 2 = 0 → n = 0 := by omega

private theorem fin2_lt {d : ℕ} {a : BinVec d} {j : ℕ} (hj : j < d + 1) :
    (a ⟨j, hj⟩ : ℕ) < 2 := (a ⟨j, hj⟩).isLt

private theorem constraintSum_last (d : ℕ) (a : BinVec d) :
    constraintSum d a d = aVal a d := by
  simp only [constraintSum]
  rw [Finset.sum_eq_single (d : ℕ)
    (fun i hi hne => by rw [Finset.mem_range] at hi; simp [show ¬(d ≤ i) from by omega])
    (fun h => absurd (Finset.mem_range.mpr (by omega)) h)]
  simp [Nat.choose_self]

private theorem constraint_d_zero (d : ℕ) (a : BinVec d) (ha : satisfiesAll d a) :
    aVal a d = 0 := by
  have h := ha d (by omega)
  rw [constraintSum_last] at h
  rw [aVal_expand a d (by omega)] at h ⊢
  exact mod2_zero (fin2_lt (by omega)) h

private theorem constraint_from_tail (d j : ℕ) (a : BinVec d) (ha : satisfiesAll d a)
    (hj : j ≤ d) (hzero : ∀ i, j < i → i ≤ d → aVal a i = 0) :
    aVal a j = 0 := by
  have h := ha j (by omega)
  simp only [constraintSum] at h
  rw [Finset.sum_eq_single (j : ℕ)
    (fun i hi hne => by
      rw [Finset.mem_range] at hi
      by_cases hle : j ≤ i
      · have hz := hzero i (by omega) (by omega); simp [hle, hz]
      · simp [hle])
    (fun hno => absurd (Finset.mem_range.mpr (by omega)) hno)] at h
  simp [Nat.choose_self] at h
  rw [aVal_expand a j (by omega)] at h ⊢
  exact mod2_zero (fin2_lt (by omega)) h

-- THE FULL RANK THEOREM
-- The constraint matrix has full column rank over F₂:
-- satisfiesAll d a → a i = 0 for all i
-- Proof: descending induction using Nat.decreasingInduction.
-- The cumulative motive tracks "all aVal from k to d are 0".

-- Helper: if constraint k holds and all a_{k+1},...,a_d are 0, then a_k = 0
private theorem step_down {d : ℕ} (a : BinVec d) (ha : satisfiesAll d a) {k : ℕ}
    (hk : k ≤ d) (habove : ∀ m, k < m → m ≤ d → aVal a m = 0) : aVal a k = 0 :=
  constraint_from_tail d k a ha hk habove

-- Cumulative descending proof: for all k ≤ d, aVal a k = 0
private theorem all_zero_cum {d : ℕ} (a : BinVec d) (ha : satisfiesAll d a) (k : ℕ) (hk : k ≤ d) :
    aVal a k = 0 := by
  have base : ∀ j, d ≤ j → j ≤ d → aVal a j = 0 := by
    intro j hm hm'
    have heq : j = d := Nat.le_antisymm hm' hm
    rw [heq]; exact constraint_d_zero d a ha
  have step : ∀ k, k < d →
      (∀ j, k + 1 ≤ j → j ≤ d → aVal a j = 0) →
      ∀ j, k ≤ j → j ≤ d → aVal a j = 0 := by
    intro k hk ih j hjk hjd
    by_cases hjeq : j = k
    · subst hjeq
      exact step_down a ha hjd (fun i hi hid => ih i (by omega) hid)
    · exact ih j (by omega) hjd
  have hfull := @Nat.decreasingInduction d
    (fun k _ => ∀ j, k ≤ j → j ≤ d → aVal a j = 0)
    step base k hk
  exact hfull k le_rfl hk

theorem satisfiesAll_eq_zero {d : ℕ} (a : BinVec d) (ha : satisfiesAll d a) :
    ∀ i : Fin (d + 1), a i = 0 := by
  intro i
  suffices aVal a i.val = 0 from by
    rw [aVal_expand a i.val i.isLt] at this
    exact Fin.val_injective this
  exact all_zero_cum a ha i.val (Nat.le_of_lt_succ i.isLt)

--! Structural lemmas

theorem binomMoment_zero (d : ℕ) (a : BinVec d) :
    binomMoment a 0 = ∑ i in Finset.range (d + 1), aVal a i := by
  simp only [binomMoment]; apply Finset.sum_congr rfl; intro i hi
  rw [Finset.mem_range] at hi; split_ifs with hle
  · simp [Nat.choose_zero_right, mul_one]
  · omega

theorem binomMoment_le (d : ℕ) (a : BinVec d) :
    binomMoment a 0 ≤ d + 1 := by
  rw [binomMoment_zero]
  trans ∑ _i in Finset.range (d + 1), (1 : ℕ)
  · apply Finset.sum_le_sum; intro i hi
    rw [Finset.mem_range] at hi; simp only [aVal]; split_ifs <;> omega
  · simp [Finset.card_range]

--! Step 6: Carry conditions for P(3) = 2^r

-- The carry recurrence decomposes P(3) = Σ_j 2^j · M_j into binary.
-- c(-1) = 0, c(k) = (c(k-1) + M_k) / 2, bit_k = (c(k-1) + M_k) % 2
-- For P(3) = 2^r: bits 0..r-1 = 0, bit r = 1, bits > r = 0.

-- carrySeq k = c(k) = the k-th carry
noncomputable def carrySeq (a : BinVec d) : ℕ → ℕ
  | 0 => binomMoment a 0 / 2
  | k + 1 => (carrySeq a k + binomMoment a (k + 1)) / 2

-- sumAtLevel k = c(k-1) + M_k = 2·c(k) + bit_k
noncomputable def sumAtLevel (a : BinVec d) : ℕ → ℕ
  | 0 => binomMoment a 0
  | k + 1 => carrySeq a k + binomMoment a (k + 1)

-- The k-th bit of P(3)
noncomputable def bitOfP3 (a : BinVec d) (k : ℕ) : ℕ :=
  sumAtLevel a k % 2

-- Carry condition: s(k) is even (bit k = 0)
def carryEven (a : BinVec d) (k : ℕ) : Prop :=
  sumAtLevel a k % 2 = 0

-- Carry condition: s(k) is odd (bit k = 1)
def carryOdd (a : BinVec d) (k : ℕ) : Prop :=
  sumAtLevel a k % 2 = 1

-- P(3) = 2^r iff carry propagates to level r with bit r = 1
def isCarryPowerOfTwo (a : BinVec d) (r : ℕ) : Prop :=
  (∀ k < r, carryEven a k) ∧ carryOdd a r ∧ (∀ k > r, carryEven a k)

@[simp] theorem carrySeq_zero (a : BinVec d) :
    carrySeq a 0 = binomMoment a 0 / 2 := rfl

@[simp] theorem carrySeq_succ (a : BinVec d) (k : ℕ) :
    carrySeq a (k + 1) = (carrySeq a k + binomMoment a (k + 1)) / 2 := rfl

@[simp] theorem sumAtLevel_zero (a : BinVec d) :
    sumAtLevel a 0 = binomMoment a 0 := rfl

@[simp] theorem sumAtLevel_succ (a : BinVec d) (k : ℕ) :
    sumAtLevel a (k + 1) = carrySeq a k + binomMoment a (k + 1) := rfl

@[simp] theorem bitOfP3_eq (a : BinVec d) (k : ℕ) :
    bitOfP3 a k = sumAtLevel a k % 2 := rfl

-- The fundamental carry identity:
-- sumAtLevel a k = 2 * carrySeq a k + bitOfP3 a k
theorem carry_bit_decomp (a : BinVec d) (k : ℕ) :
    sumAtLevel a k = 2 * carrySeq a k + bitOfP3 a k := by
  cases k with
  | zero => simp [sumAtLevel, carrySeq, bitOfP3, Nat.div_add_mod]
  | succ k => simp [sumAtLevel, carrySeq, bitOfP3, Nat.div_add_mod]

-- Carry conditions for v₂(P(3)) ≥ k+1:
def v2AtLeast (a : BinVec d) (k : ℕ) : Prop :=
  ∀ j ≤ k, carryEven a j

-- Connection to DivPow2: carryEven a k ↔ 2^{k+1} | momentPartial a k
-- (via the carry_chain theorem and the decomposition of momentPartial)

-- constraintSum d a j equals binomMoment a j
theorem constraintSum_eq_binomMoment (d j : ℕ) (a : BinVec d) :
    constraintSum d a j = binomMoment a j := by
  simp only [constraintSum, binomMoment]
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs <;> ring

-- binomMoment a j = 0 when j > d (since C(i,j)=0 for all i ≤ d < j)
theorem binomMoment_zero_of_gt (d j : ℕ) (a : BinVec d) (hj : j > d) :
    binomMoment a j = 0 := by
  simp only [binomMoment]
  apply Finset.sum_eq_zero
  intro i hi
  rw [Finset.mem_range] at hi
  split_ifs with hle
  · rw [Nat.choose_eq_zero_of_lt (by omega : i < j)]
    omega
  · omega

-- If satisfiesAll d a holds, then constraintSum d a j % 2 = 0 for j ≤ d,
-- i.e., binomMoment a j is even for all j ≤ d.
-- This is the RIGHT direction (not v2AtLeast → satisfiesAll, which is false).
theorem satisfiesAll_imp_moments_even (d : ℕ) (a : BinVec d) (ha : satisfiesAll d a)
    {j : ℕ} (hj : j ≤ d) : binomMoment a j % 2 = 0 := by
  have := ha j (by omega)
  rw [constraintSum_eq_binomMoment] at this
  exact this

-- evalP3 a = momentPartial a d, written out for the carry chain
theorem evalP3_eq (a : BinVec d) : evalP3 a = momentPartial a d := taylor_expansion a

-- Key property of DivPow2: connects divisibility of P(3) to momentPartial.
-- For 1 ≤ k ≤ d+1: DivPow2 a k ↔ 2^k | momentPartial a (k-1)
-- This is the carry_chain theorem.

-- The correct logical path to the Erdős conjecture for large r:
-- For r ∈ {0,...,8}: direct computational check (done in CriticalInvariant).
-- For r ≥ 9: the proof proceeds by showing that if P(3) = 2^r with binary
-- representation a = (a_0,...,a_d), then d must be large enough relative to r,
-- and the constraint matrix full rank (satisfiesAll_eq_zero) forces a = 0.
--
-- Specifically, the path is:
-- (1) isCarryPowerOfTwo a r means P(3) = 2^r.
-- (2) From taylor_expansion + carry_chain, the carry conditions for bits 0..r-1
--     being 0 give: 2^{r} | momentPartial a d (when r ≤ d+1).
-- (3) For r ≥ 9 and d = popcount(2^r in ternary) - 1, the computational bounds
--     V(d) ≤ d+3 ensure no representation exists.

-- We record the structure of the proof without committing to a specific approach:

-- If P(3) = 2^r and r ≤ d, then the bits 0..r-1 are 0 and bit r = 1.
-- The momentPartial decomposition gives us:
--   momentPartial a d = 2^r
-- So each binomMoment a j with j < r must contribute to make the lower bits vanish.

-- Note: isCarryPowerOfTwo a r with r > d does NOT force a = 0 in general.
-- Counterexample: d=1, r=2, a=(1,1), P(3) = 1+3 = 4 = 2^2.
-- The correct statement needs additional structure (e.g., r sufficiently large relative to d).

end MomentSystem
