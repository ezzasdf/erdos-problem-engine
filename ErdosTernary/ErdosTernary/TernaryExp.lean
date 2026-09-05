/-
  Erdős ternary expansion: base-3 representation lemma.
  Every natural number has a base-3 digit representation.
-/

namespace ErdosTernary

/- A digit in {0, 1, 2} -/
def isTernaryDigit (d : Nat) : Prop :=
  d = 0 ∨ d = 1 ∨ d = 2

/- Evaluate a list of base-3 digits as a number -/
def evalTernary : List Nat → Nat
  | [] => 0
  | d :: ds => d + 3 * evalTernary ds

/- Division algorithm: n = q * 3 + r, 0 ≤ r < 3 -/
theorem div3_decomp (n : Nat) :
    ∃ q r, n = q * 3 + r ∧ r < 3 := by
  refine ⟨n / 3, n % 3, ?_, Nat.mod_lt n (by omega)⟩
  omega

/- Every n has a ternary representation -/
theorem exists_ternary_repr (n : Nat) :
    ∃ ds : List Nat, (∀ d ∈ ds, isTernaryDigit d) ∧ evalTernary ds = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases h : n = 0
    · exact ⟨[], by simp [evalTernary, h]⟩
    · obtain ⟨q, r, h_eq, h_lt⟩ := div3_decomp n
      have hq_lt : q < n := by omega
      obtain ⟨ds, hd, hval⟩ := ih q hq_lt
      refine ⟨r :: ds, ?_, ?_⟩
      · intro d hd2
        cases hd2 with
        | head => simp [isTernaryDigit]; omega
        | tail _ h => exact hd d h
      · simp [evalTernary, h_eq, hval]
        omega

end ErdosTernary
