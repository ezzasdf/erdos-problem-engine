/-
  EMVE Lean 4 Standalone Collatz–Wielandt Certificate Validator
  Format Version: emve-cert-v1
  Problem ID: erdos-cantor-multiplier:M=19:family=2:lag=(1,3)
  Zenodo DOI: 10.5281/zenodo.24595631

  Zero dependencies: Requires only Lean 4 standard library (no Mathlib needed).
  Verified by computational reflexivity (`by rfl`) in Lean's trusted kernel.
-/

namespace EMVE

/-!
  ### Epistemic Guarantee & Trust Boundary
  
  1. WHAT IS VERIFIED IN THE LEAN KERNEL:
     The computational theorem `m19_witness_inequality_verified` proves by
     definitional reflexivity (`by rfl`) inside the trusted Lean 4 kernel that the
     concrete matrix A and strictly positive integer vector v satisfy the linear inequality:
       5 * (A * v)_i <= 8 * v_i  for all rows i ∈ {0, ..., 5}.
     The validator strictly enforces:
     - Dimension consistency: matrix is square (n x n) and vector has dimension n > 0.
     - Strict row length: every row has length exactly n, preventing silent truncation in zip operations.
     - Positivity: c > 0, d > 0, and v_i > 0 for all i.

  2. EXTERNAL MATHEMATICAL JUSTIFICATION:
     The deduction that this linear inequality implies the spectral radius upper bound
       ρ(A) <= 8/5 = 1.60 < φ = (1 + √5)/2
     rests on the classical Collatz–Wielandt / Perron–Frobenius theorem for nonnegative
     matrices. That general spectral theorem is an external mathematical justification
     and is not formalized within this single-file arithmetic validator.
-/

/-- Scalar dot product between two integer lists of equal length -/
def dotProduct (row : List Nat) (v : List Nat) : Nat :=
  List.foldl (· + ·) 0 (List.zipWith (· * ·) row v)

/-- Matrix-vector multiplication A * v -/
def mulVec (matrix : List (List Nat)) (v : List Nat) : List Nat :=
  matrix.map (fun row => dotProduct row v)

/-- Check that all elements of witness vector v are strictly positive -/
def allStrictlyPositive (v : List Nat) : Bool :=
  v.all (fun x => decide (x > 0))

/-- Check that c * (A * v)_i <= d * v_i for all rows i, verifying matching dimensions -/
def checkInequality (c d : Nat) (Av : List Nat) (v : List Nat) : Bool :=
  Av.length == v.length &&
  (List.zipWith (fun avi vi => decide (c * avi <= d * vi)) Av v).all id

/--
Hardened Collatz–Wielandt verification predicate:
Given nonnegative square matrix A, strictly positive vector v, and positive integers c, d:
  - c > 0 and d > 0 (strictly positive scaling constants)
  - n = v.length > 0 (non-empty vector)
  - A has exactly n rows
  - Every row of A has length exactly n (strictly square, guards against zip truncation)
  - All v_i > 0 (strictly positive witness vector)
  - c * (A * v)_i <= d * v_i for all i
-/
def verifyCollatzWielandt (matrix : List (List Nat)) (v : List Nat) (c d : Nat) : Bool :=
  let n := v.length
  c > 0 && d > 0 && n > 0 &&
  matrix.length == n &&
  matrix.all (fun row => row.length == n) &&
  allStrictlyPositive v &&
  checkInequality c d (mulVec matrix v) v

/-! ### Positive Test: Multiplier M = 19 (Family 2) -/

def m19_matrix : List (List Nat) :=
  [ [1, 0, 0, 1, 0, 0],
    [1, 0, 0, 0, 0, 0],
    [0, 1, 0, 0, 0, 0],
    [0, 0, 0, 0, 1, 0],
    [0, 0, 0, 0, 0, 1],
    [0, 0, 1, 0, 0, 1] ]

def m19_witness : List Nat :=
  [201563, 139062, 100000, 100000, 139062, 201562]

/--
THEOREM: The M = 19 zero-reachable transition matrix and witness vector
satisfy the hardened Collatz–Wielandt certificate predicate for c = 5, d = 8.
Proof: Evaluated by definitional reflexivity in Lean's trusted kernel (zero axioms).
-/
theorem m19_witness_inequality_verified :
    verifyCollatzWielandt m19_matrix m19_witness 5 8 = true := by
  rfl

/-! ### Negative Regression Tests: Hardening Verification -/

-- Negative Test 1: Inconsistent row lengths must be rejected (guard against zip truncation)
def malformed_rows_matrix : List (List Nat) :=
  [ [1, 0, 0],
    [0, 1] ]

theorem test_reject_inconsistent_row_lengths :
    verifyCollatzWielandt malformed_rows_matrix [1, 1] 5 8 = false := by
  rfl

-- Negative Test 2: Matrix row count not matching vector dimension must be rejected
def mismatched_dim_matrix : List (List Nat) :=
  [ [1, 0],
    [0, 1] ]

theorem test_reject_dimension_mismatch :
    verifyCollatzWielandt mismatched_dim_matrix [1, 1, 1] 5 8 = false := by
  rfl

-- Negative Test 3: Zero or non-positive witness vector entry must be rejected
def zero_entry_witness : List Nat := [1, 0]

theorem test_reject_zero_witness_entry :
    verifyCollatzWielandt [[1, 0], [0, 1]] zero_entry_witness 5 8 = false := by
  rfl

-- Negative Test 4: Non-positive scalar multiplier (c = 0 or d = 0) must be rejected
theorem test_reject_zero_scalar_c :
    verifyCollatzWielandt [[1]] [1] 0 8 = false := by
  rfl

theorem test_reject_zero_scalar_d :
    verifyCollatzWielandt [[1]] [1] 5 0 = false := by
  rfl

-- Negative Test 5: A deliberately false inequality must evaluate to false
-- Matrix = [[2, 0], [0, 2]], v = [1, 1], c = 1, d = 1: (1 * 2 <= 1 * 1 is false)
def scaling_matrix : List (List Nat) :=
  [ [2, 0],
    [0, 2] ]

theorem test_reject_false_inequality :
    verifyCollatzWielandt scaling_matrix [1, 1] 1 1 = false := by
  rfl

#eval verifyCollatzWielandt m19_matrix m19_witness 5 8

end EMVE
