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
  v.all (fun x => x > 0)

/-- Check that c * (A * v)_i <= d * v_i for all rows i, verifying matching dimensions -/
def checkInequality (c d : Nat) (Av : List Nat) (v : List Nat) : Bool :=
  Av.length == v.length &&
  (List.zipWith (fun avi vi => c * avi <= d * vi) Av v).all id

/--
Hardened Collatz–Wielandt verification predicate:
Given nonnegative square matrix A, strictly positive vector v, and positive integers c, d:
  - c > 0 and d > 0
  - n = v.length > 0
  - A has exactly n rows
  - Every row of A has length exactly n (strictly square, guards against zip truncation)
  - All v_i > 0
  - c * (A * v)_i <= d * v_i for all i
-/
def verifyCollatzWielandt (matrix : List (List Nat)) (v : List Nat) (c d : Nat) : Bool :=
  let n := v.length
  c > 0 && d > 0 && n > 0 &&
  matrix.length == n &&
  matrix.all (fun row => row.length == n) &&
  allStrictlyPositive v &&
  checkInequality c d (mulVec matrix v) v

/-! ### Certified Instance: Multiplier M = 19 (Family 2) -/

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

#eval verifyCollatzWielandt m19_matrix m19_witness 5 8

end EMVE
