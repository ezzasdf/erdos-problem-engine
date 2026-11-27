/-
  EMVE Lean 4 Standalone Collatz–Wielandt Certificate Validator
  Format Version: emve-cert-v1
  Problem ID: erdos-cantor-multiplier:M=19:family=2:lag=(1,3)
  Zenodo DOI: 10.5281/zenodo.24595631

  Zero dependencies: Requires only Lean 4 standard library (no Mathlib needed).
  Verified by computational reflexivity (`by rfl`) in Lean's trusted kernel.
-/

namespace EMVE

/-- Scalar dot product between two integer lists -/
def dotProduct (row : List Nat) (v : List Nat) : Nat :=
  List.foldl (· + ·) 0 (List.zipWith (· * ·) row v)

/-- Matrix-vector multiplication A * v -/
def mulVec (matrix : List (List Nat)) (v : List Nat) : List Nat :=
  matrix.map (fun row => dotProduct row v)

/-- Check that all elements of witness vector v are strictly positive -/
def allStrictlyPositive (v : List Nat) : Bool :=
  v.all (fun x => x > 0)

/-- Check that c * (A * v)_i <= d * v_i for all rows i -/
def checkInequality (c d : Nat) (Av : List Nat) (v : List Nat) : Bool :=
  (List.zipWith (fun avi vi => c * avi <= d * vi) Av v).all id

/--
Complete Collatz–Wielandt verification predicate:
Given nonnegative square matrix A, strictly positive vector v, and positive integers c, d:
  c * (A * v) <= d * v  ==>  rho(A) <= d / c
-/
def verifyCollatzWielandt (matrix : List (List Nat)) (v : List Nat) (c d : Nat) : Bool :=
  let Av := mulVec matrix v
  allStrictlyPositive v &&
  matrix.length == v.length &&
  checkInequality c d Av v

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
THEOREM: The M = 19 zero-reachable transition matrix satisfies the
Collatz–Wielandt certificate with c = 5, d = 8.
By the Perron–Frobenius theorem, this establishes rho(A) <= 8/5 = 1.60 < phi.
Proof: Kernel evaluation by definitional reflexivity (zero axioms).
-/
theorem m19_spectral_bound_verified :
    verifyCollatzWielandt m19_matrix m19_witness 5 8 = true := by
  rfl

#eval verifyCollatzWielandt m19_matrix m19_witness 5 8

end EMVE
