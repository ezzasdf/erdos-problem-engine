#!/usr/bin/env python3
"""Standalone Independent Certificate Checker for EMVE.

This script acts as an independent mathematical auditor. It does NOT trust or run
the search heuristics that found the Collatz-Wielandt vectors or candidate factors.
Instead, it takes the mathematical witnesses and verifies them from first principles:

1. Collatz-Wielandt Certificate Validator:
   Given a nonnegative integer matrix A and a positive integer vector v:
     Asserts: v[i] > 0 for all i
     Asserts: 5 * sum(A[i][j] * v[j]) <= 8 * v[i] for all i
   Mathematical Guarantee:
     By Collatz-Wielandt, rho(A) <= max_i ((A @ v)_i / v_i) <= 8/5 = 1.60 < phi.
     Verified using pure Python arbitrary-precision integers (no floating point).

2. Sturm Root-Count Certificate Validator in Q(sqrt(5)):
   Given a matrix A and target root phi = (1 + sqrt(5))/2:
     - Computes exact characteristic polynomial P(x) = det(x*I - A) in Z[x].
     - Verifies exact divisibility P(x) = (x^2 - x - 1) * Q(x) in Z[x].
     - Constructs exact Sturm chain on square-free part of P(x).
     - Evaluates exact signs at phi in the quadratic field Q(sqrt(5)).
     - Evaluates exact signs at +infinity.
     - Asserts exactly 0 real roots strictly greater than phi.
   Mathematical Guarantee:
     Proves rho(A) = phi exactly, without numerical approximation.
"""

import sys
import argparse
from fractions import Fraction
import sympy as sp

X = sp.Symbol("x")


class QSqrt5:
    """Exact arithmetic in the quadratic field Q(sqrt(5)) = {a + b*sqrt(5) : a, b in Q}."""
    def __init__(self, a, b=0):
        self.a = Fraction(a)
        self.b = Fraction(b)

    def __add__(self, other):
        if not isinstance(other, QSqrt5):
            other = QSqrt5(other)
        return QSqrt5(self.a + other.a, self.b + other.b)

    def __sub__(self, other):
        if not isinstance(other, QSqrt5):
            other = QSqrt5(other)
        return QSqrt5(self.a - other.a, self.b - other.b)

    def __mul__(self, other):
        if not isinstance(other, QSqrt5):
            other = QSqrt5(other)
        return QSqrt5(
            self.a * other.a + 5 * self.b * other.b,
            self.a * other.b + self.b * other.a
        )

    def sign(self):
        """Exact sign determination in R."""
        if self.a == 0 and self.b == 0:
            return 0
        if self.a >= 0 and self.b >= 0:
            return 1
        if self.a <= 0 and self.b <= 0:
            return -1
        # Opposite signs: compare a^2 with 5*b^2
        a2 = self.a ** 2
        b2_5 = 5 * (self.b ** 2)
        if self.a > 0 and self.b < 0:
            return 1 if a2 > b2_5 else (-1 if a2 < b2_5 else 0)
        else: # self.a < 0, self.b > 0
            return 1 if b2_5 > a2 else (-1 if b2_5 < a2 else 0)


def eval_poly_qsqrt5(poly, x_val):
    """Evaluate polynomial poly in Q[x] at x_val in Q(sqrt(5)) using Horner's method."""
    coeffs = sp.Poly(poly, X).all_coeffs()
    res = QSqrt5(0)
    for c in coeffs:
        res = res * x_val + QSqrt5(Fraction(c))
    return res


def count_sign_changes(signs):
    """Count number of sign changes in a sequence of non-zero signs."""
    non_zero = [s for s in signs if s != 0]
    return sum(1 for i in range(len(non_zero) - 1) if non_zero[i] != non_zero[i + 1])


def verify_collatz_wielandt_witness(A_matrix, v_vector):
    """Independently audit a Collatz-Wielandt certificate.
    
    A_matrix: list of lists of ints
    v_vector: list of ints
    """
    n = len(A_matrix)
    if len(v_vector) != n:
        return False, f"Dimension mismatch: matrix {n}x{n} vs vector length {len(v_vector)}"
    
    # 1. Vector strictly positive
    for i, vi in enumerate(v_vector):
        if not isinstance(vi, int) or vi <= 0:
            return False, f"Witness vector v[{i}] = {vi} is not a strictly positive integer"

    # 2. Matrix entries nonnegative integers
    for i in range(n):
        for j in range(n):
            if not isinstance(A_matrix[i][j], int) or A_matrix[i][j] < 0:
                return False, f"Matrix entry A[{i}][{j}] = {A_matrix[i][j]} is not a nonnegative integer"

    # 3. Check 5 * A @ v <= 8 * v in pure arbitrary-precision integers
    for i in range(n):
        row_sum = sum(A_matrix[i][j] * v_vector[j] for j in range(n))
        lhs = 5 * row_sum
        rhs = 8 * v_vector[i]
        if lhs > rhs:
            return False, f"Inequality failed at row {i}: 5*(A@v)[{i}] = {lhs} > 8*v[{i}] = {rhs}"

    return True, f"Collatz-Wielandt verified: 5*(A@v) <= 8*v holds across all {n} rows. Proves rho(A) <= 1.60 < phi."


def verify_sturm_extremizer_witness(A_matrix):
    """Independently audit an extremizer Sturm sequence certificate.
    
    Verifies that rho(A) == phi exactly using exact polynomial arithmetic in Q(sqrt(5)).
    """
    n = len(A_matrix)
    M_sp = sp.Matrix(A_matrix)
    cp = M_sp.charpoly(X)
    P = sp.Poly(cp.as_expr(), X, domain='ZZ')

    # 1. Check exact divisibility by x^2 - x - 1
    golden_poly = sp.Poly(X**2 - X - 1, X, domain='ZZ')
    q, r = sp.div(P, golden_poly)
    if not r.is_zero:
        return False, f"Charpoly P(x) is not divisible by x^2 - x - 1 (remainder: {r})"

    # 2. Square-free part of P(x)
    P_sqf = sp.sqf_part(P)

    # 3. Sturm chain on P_sqf
    sturm_chain = sp.sturm(P_sqf)

    # 4. Evaluate signs at phi = 1/2 + 1/2*sqrt(5)
    phi_val = QSqrt5(Fraction(1, 2), Fraction(1, 2))
    signs_at_phi = [eval_poly_qsqrt5(p, phi_val).sign() for p in sturm_chain]

    # 5. Evaluate signs at +infinity (leading coefficient signs)
    signs_at_inf = [1 if sp.Poly(p, X).LC() > 0 else -1 for p in sturm_chain]

    # 6. Real roots in (phi, +infinity)
    var_phi = count_sign_changes(signs_at_phi)
    var_inf = count_sign_changes(signs_at_inf)
    roots_gt_phi = var_phi - var_inf

    if roots_gt_phi != 0:
        return False, f"Sturm check failed: found {roots_gt_phi} real roots strictly greater than phi"

    return True, f"Sturm sequence verified: (x^2 - x - 1) | P(x) with 0 real roots > phi. Proves rho(A) = phi exactly."


def run_standalone_audit():
    print("=" * 75)
    print("EMVE Independent Mathematical Certificate Checker (Auditor)")
    print("=" * 75)

    # Example 1: Non-extremizer M = 19 (6 states)
    # Zero-reachable forward SFT graph matrix for lag (1, 3)
    A_19 = [
        [1, 0, 0, 1, 0, 0],
        [1, 0, 0, 0, 0, 0],
        [0, 1, 0, 0, 0, 0],
        [0, 0, 0, 0, 1, 0],
        [0, 0, 0, 0, 0, 1],
        [0, 0, 1, 0, 0, 1],
    ]
    # Independent integer witness vector
    v_19 = [201563, 139062, 100000, 100000, 139062, 201562]

    print("\n[Audit 1] Verifying Collatz-Wielandt witness for M = 19 (6x6 matrix)...")
    ok1, msg1 = verify_collatz_wielandt_witness(A_19, v_19)
    print(f"  Result : {'PASS' if ok1 else 'FAIL'}")
    print(f"  Proof  : {msg1}")
    assert ok1

    # Example 2: Extremizer M = 7 (4 states)
    # Zero-reachable forward SFT graph matrix for lag (1, 2)
    A_7 = [
        [1, 0, 1, 0],
        [1, 0, 0, 0],
        [0, 0, 0, 1],
        [0, 1, 0, 1],
    ]
    print("\n[Audit 2] Verifying Sturm sequence witness for M = 7 (4x4 matrix)...")
    ok2, msg2 = verify_sturm_extremizer_witness(A_7)
    print(f"  Result : {'PASS' if ok2 else 'FAIL'}")
    print(f"  Proof  : {msg2}")
    assert ok2

    print("\n" + "=" * 75)
    print("INDEPENDENT AUDIT COMPLETE: 2/2 MATHEMATICAL CERTIFICATES INDEPENDENTLY VERIFIED.")
    print("No heuristic search trusted. All proofs certified via exact integer arithmetic and Q(sqrt5).")
    print("=" * 75)
    return 0


def main():
    parser = argparse.ArgumentParser(description="EMVE Independent Certificate Auditor")
    parser.add_argument("--example", action="store_true", default=True, help="Run standalone audit on representative witnesses")
    args = parser.parse_args()
    return run_standalone_audit()


if __name__ == "__main__":
    sys.exit(main())
