#!/usr/bin/env python3
"""Standalone Independent Certificate Checker for EMVE.

This script acts as an independent mathematical auditor. It does NOT trust or run
the search heuristics that found the Collatz-Wielandt vectors or candidate factors.
Instead, it takes portable mathematical witnesses (JSON or raw data) and verifies
them from first principles:

1. Collatz-Wielandt Certificate Validator:
   Given a nonnegative integer matrix A and a positive integer vector v:
     Asserts: v[i] > 0 for all i (strictly integer, rejecting booleans)
     Asserts: 5 * sum(A[i][j] * v[j]) <= 8 * v[i] for all i
   Mathematical Guarantee:
     By Collatz-Wielandt, rho(A) <= max_i ((A @ v)_i / v_i) <= 8/5 = 1.60 < phi.
     Verified using pure Python arbitrary-precision integers (no floating point, zero external deps).

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

3. The Three-Level Verification Hierarchy:
   - Level 1 (Verified Certificate): Verifies mathematical properties of the supplied
     matrix and witness (Collatz-Wielandt inequality or Sturm golden root equality)
     independent of EMVE graph search and heuristics.
   - Level 2 (Verified Derivation): Verifies that the matrix and metadata match
     the canonical carry automaton for multiplier M (checked via `--verify-derivation`).
     NOTICE: This proves agreement with the generator code, but does not independently
     prove the generator algorithm faithfully models the continuous Cantor problem.
   - Level 3 (Full Theorem Target / Conditional Mathematical Conclusion): The full
     universal dimension bound on R is unconditional on boundary rays and proven extremizers,
     but conditional on Hypothesis (H) in the interior domain, with an analytical Frostman bridge.

4. Trust Boundaries & Integrity:
   - Integrity Checksum: The SHA-256 payload digest detects accidental bit flips,
     transmission errors, or file corruption. It does NOT prove author authenticity
     or provide non-repudiation (anyone can rehash a modified JSON). Authenticity
     must be established via signed Git tags or the published Zenodo record.
   - External Dependencies: Collatz-Wielandt has ZERO external dependencies (operates
     on stock Python 3 standard library; SymPy is NOT imported). Sturm root-counting
     lazily imports SymPy for characteristic polynomial and Sturm chain generation,
     evaluating all signs in exact Q(sqrt(5)) arithmetic.
"""

import sys
import os
import json
import hashlib
import time
import argparse
from pathlib import Path
from fractions import Fraction

CHECKER_VERSION = "EMVE Independent Certificate Auditor v1.0.0"
SUPPORTED_FORMAT_VERSIONS = {"emve-cert-v1"}

_SP = None
_X = None

def _get_sympy():
    """Lazily load SymPy only when auditing Sturm sequence certificates."""
    global _SP, _X
    if _SP is None:
        try:
            import sympy as sp
            _SP = sp
            _X = sp.Symbol("x")
        except ImportError:
            raise ImportError(
                "SymPy is required for Sturm sequence exact root-counting certificates. "
                "Install it via `pip install sympy` or audit Collatz-Wielandt certificates which require 0 external dependencies."
            )
    return _SP, _X


def is_strict_int(val):
    """Check if value is an integer and strictly not a boolean."""
    return isinstance(val, int) and not isinstance(val, bool)


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
    sp, X = _get_sympy()
    coeffs = sp.Poly(poly, X).all_coeffs()
    res = QSqrt5(0)
    for c in coeffs:
        res = res * x_val + QSqrt5(Fraction(c))
    return res


def count_sign_changes(signs):
    """Count number of sign changes in a sequence of non-zero signs."""
    non_zero = [s for s in signs if s != 0]
    return sum(1 for i in range(len(non_zero) - 1) if non_zero[i] != non_zero[i + 1])


def compute_payload_sha256(cert_dict):
    """Compute deterministic SHA-256 integrity checksum of certificate payload."""
    payload = {k: v for k, v in cert_dict.items() if k not in ("payload_sha256", "audit_receipt")}
    canonical_json = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(canonical_json.encode("utf-8")).hexdigest()


def verify_collatz_wielandt_witness(A_matrix, v_vector):
    """Independently audit a Collatz-Wielandt certificate.
    
    A_matrix: list of lists of ints
    v_vector: list of ints
    """
    n = len(A_matrix)
    if len(v_vector) != n:
        return False, f"Dimension mismatch: matrix {n}x{n} vs vector length {len(v_vector)}"
    
    # 1. Vector strictly positive integers (rejecting booleans)
    for i, vi in enumerate(v_vector):
        if not is_strict_int(vi) or vi <= 0:
            return False, f"Witness vector v[{i}] = {vi!r} is not a strictly positive integer"

    # 2. Matrix entries nonnegative integers (rejecting booleans)
    for i in range(n):
        if len(A_matrix[i]) != n:
            return False, f"Matrix row {i} length {len(A_matrix[i])} != {n}"
        for j in range(n):
            if not is_strict_int(A_matrix[i][j]) or A_matrix[i][j] < 0:
                return False, f"Matrix entry A[{i}][{j}] = {A_matrix[i][j]!r} is not a nonnegative integer"

    # 3. Check 5 * A @ v <= 8 * v in pure arbitrary-precision integers
    for i in range(n):
        row_sum = sum(A_matrix[i][j] * v_vector[j] for j in range(n))
        lhs = 5 * row_sum
        rhs = 8 * v_vector[i]
        if lhs > rhs:
            return False, f"Inequality failed at row {i}: 5*(A@v)[{i}] = {lhs} > 8*v[{i}] = {rhs}"

    return True, f"Collatz-Wielandt verified: 5*(A@v) <= 8*v holds across all {n} rows. Proves rho(A) <= 8/5 = 1.60 < phi strictly."


def verify_sturm_extremizer_witness(A_matrix):
    """Independently audit an extremizer Sturm sequence certificate.
    
    Verifies that rho(A) == phi exactly using exact polynomial arithmetic in Q(sqrt(5)).
    Requires SymPy (lazily imported).
    """
    sp, X = _get_sympy()
    n = len(A_matrix)
    for i in range(n):
        if len(A_matrix[i]) != n:
            return False, f"Matrix row {i} length {len(A_matrix[i])} != {n}"
        for j in range(n):
            if not is_strict_int(A_matrix[i][j]) or A_matrix[i][j] < 0:
                return False, f"Matrix entry A[{i}][{j}] = {A_matrix[i][j]!r} is not a nonnegative integer"

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


def verify_matrix_derivation(cert_data):
    """Verify that the matrix and contextual metadata inside the certificate match the canonical automaton for M.
    
    Level 2 Verification (Derivation Consistency):
    Confirms that the matrix and contextual metadata match EMVE's canonical zero-reachable graph generator.
    NOTICE: This verifies agreement with the generator code; it does NOT by itself prove that the generator
    faithfully models the original real-line intersection problem (Level 3 Theorem obligation).
    """
    try:
        root_dir = Path(__file__).resolve().parent.parent
        sys.path.insert(0, str(root_dir))
        from scripts.cantor_multiplier.verify_dimensions import get_graph_for_M
        import numpy as np

        m_ctx = cert_data.get("mathematical_context", {})
        M = m_ctx.get("multiplier_M")
        if M is None:
            return False, "Cannot verify derivation: missing 'multiplier_M' in mathematical_context"

        states, A_derived, fam, params, fwd_lag = get_graph_for_M(M)

        # 1. Check family (strictly required)
        cert_fam = m_ctx.get("family")
        if cert_fam is None:
            return False, f"Metadata derivation mismatch: missing required 'family' in mathematical_context for M={M}"
        norm_cert_fam = str(cert_fam).upper().replace("FAMILY", "").strip()
        norm_derived_fam = str(fam).upper().replace("FAMILY", "").strip()
        if norm_cert_fam not in (norm_derived_fam, norm_derived_fam.lstrip("F")):
            return False, f"Metadata derivation mismatch: stated family {cert_fam} != derived family {fam} for M={M}"

        # 2. Check forward_lag (strictly required)
        if "forward_lag" not in m_ctx:
            return False, f"Metadata derivation mismatch: missing required 'forward_lag' in mathematical_context for M={M}"
        cert_lag = m_ctx.get("forward_lag")
        expected_lag = list(fwd_lag) if fwd_lag else None
        if cert_lag != expected_lag:
            return False, f"Metadata derivation mismatch: stated forward_lag {cert_lag} != derived forward_lag {expected_lag} for M={M}"

        # 3. Check matrix dimensions vs states
        n_states = len(states)
        dims = cert_data.get("witness", {}).get("matrix_dimensions")
        if dims != [n_states, n_states]:
            return False, f"Metadata derivation mismatch: derived {n_states} states != certificate matrix_dimensions {dims}"

        # 4. Check matrix entries
        A_cert = np.array(cert_data["witness"]["matrix"], dtype=int)
        if not np.array_equal(A_derived, A_cert):
            return False, f"Matrix derivation mismatch: derived {A_derived.shape} matrix != certificate matrix"

        return True, f"Matrix & metadata derivation verified: canonical zero-reachable graph for M={M} (family={fam}, lag={fwd_lag}, {n_states} states) matches certificate exactly."
    except Exception as e:
        return False, f"Matrix derivation verification error: {e}"


def verify_portable_certificate_dict(cert_data, check_derivation=False):
    """Verify a portable certificate dictionary against the emve-cert-v1 specification."""
    # 1. Format version
    fmt = cert_data.get("format_version")
    if fmt not in SUPPORTED_FORMAT_VERSIONS:
        return False, f"Unsupported certificate format version: '{fmt}' (supported: {SUPPORTED_FORMAT_VERSIONS})"

    # 2. Strict SHA-256 integrity checksum check (cannot be bypassed)
    claimed_sha = cert_data.get("payload_sha256")
    if not isinstance(claimed_sha, str) or len(claimed_sha) != 64 or not all(c in "0123456789abcdefABCDEF" for c in claimed_sha):
        return False, f"Missing or invalid payload_sha256 integrity checksum: expected 64-character hex string, got {claimed_sha!r}"

    actual_sha = compute_payload_sha256(cert_data)
    if claimed_sha.lower() != actual_sha.lower():
        return False, f"SHA-256 integrity checksum mismatch: claimed {claimed_sha} != computed {actual_sha}"

    # 3. Required sections
    cert_type = cert_data.get("certificate_type")
    witness = cert_data.get("witness", {})
    matrix = witness.get("matrix")
    if not matrix or not isinstance(matrix, list):
        return False, "Missing or invalid witness matrix in certificate"

    dims = witness.get("matrix_dimensions")
    if dims != [len(matrix), len(matrix[0]) if matrix else 0]:
        return False, f"matrix_dimensions {dims} does not match actual matrix dimensions [{len(matrix)}, {len(matrix[0]) if matrix else 0}]"

    # 4. Optional end-to-end matrix derivation verification
    if check_derivation:
        d_ok, d_msg = verify_matrix_derivation(cert_data)
        if not d_ok:
            return False, d_msg

    # 5. Certificate type specific checks
    if cert_type == "collatz_wielandt":
        vector = witness.get("witness_vector")
        if not vector or not isinstance(vector, list):
            return False, "Missing or invalid witness_vector for collatz_wielandt certificate"
        ok, msg = verify_collatz_wielandt_witness(matrix, vector)
        return ok, msg

    elif cert_type == "sturm_root_count":
        ok, msg = verify_sturm_extremizer_witness(matrix)
        return ok, msg

    else:
        return False, f"Unknown certificate_type: '{cert_type}'"


def verify_certificate_file(file_path, check_derivation=False):
    """Load and audit a single portable certificate file."""
    path = Path(file_path)
    if not path.is_file():
        return False, f"File not found: {file_path}", None

    try:
        with open(path, "r", encoding="utf-8") as f:
            data = json.load(f)
    except Exception as e:
        return False, f"Failed to parse JSON: {e}", None

    start_t = time.time()
    ok, msg = verify_portable_certificate_dict(data, check_derivation=check_derivation)
    elapsed = time.time() - start_t

    report = {
        "file": str(path),
        "problem_id": data.get("problem_id", "unknown"),
        "certificate_type": data.get("certificate_type", "unknown"),
        "format_version": data.get("format_version", "unknown"),
        "payload_sha256": data.get("payload_sha256", "none"),
        "status": "PASS" if ok else "FAIL",
        "proof_summary": msg,
        "derivation_checked": check_derivation,
        "elapsed_seconds": elapsed,
        "checker_version": CHECKER_VERSION
    }
    return ok, msg, report


def create_portable_collatz_wielandt_cert(problem_id, math_context, A_matrix, v_vector, metadata=None):
    """Construct an emve-cert-v1 Collatz-Wielandt portable certificate."""
    cert = {
        "format_version": "emve-cert-v1",
        "certificate_type": "collatz_wielandt",
        "problem_id": problem_id,
        "mathematical_context": math_context,
        "claim": {
            "property": "spectral_radius_upper_bound",
            "inequality": "5 * sum_j A[i][j]*v[j] <= 8 * v[i] for all i",
            "spectral_bound_rational": "8/5",
            "spectral_bound_float": 1.6,
            "target_golden_ratio": "phi = (1 + sqrt(5)) / 2 approx 1.618033989",
            "conclusion": "rho(A) <= 1.60 < phi strictly"
        },
        "witness": {
            "matrix_dimensions": [len(A_matrix), len(A_matrix[0])],
            "matrix": A_matrix,
            "witness_vector": v_vector
        },
        "metadata": metadata or {
            "generator": "EMVE verify_dimensions.py v0.9.1",
            "zenodo_doi": "10.5281/zenodo.24595631",
            "created_at_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
            "checksum_type": "sha256_canonical_payload_integrity"
        }
    }
    cert["payload_sha256"] = compute_payload_sha256(cert)
    return cert


def create_portable_sturm_cert(problem_id, math_context, A_matrix, metadata=None):
    """Construct an emve-cert-v1 Sturm root-count portable certificate."""
    cert = {
        "format_version": "emve-cert-v1",
        "certificate_type": "sturm_root_count",
        "problem_id": problem_id,
        "mathematical_context": math_context,
        "claim": {
            "property": "exact_spectral_radius_equality",
            "target_field": "Q(sqrt(5))",
            "target_root": "phi = (1 + sqrt(5)) / 2",
            "polynomial_factor": "x^2 - x - 1",
            "exact_roots_strictly_greater_than_phi": 0,
            "conclusion": "rho(A) == phi exactly"
        },
        "witness": {
            "matrix_dimensions": [len(A_matrix), len(A_matrix[0])],
            "matrix": A_matrix
        },
        "metadata": metadata or {
            "generator": "EMVE verify_dimensions.py v0.9.1",
            "zenodo_doi": "10.5281/zenodo.24595631",
            "created_at_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
            "checksum_type": "sha256_canonical_payload_integrity"
        }
    }
    cert["payload_sha256"] = compute_payload_sha256(cert)
    return cert


def export_sample_certificates(output_dir):
    """Generate canonical portable JSON certificates for M=19, M=7, and M=4."""
    out_path = Path(output_dir)
    out_path.mkdir(parents=True, exist_ok=True)

    # 1. Non-extremizer M = 19
    A_19 = [
        [1, 0, 0, 1, 0, 0],
        [1, 0, 0, 0, 0, 0],
        [0, 1, 0, 0, 0, 0],
        [0, 0, 0, 0, 1, 0],
        [0, 0, 0, 0, 0, 1],
        [0, 0, 1, 0, 0, 1],
    ]
    v_19 = [201563, 139062, 100000, 100000, 139062, 201562]
    ctx_19 = {
        "problem": "Erdos 1939 Middle-Thirds Cantor Set Arithmetic Intersection",
        "multiplier_M": 19,
        "family": "F2",
        "forward_lag": [1, 3],
        "graph_type": "zero_reachable_forward_sft"
    }
    cert_19 = create_portable_collatz_wielandt_cert(
        "erdos-cantor-multiplier:M=19:family=2:lag=(1,3)", ctx_19, A_19, v_19
    )
    p19 = out_path / "M19_collatz_wielandt.json"
    with open(p19, "w", encoding="utf-8") as f:
        json.dump(cert_19, f, indent=2)

    # 2. Extremizer M = 7
    A_7 = [
        [1, 0, 1, 0],
        [1, 0, 0, 0],
        [0, 0, 0, 1],
        [0, 1, 0, 1],
    ]
    ctx_7 = {
        "problem": "Erdos 1939 Middle-Thirds Cantor Set Arithmetic Intersection",
        "multiplier_M": 7,
        "family": "F2",
        "forward_lag": [1, 2],
        "graph_type": "zero_reachable_forward_sft"
    }
    cert_7 = create_portable_sturm_cert(
        "erdos-cantor-multiplier:M=7:family=2:lag=(1,2)", ctx_7, A_7
    )
    p7 = out_path / "M7_sturm_extremizer.json"
    with open(p7, "w", encoding="utf-8") as f:
        json.dump(cert_7, f, indent=2)

    # 3. Extremizer M = 4
    A_4 = [
        [1, 1],
        [1, 0]
    ]
    ctx_4 = {
        "problem": "Erdos 1939 Middle-Thirds Cantor Set Arithmetic Intersection",
        "multiplier_M": 4,
        "family": "F1",
        "forward_lag": [1, 1],
        "graph_type": "zero_reachable_forward_sft"
    }
    cert_4 = create_portable_sturm_cert(
        "erdos-cantor-multiplier:M=4:family=1:carry", ctx_4, A_4
    )
    p4 = out_path / "M4_sturm_extremizer.json"
    with open(p4, "w", encoding="utf-8") as f:
        json.dump(cert_4, f, indent=2)

    return [p19, p7, p4]


def run_standalone_audit():
    print("=" * 75)
    print("EMVE Independent Mathematical Certificate Checker (Auditor)")
    print(f"Version: {CHECKER_VERSION}")
    print("Trust Boundary: Certifies spectral properties of explicit matrix A.")
    print("=" * 75)

    # Example 1: Non-extremizer M = 19 (6 states)
    A_19 = [
        [1, 0, 0, 1, 0, 0],
        [1, 0, 0, 0, 0, 0],
        [0, 1, 0, 0, 0, 0],
        [0, 0, 0, 0, 1, 0],
        [0, 0, 0, 0, 0, 1],
        [0, 0, 1, 0, 0, 1],
    ]
    v_19 = [201563, 139062, 100000, 100000, 139062, 201562]

    print("\n[Audit 1] Verifying Collatz-Wielandt witness for M = 19 (6x6 matrix)...")
    ok1, msg1 = verify_collatz_wielandt_witness(A_19, v_19)
    print(f"  Result : {'PASS' if ok1 else 'FAIL'}")
    print(f"  Proof  : {msg1}")
    assert ok1

    # Example 2: Extremizer M = 7 (4 states)
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
    print("INDEPENDENT AUDIT COMPLETE: 2/2 RAW MATHEMATICAL WITNESSES VERIFIED.")
    print("Guarantees: Strict integer validation (booleans rejected), pure Z arithmetic & Q(sqrt5).")
    print("=" * 75)
    return 0


def main():
    parser = argparse.ArgumentParser(
        description="EMVE Independent Certificate Auditor: Verify portable mathematical certificates."
    )
    parser.add_argument(
        "files", nargs="*", help="Portable certificate JSON files to audit (emve-cert-v1)"
    )
    parser.add_argument(
        "--example", action="store_true", help="Run standalone audit on built-in sample witnesses"
    )
    parser.add_argument(
        "--export-samples", metavar="DIR", help="Export canonical sample portable certificate JSONs to DIR"
    )
    parser.add_argument(
        "--verify-derivation", action="store_true", help="Also verify that matrix A matches canonical derivation from M"
    )
    args = parser.parse_args()

    if args.export_samples:
        paths = export_sample_certificates(args.export_samples)
        print(f"Exported {len(paths)} portable certificate(s) to '{args.export_samples}':")
        for p in paths:
            print(f"  - {p}")
        return 0

    if not args.files or args.example:
        return run_standalone_audit()

    # Audit files passed via CLI
    all_passed = True
    print("=" * 80)
    print("EMVE Independent Certificate Auditor: Auditing Portable Certificates")
    print(f"Checker: {CHECKER_VERSION}")
    print(f"Derivation Check: {'ENABLED (re-derives graph from M)' if args.verify_derivation else 'DISABLED (decoupled matrix-only check)'}")
    print("=" * 80)

    for fpath in args.files:
        ok, msg, report = verify_certificate_file(fpath, check_derivation=args.verify_derivation)
        status_str = "\033[92mPASS\033[0m" if ok else "\033[91mFAIL\033[0m"
        print(f"\nTarget File        : {fpath}")
        print(f"Problem ID         : {report.get('problem_id')}")
        print(f"Format Version     : {report.get('format_version')}")
        print(f"Cert Type          : {report.get('certificate_type')}")
        print(f"Integrity Checksum : {report.get('payload_sha256')}")
        print(f"Audit Status       : [{status_str}]")
        print(f"Proof Details      : {msg}")
        print(f"Execution Time     : {report.get('elapsed_seconds', 0.0):.4f}s")
        if not ok:
            all_passed = False

    print("\n" + "=" * 80)
    if all_passed:
        print(f"AUDIT SUMMARY: ALL {len(args.files)} CERTIFICATES INDEPENDENTLY AUDITED AND PASSED.")
        print("Guarantees: Strict integer typing; verified SHA-256 integrity checksum; exact spectral bound.")
        if not args.verify_derivation:
            print("Notice: Checked matrix properties. Run with --verify-derivation to re-derive matrix from M.")
        print("=" * 80)
        return 0
    else:
        print("AUDIT SUMMARY: ONE OR MORE CERTIFICATES FAILED INDEPENDENT AUDIT.")
        print("=" * 80)
        return 1


if __name__ == "__main__":
    sys.exit(main())
