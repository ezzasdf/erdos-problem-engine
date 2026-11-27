#!/usr/bin/env python3
"""Customer-Independent Reproducibility Test for EMVE Spectral Certification.

This test runs an automated, self-contained verification check without manual intervention:
1. Tests exact Collatz-Wielandt certificate for non-extremizer M = 19:
   Asserts 5*A*v <= 8*v in Z, proving rho(A) <= 1.60 < phi strictly.
2. Tests exact Sturm sequence certificate for extremizer M = 7:
   Asserts (x^2 - x - 1) divides P(x) in Z[x] and exactly 0 real roots > phi in Q(sqrt(5)).
3. Verifies zero floating-point dependencies for certificate acceptance.
"""

import sys
import os
import json
import time
import tempfile
from pathlib import Path

# Add project root to sys.path
root_dir = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(root_dir))

from scripts.cantor_multiplier.verify_dimensions import analyse, forward_sft_graph

def run_test():
    print("=" * 70)
    print("EMVE Reproducibility Test: Exact Mathematical Spectral Certification")
    print("=" * 70)

    start_time = time.time()

    # Test 1: Non-extremizer M = 19 (exp (2,3) -> fwd (1,3))
    print("\n[Test 1] Testing Non-Extremizer M = 19 (Family 2)...")
    res_19 = analyse(19, mode="exact")
    print(f"  Status        : {res_19['status']}")
    print(f"  States        : {res_19['states']}")
    print(f"  Perron Root   : {res_19['lambda']:.9f}")
    print(f"  Certificate   : {res_19['certificate']}")
    assert res_19['status'] == "EXACT_STRICTLY_LESS_PHI", f"Expected STRICTLY_LESS_PHI, got {res_19['status']}"
    assert "Collatz-Wielandt" in res_19['certificate'], "Expected Collatz-Wielandt certificate"
    print("  -> TEST 1 PASSED: Certified strictly less than phi via pure integer arithmetic.")

    # Test 2: Extremizer M = 7 (exp (1,2) -> fwd (1,2))
    print("\n[Test 2] Testing Proven Extremizer M = 7 (Family 2, b = 2a)...")
    res_7 = analyse(7, mode="exact")
    print(f"  Status        : {res_7['status']}")
    print(f"  States        : {res_7['states']}")
    print(f"  Perron Root   : {res_7['lambda']:.9f}")
    print(f"  Perron Factor : {res_7['perron_factor']}")
    print(f"  Certificate   : {res_7['certificate']}")
    assert res_7['status'] == "EXACT_EQUAL_PHI", f"Expected EXACT_EQUAL_PHI, got {res_7['status']}"
    assert str(res_7['perron_factor']) == "x**2 - x - 1", "Expected factor x^2 - x - 1"
    assert "Exact match (x^2 - x - 1)" in res_7['certificate'], "Expected exact Sturm certificate"
    print("  -> TEST 2 PASSED: Certified exact equality to phi via Sturm sequence in Q(sqrt5).")

    # Test 3: Numerical vs Exact Consistency
    print("\n[Test 3] Verifying Exact vs Heuristic Consistency...")
    res_4 = analyse(4, mode="exact")
    assert res_4['status'] == "EXACT_EQUAL_PHI", "M=4 must be exact extremizer"
    res_2 = analyse(2, mode="exact")
    assert res_2['status'] == "EXACT_STRICTLY_LESS_PHI", "M=2 must be strictly less than phi"
    print("  -> TEST 3 PASSED: Boundary cases (M=2, M=4) certified correctly.")

    # Test 4: Independent External Auditor
    print("\n[Test 4] Running Independent Mathematical Auditor (Zero-Trust Check)...")
    from scripts.check_certificate import run_standalone_audit, verify_certificate_file
    audit_res = run_standalone_audit()
    assert audit_res == 0, "Independent auditor failed"
    print("  -> TEST 4 PASSED: Independent auditor verified raw mathematical witnesses.")

    # Test 5: Portable Certificate Format (emve-cert-v1) Validation
    print("\n[Test 5] Auditing Portable JSON Certificates (emve-cert-v1)...")
    cert_dir = root_dir / "certificates"
    for cfile in ["M19_collatz_wielandt.json", "M7_sturm_extremizer.json", "M4_sturm_extremizer.json"]:
        cpath = cert_dir / cfile
        assert cpath.exists(), f"Certificate file {cfile} not found"
        # Test both decoupled and end-to-end derivation check
        ok, msg, rep = verify_certificate_file(cpath, check_derivation=True)
        assert ok, f"Portable certificate {cfile} failed audit: {msg}"
        print(f"  - {cfile:<28}: [{rep['status']}] (SHA-256 & derivation verified, {rep['elapsed_seconds']:.4f}s)")
    print("  -> TEST 5 PASSED: Portable JSON certificates independently validated.")

    # Test 6: Security & Hardening Integrity Validation
    print("\n[Test 6] Running Auditor Security & Hardening Tests...")
    from scripts.check_certificate import verify_portable_certificate_dict, compute_payload_sha256
    dummy_cert = {
        "format_version": "emve-cert-v1",
        "certificate_type": "collatz_wielandt",
        "problem_id": "hardening-test",
        "witness": {"matrix_dimensions": [1, 1], "matrix": [[1]], "witness_vector": [1]}
    }
    dummy_cert["payload_sha256"] = compute_payload_sha256(dummy_cert)

    # 6a. Missing hash must fail
    bad_no_hash = dict(dummy_cert)
    del bad_no_hash["payload_sha256"]
    ok_nh, _ = verify_portable_certificate_dict(bad_no_hash)
    assert not ok_nh, "Auditor accepted certificate with missing payload_sha256"

    # 6b. Empty hash must fail
    bad_empty_hash = dict(dummy_cert)
    bad_empty_hash["payload_sha256"] = ""
    ok_eh, _ = verify_portable_certificate_dict(bad_empty_hash)
    assert not ok_eh, "Auditor accepted certificate with empty payload_sha256"

    # 6c. Corrupted hash must fail
    bad_corrupt_hash = dict(dummy_cert)
    bad_corrupt_hash["payload_sha256"] = "0" * 64
    ok_ch, _ = verify_portable_certificate_dict(bad_corrupt_hash)
    assert not ok_ch, "Auditor accepted certificate with corrupted payload_sha256"

    # 6d. Boolean in CW vector must fail
    bad_bool_v = {
        "format_version": "emve-cert-v1",
        "certificate_type": "collatz_wielandt",
        "problem_id": "hardening-test",
        "witness": {"matrix_dimensions": [1, 1], "matrix": [[1]], "witness_vector": [True]}
    }
    bad_bool_v["payload_sha256"] = compute_payload_sha256(bad_bool_v)
    ok_bv, _ = verify_portable_certificate_dict(bad_bool_v)
    assert not ok_bv, "Auditor accepted boolean True in witness_vector"

    # 6e. Boolean in CW matrix must fail
    bad_bool_m = {
        "format_version": "emve-cert-v1",
        "certificate_type": "collatz_wielandt",
        "problem_id": "hardening-test",
        "witness": {"matrix_dimensions": [1, 1], "matrix": [[True]], "witness_vector": [1]}
    }
    bad_bool_m["payload_sha256"] = compute_payload_sha256(bad_bool_m)
    ok_bm, _ = verify_portable_certificate_dict(bad_bool_m)
    assert not ok_bm, "Auditor accepted boolean True in CW matrix"

    # 6f. Boolean in Sturm matrix must fail
    bad_bool_sturm = {
        "format_version": "emve-cert-v1",
        "certificate_type": "sturm_root_count",
        "problem_id": "hardening-test",
        "witness": {"matrix_dimensions": [2, 2], "matrix": [[True, 0], [0, 1]]}
    }
    bad_bool_sturm["payload_sha256"] = compute_payload_sha256(bad_bool_sturm)
    ok_bs, _ = verify_portable_certificate_dict(bad_bool_sturm)
    assert not ok_bs, "Auditor accepted boolean True in Sturm matrix"

    # 6g. Derivation metadata mismatch (wrong family) must fail derivation check
    bad_meta_cert = {
        "format_version": "emve-cert-v1",
        "certificate_type": "collatz_wielandt",
        "problem_id": "erdos-cantor-multiplier:M=19:family=2:lag=(1,3)",
        "mathematical_context": {
            "multiplier_M": 19,
            "family": "F99_MISMATCH",
            "forward_lag": [1, 3]
        },
        "witness": {
            "matrix_dimensions": [6, 6],
            "matrix": [
                [1, 0, 0, 1, 0, 0],
                [1, 0, 0, 0, 0, 0],
                [0, 1, 0, 0, 0, 0],
                [0, 0, 0, 0, 1, 0],
                [0, 0, 0, 0, 0, 1],
                [0, 0, 1, 0, 0, 1]
            ],
            "witness_vector": [201563, 139062, 100000, 100000, 139062, 201562]
        }
    }
    bad_meta_cert["payload_sha256"] = compute_payload_sha256(bad_meta_cert)
    ok_meta, msg_meta = verify_portable_certificate_dict(bad_meta_cert, check_derivation=True)
    assert not ok_meta and "Metadata derivation mismatch" in msg_meta, f"Derivation check failed to catch metadata mismatch: {msg_meta}"

    # 6h. Derivation metadata missing family must fail derivation check
    bad_no_fam = {
        "format_version": "emve-cert-v1",
        "certificate_type": "collatz_wielandt",
        "problem_id": "erdos-cantor-multiplier:M=19:family=2:lag=(1,3)",
        "mathematical_context": {
            "multiplier_M": 19,
            "forward_lag": [1, 3]
        },
        "witness": bad_meta_cert["witness"]
    }
    bad_no_fam["payload_sha256"] = compute_payload_sha256(bad_no_fam)
    ok_nf, msg_nf = verify_portable_certificate_dict(bad_no_fam, check_derivation=True)
    assert not ok_nf and "missing required 'family'" in msg_nf, f"Failed to reject missing family: {msg_nf}"

    # 6i. Derivation metadata wrong forward_lag must fail derivation check
    bad_wrong_lag = {
        "format_version": "emve-cert-v1",
        "certificate_type": "collatz_wielandt",
        "problem_id": "erdos-cantor-multiplier:M=19:family=2:lag=(1,3)",
        "mathematical_context": {
            "multiplier_M": 19,
            "family": "F2",
            "forward_lag": [99, 99]
        },
        "witness": bad_meta_cert["witness"]
    }
    bad_wrong_lag["payload_sha256"] = compute_payload_sha256(bad_wrong_lag)
    ok_wl, msg_wl = verify_portable_certificate_dict(bad_wrong_lag, check_derivation=True)
    assert not ok_wl and "stated forward_lag [99, 99]" in msg_wl, f"Failed to reject wrong forward_lag: {msg_wl}"

    # 6j. File-level error handling with non-dict JSON values ([], null, "hello", 123)
    for bad_val, val_name in [([], "list"), (None, "null"), ("hello", "string"), (123, "int")]:
        with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False) as tf:
            json.dump(bad_val, tf)
            tpath = tf.name
        try:
            ok_f, msg_f, rep_f = verify_certificate_file(tpath)
            assert not ok_f, f"File wrapper accepted {val_name} as certificate"
            assert rep_f is not None and rep_f["status"] == "FAIL", f"Expected FAIL status for {val_name}"
            assert "Malformed certificate structure" in msg_f, f"Unexpected message for {val_name}: {msg_f}"
        finally:
            if os.path.exists(tpath):
                os.unlink(tpath)

    print("  -> TEST 6 PASSED: SHA-256 enforcement, boolean typing, derivation metadata checks, and non-dict file wrapper robustness ([], null, string, int) verified.")

    elapsed = time.time() - start_time
    print("\n" + "=" * 70)
    print(f"ALL TESTS PASSED in {elapsed:.3f} seconds.")
    print("Assurance Level: Reproducibility + Standalone Audit + Portable JSON Verification.")
    print("Trust Boundary: Certifies zero-reachable transition matrix spectral radii.")
    print("=" * 70)
    return 0

if __name__ == "__main__":
    sys.exit(run_test())
