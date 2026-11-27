#!/usr/bin/env python3
"""
EMVE Certificate Catalog Generator (emve-cert-v1)
Generates exact mathematical certificates for all multipliers M <= 35 with gcd(M, 3) = 1.
Computes canonical SHA-256 payload digests and independently audits each output.
"""

import os
import sys
import json
import hashlib
from pathlib import Path
import numpy as np
import sympy as sp

# Add repo root and scripts to path
REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT))
sys.path.insert(0, str(REPO_ROOT / "scripts"))
sys.path.insert(0, str(REPO_ROOT / "scripts" / "cantor_multiplier"))

from scripts.cantor_multiplier.verify_dimensions import (
    get_graph_for_M,
    find_collatz_wielandt_vector,
    count_roots_strictly_greater_than_phi,
    analyse
)
from scripts.check_certificate import (
    compute_payload_sha256,
    verify_certificate_file
)

CATALOG_DIR = REPO_ROOT / "certificates" / "catalog"
CATALOG_DIR.mkdir(parents=True, exist_ok=True)

def generate_certificate_for_M(M: int):
    states, A_derived, fam, params, fwd_lag = get_graph_for_M(M)
    A_np = np.array(A_derived, dtype=int)
    n = A_np.shape[0]

    # Stated family & lag
    norm_fam = str(fam).upper().strip()
    lag_list = list(fwd_lag) if fwd_lag else None

    # Check whether extremizer or strictly less than phi
    analysis = analyse(M)
    status = analysis["status"]

    if status == "EXACT_STRICTLY_LESS_PHI":
        success, v_int = find_collatz_wielandt_vector(A_np)
        if not success:
            raise ValueError(f"Could not find Collatz-Wielandt vector for M={M}")
        
        cert = {
            "format_version": "emve-cert-v1",
            "certificate_type": "collatz_wielandt",
            "problem_id": f"erdos-cantor-multiplier:M={M}:family={norm_fam}:lag={fwd_lag}",
            "mathematical_context": {
                "problem": "Erdos 1939 Middle-Thirds Cantor Set Arithmetic Intersection",
                "multiplier_M": M,
                "family": norm_fam,
                "forward_lag": lag_list,
                "graph_type": "zero_reachable_forward_sft"
            },
            "claim": {
                "property": "spectral_radius_upper_bound",
                "inequality": "5 * sum_j A[i][j]*v[j] <= 8 * v[i] for all i",
                "spectral_bound_rational": "8/5",
                "spectral_bound_float": 1.6,
                "target_golden_ratio": "phi = (1 + sqrt(5)) / 2 approx 1.618033989",
                "conclusion": "rho(A) <= 1.60 < phi strictly"
            },
            "witness": {
                "matrix_dimensions": [n, n],
                "matrix": A_np.tolist(),
                "witness_vector": v_int
            },
            "metadata": {
                "generator": "EMVE export_catalog.py v1.0.0",
                "zenodo_doi": "10.5281/zenodo.24595631",
                "created_at_utc": "2026-11-27T21:45:00Z",
                "checksum_type": "sha256_canonical_payload_integrity"
            }
        }
        filename = f"M{M}_collatz_wielandt.json"

    elif status == "EXACT_EQUAL_PHI":
        A_sp = sp.Matrix(A_np)
        cp = A_sp.charpoly()
        X = sp.Symbol('x')
        expr = cp.as_expr().subs(cp.gen, X)
        div_phi, roots_gt_phi = count_roots_strictly_greater_than_phi(expr)
        if not div_phi or roots_gt_phi != 0:
            raise ValueError(f"Extremizer M={M} failed: div_phi={div_phi}, roots_gt_phi={roots_gt_phi}")

        cert = {
            "format_version": "emve-cert-v1",
            "certificate_type": "sturm_root_count",
            "problem_id": f"erdos-cantor-multiplier:M={M}:family={norm_fam}:lag={fwd_lag}",
            "mathematical_context": {
                "problem": "Erdos 1939 Middle-Thirds Cantor Set Arithmetic Intersection",
                "multiplier_M": M,
                "family": norm_fam,
                "forward_lag": lag_list,
                "graph_type": "zero_reachable_forward_sft"
            },
            "claim": {
                "property": "exact_spectral_radius_equality",
                "target_field": "Q(sqrt(5))",
                "target_root": "phi = (1 + sqrt(5)) / 2",
                "polynomial_factor": "x^2 - x - 1",
                "exact_roots_strictly_greater_than_phi": 0,
                "conclusion": "rho(A) == phi exactly"
            },
            "witness": {
                "matrix_dimensions": [n, n],
                "matrix": A_np.tolist()
            },
            "metadata": {
                "generator": "EMVE export_catalog.py v1.0.0",
                "zenodo_doi": "10.5281/zenodo.24595631",
                "created_at_utc": "2026-11-27T21:45:00Z",
                "checksum_type": "sha256_canonical_payload_integrity"
            }
        }
        filename = f"M{M}_sturm_extremizer.json"
    else:
        raise ValueError(f"Unknown status {status} for M={M}")

    # Compute SHA-256 payload digest
    cert["payload_sha256"] = compute_payload_sha256(cert)
    
    out_path = CATALOG_DIR / filename
    with open(out_path, "w", encoding="utf-8") as f:
        json.dump(cert, f, indent=2)
    
    return filename, cert

def build_catalog(limit: int = 35):
    print(f"Building EMVE Certificate Catalog for 2 <= M <= {limit}, gcd(M, 3) = 1...")
    candidates = [M for M in range(2, limit + 1) if M % 3 != 0]
    
    index_entries = []
    audits_passed = 0

    for M in candidates:
        fname, cert = generate_certificate_for_M(M)
        filepath = CATALOG_DIR / fname
        
        # Verify immediately with auditor
        passed, msg, report = verify_certificate_file(str(filepath), check_derivation=True)
        if not passed:
            print(f"FAILED verification for {fname}: {msg}")
            sys.exit(1)
        
        audits_passed += 1
        entry = {
            "multiplier_M": M,
            "filename": fname,
            "certificate_type": cert["certificate_type"],
            "states": cert["witness"]["matrix_dimensions"][0],
            "conclusion": cert["claim"]["conclusion"],
            "payload_sha256": cert["payload_sha256"],
            "audit_status": "PASS"
        }
        index_entries.append(entry)
        print(f"  [PASS] M = {M:2d} -> {fname} ({cert['certificate_type']}, {entry['states']} states, SHA-256: {cert['payload_sha256'][:8]}...)")

    # Write catalog_index.json
    index_path = CATALOG_DIR / "catalog_index.json"
    catalog_summary = {
        "catalog_version": "emve-catalog-v1.0.0",
        "format_version": "emve-cert-v1",
        "total_certificates": len(index_entries),
        "audited_and_verified": audits_passed,
        "zenodo_doi": "10.5281/zenodo.24595631",
        "certificates": index_entries
    }
    with open(index_path, "w", encoding="utf-8") as f:
        json.dump(catalog_summary, f, indent=2)

    print(f"\nSuccessfully generated and audited {audits_passed}/{len(candidates)} certificates in {CATALOG_DIR}.")
    return catalog_summary

if __name__ == "__main__":
    build_catalog(35)
