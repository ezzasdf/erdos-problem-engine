#!/usr/bin/env python3
"""Generate Lean proof terms for bridge theorem extended range (n=48..1000).

For each n in [48, 1000], proves that 2^n has a digit 2 in its first 30
ternary digits. Generates Lean 4 proof terms for BridgeComputeExtended.lean.
"""

import sys
import os


def ternary_digits(n):
    """Return ternary digits of n, most significant first."""
    if n == 0:
        return [0]
    digits = []
    while n > 0:
        digits.append(n % 3)
        n //= 3
    digits.reverse()
    return digits


def first_digit2_position(n, max_digits=30):
    """Find position of first digit 2 in first max_digits ternary digits of n.
    Returns (position, digits) or (None, digits) if no digit 2 found."""
    digits = ternary_digits(n)
    for i, d in enumerate(digits[:max_digits]):
        if d == 2:
            return i, digits
    return None, digits


def generate_proof_term(n):
    """Generate a Lean proof term for hasLeadingDigit2 (2^n) 30 = true."""
    val = 2 ** n
    pos, digits = first_digit2_position(val, 30)

    if pos is None:
        return None  # Should not happen for n >= 9

    # The proof is: unfold definitions, then native_decide handles the rest
    return f"""theorem check_leading_{n} : hasLeadingDigit2 (2 ^ {n}) 30 = true := by
  native_decide"""


def generate_batch_theorem(n_start, n_end):
    """Generate a single batch theorem using List.all."""
    return f"""theorem check_leading_{n_start}_to_{n_end} :
    List.all ((List.range {n_end + 1}).filter (· ≥ {n_start}))
      (fun n => hasLeadingDigit2 (2 ^ n) 30) = true := by
  native_decide"""


def main():
    n_start = 48
    n_end = 1000

    print(f"# Generating Lean proof terms for n={n_start}..{n_end}")
    print(f"# {n_end - n_start + 1} proof terms total")
    print()

    # First, verify all n have digit 2 in first 30 digits
    missing = []
    for n in range(n_start, n_end + 1):
        pos, _ = first_digit2_position(2 ** n, 30)
        if pos is None:
            missing.append(n)

    if missing:
        print(f"# WARNING: {len(missing)} values have no digit 2 in first 30 digits:")
        print(f"# {missing}")
        print(f"# Extending to 50 digits for these values...")
        # Re-check with 50 digits
        for n in missing:
            pos50, _ = first_digit2_position(2 ** n, 50)
            if pos50 is not None:
                print(f"#   n={n}: digit 2 at position {pos50} (of 50)")
            else:
                print(f"#   n={n}: NO digit 2 even in 50 digits!")
        sys.exit(1)

    print(f"# All {n_end - n_start + 1} values verified to have digit 2 in first 30 digits")
    print()

    # Generate the Lean file
    lean_code = []
    lean_code.append("/-")
    lean_code.append("  Bridge Theorem: Extended Computational Verification")
    lean_code.append("")
    lean_code.append("  Proves the first-period bridge theorem for n=48..1000.")
    lean_code.append("  For each n, verifies that 2^n has digit 2 in first 30 ternary digits.")
    lean_code.append("")
    lean_code.append("  This extends the precomputed range from N=47 to N=1000,")
    lean_code.append("  pushing the axiom split in BridgeUniform.lean from r=48 to r=1001.")
    lean_code.append("-/")
    lean_code.append("")
    lean_code.append("import Mathlib.Tactic")
    lean_code.append("import ErdosTernary.BridgeCompute")
    lean_code.append("")
    lean_code.append("open ErdosTernary.BridgeCompute")
    lean_code.append("")
    lean_code.append("namespace ErdosTernary.BridgeComputeExtended")
    lean_code.append("")

    # Try batch approach first (single native_decide for all 953 elements)
    lean_code.append("/-- Batch verification: all n in [48, 1000] have digit 2 in first 30 digits. -/")
    lean_code.append(generate_batch_theorem(n_start, n_end))
    lean_code.append("")

    lean_code.append("end ErdosTernary.BridgeComputeExtended")

    # Write the file
    output_path = "ErdosTernary/ErdosTernary/BridgeComputeExtended.lean"
    with open(output_path, 'w') as f:
        f.write('\n'.join(lean_code) + '\n')

    print(f"Written to {output_path}")
    print(f"File size: {len(lean_code)} lines")


if __name__ == "__main__":
    main()
