#!/usr/bin/env python3
"""Generate range-check chunk proofs for BridgeCantorChunked.lean.

For K in {15, 16, 17}, generates:
1. Per-chunk theorems: rangeCheck K lo hi = true (proved by native_decide)
2. Combined theorem: checkBridgeCantorPow2 K = true
"""

CHUNK_SIZE_EXP = 13  # chunk_size = 3^CHUNK_SIZE_EXP
CHUNK_SIZE = 3 ** CHUNK_SIZE_EXP  # 1,594,323

def uK(K):
    """uK K = 2 * 3^(K-1)"""
    return 2 * (3 ** (K - 1))

def generate_lean_file():
    output = []

    output.append("/-")
    output.append("  Auto-generated range-check chunk proofs for K=15,16,17.")
    output.append("  Each chunk covers a range of size 3^13 = 1,594,323.")
    output.append("  Proved by native_decide on the range-parallel bridge check.")
    output.append("-/")
    output.append("")
    output.append("import ErdosTernary.BridgeCantorChunked")
    output.append("")
    output.append("open ErdosTernary.BridgeCantorChunked")
    output.append("")

    total_chunks = 0

    for K in [15, 16, 17]:
        period = uK(K)
        assert period % CHUNK_SIZE == 0, \
            f"CHUNK_SIZE={CHUNK_SIZE} does not divide uK {K}={period}"
        num_chunks = period // CHUNK_SIZE
        total_chunks += num_chunks

        output.append(f"-- K={K}: uK K = {period}, chunk_size = {CHUNK_SIZE}, "
                      f"num_chunks = {num_chunks}")
        output.append("")

        # Per-chunk theorems
        for i in range(num_chunks):
            lo = i * CHUNK_SIZE
            hi = (i + 1) * CHUNK_SIZE
            output.append(f"set_option maxHeartbeats 20000000 in")
            output.append(f"private theorem rc_K{K}_{i} :")
            output.append(f"    rangeCheck {K} {lo} {hi} = true := by")
            output.append(f"  native_decide")
            output.append("")

        # Combined theorem using interval_cases
        output.append(f"set_option maxHeartbeats 20000000 in")
        output.append(f"theorem checkBridgeCantorPow2_K{K} :")
        output.append(f"    checkBridgeCantorPow2 {K} = true := by")
        output.append(f"  apply checkBridgeCantorPow2_of_chunked "
                      f"{K} {CHUNK_SIZE} {num_chunks}")
        output.append(f"  · native_decide")
        output.append(f"  · intro j hj; interval_cases j")
        for i in range(num_chunks):
            output.append(f"    · exact rc_K{K}_{i}")
        output.append("")

    output.append(f" -- Total: {total_chunks} native_decide calls")

    with open("ErdosTernary/BridgeCantorChunkedProofs.lean", "w") as f:
        f.write("\n".join(output) + "\n")

    print(f"Generated BridgeCantorChunkedProofs.lean")
    for K in [15, 16, 17]:
        print(f"  K={K}: {uK(K) // CHUNK_SIZE} chunks")
    print(f"  Total: {total_chunks} native_decide calls")

if __name__ == "__main__":
    generate_lean_file()
