#!/usr/bin/env python3
"""
Analyze the carry machine to understand what it computes.

The carry machine processes subset sums of {3^0, ..., 3^(d-2)} bit-by-bit.
At each position j, it tracks which carry states are achievable.

Goal: understand the exact invariant so we can formalize it in Lean.
"""

def digit3(n, i):
    """i-th digit of n in base 3."""
    return n // (3**i) % 3

def evalBit(d, n):
    """evalBit from TwoAdicObstruction."""
    if d == 0:
        return 0
    result = 0
    for i in range(d):
        if (n >> i) & 1:
            result += 3**i
    return result

def oddTarget(d):
    """The odd target residue."""
    delta = d % 2
    k = d + 4
    val = (2**(k + delta) - 1) // 3
    return (val - 3**(d-1)) % (2**k)

# For d=25, let's understand the carry machine step by step
d = 25
k = d + 4  # = 29

# The target: oddTarget(25)
T = oddTarget(d)
print(f"d={d}, target T = {T}")
print(f"T in binary ({k} bits): {T:0{k}b}")
print(f"T in base 3: ", end="")
t_copy = T
digits = []
while t_copy > 0:
    digits.append(t_copy % 3)
    t_copy //= 3
print(''.join(str(d) for d in digits[::-1]))
print(f"Has digit 2? {any(d == 2 for d in digits)}")

# The carry machine checks: can we find a subset S ⊆ {0, ..., d-2}
# such that evalBit(d-1, m) ≡ T (mod 2^k) where m encodes S?
# i.e., sum_{i in S} 3^i ≡ T (mod 2^k)

# Since evalBit(d-1, m) < (3^(d-1)-1)/2, and 2^k = 2^29 ≈ 5.4e8,
# while max evalBit(24) = (3^24 - 1)/2 ≈ 1.4e11,
# there are many possible multiples.

# The carry machine processes the BINARY representation.
# At bit position j (0-indexed), it checks if the j-th bit of the subset sum
# can match the j-th bit of the target.

# Let's trace what the carry machine does for d=25

# tableData[25] first few entries:
tbl25 = [(1, 127), (24, 127), (20, 91), (104, 51), (2, 99), (8, 67), (68, 51), 
         (120, 3), (111, 3), (112, 3), (40, 15), (16, 3), (28, 51), (16, 15), 
         (40, 3), (112, 3), (111, 3), (120, 3), (68, 3), (8, 51), (2, 3), 
         (104, 3), (20, 3), (24, 3), (1, 1), (0, 1), (0, 1), (0, 1), (0, 1)]

M = 64  # carry state width
M1 = 128  # element index width

def carryStep(M, M1, targetParity, S, p_j, vBits):
    """One step of the carry machine."""
    newS = 0
    for ci in range(M):
        if (S >> ci) & 1:
            for vi in range(M1):
                if (vBits >> vi) & 1:
                    val = p_j + vi + ci
                    if val % 2 == targetParity:
                        new_carry = (val // 2) % M
                        newS |= (1 << new_carry)
    return newS

def carryRun(d, M, M1, j):
    """Run the carry machine for j positions."""
    S = 1  # initial: only carry 0
    for pos in range(j):
        if pos < len(tbl25):
            p_j, vBits = tbl25[pos]
        else:
            p_j, vBits = (0, 0)
        targetParity = 1 if pos % 2 == 0 else 0
        S = carryStep(M, M1, targetParity, S, p_j, vBits)
        nbits = bin(S).count('1')
        print(f"  pos={pos}: targetParity={targetParity}, p_j={p_j}, vBits={vBits:#x}, S={S:#x} ({nbits} bits set)")
    return S

print(f"\n=== Carrying machine trace for d=25 ===")
S_final = carryRun(d, M, M1, k)
print(f"\nFinal state: {S_final:#x}")
print(f"Machine dead? {S_final == 0}")

# Now let's understand the relationship between vi and 3^vi
# At position j, what does (p_j + vi + ci) represent?
# 
# The key insight: the carry machine is computing the binary addition
# of selected elements 3^vi, bit by bit.
#
# At bit position j:
#   (3^vi).testBit j = the j-th bit of 3^vi
#
# The carry machine's (p_j + vi + ci) % 2 gives a bit, and
# (p_j + vi + ci) / 2 gives the carry.
#
# This is NOT the same as adding 3^vi bit by bit!
# It seems like p_j encodes some transformation.
#
# Let me check: what is (3^vi).testBit j for specific values?

print("\n=== Checking (3^vi) mod 2 at various positions ===")
for vi in range(8):
    bits = []
    for j in range(10):
        bits.append((3**vi) >> j & 1)
    print(f"3^{vi} = {3**vi}, bits[0:10] = {''.join(str(b) for b in bits)}")

# Now let me check: does (p_j + vi) % 2 == (3^vi).testBit j?
print("\n=== Checking if p_j encodes (3^vi).testBit j ===")
for j, (p_j, vBits) in enumerate(tbl25[:5]):
    print(f"\nPosition {j}, p_j={p_j}")
    for vi in range(8):
        machine_bit = (p_j + vi) % 2
        ternary_bit = (3**vi) >> j & 1
        match = "✓" if machine_bit == ternary_bit else "✗"
        print(f"  vi={vi}: machine=(p_j+vi)%2={machine_bit}, 3^{vi} bit {j}={ternary_bit} {match}")
