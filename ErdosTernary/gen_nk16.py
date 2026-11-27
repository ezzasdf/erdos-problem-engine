#!/usr/bin/env python3
# Copyright (c) 2026 Ezzeldin Ashraf Mohamed Shafey Wahba. All rights reserved.
# Released under the PolyForm Strict License 1.0.0 as described in the file LICENSE-CODE.
# Authors: Ezzeldin Ashraf Mohamed Shafey Wahba
"""Generate the NK_16 Lean definition from the computed list."""

K = 16
uK = 2 * 3**(K-1)
modulus_K = 3**K

NK = []
pow2r_modK = 1

for r in range(uK):
    temp = pow2r_modK
    has_digit2_K = False
    for i in range(K):
        if temp % 3 == 2:
            has_digit2_K = True
            break
        temp //= 3
    if not has_digit2_K:
        NK.append(r)
    pow2r_modK = (pow2r_modK * 2) % modulus_K

# Generate Lean code
with open('nk16_lean.txt', 'w') as f:
    f.write('def NK_16 : List Nat := [\n')
    for i in range(0, len(NK), 15):
        chunk = NK[i:i+15]
        line = ', '.join(str(v) for v in chunk)
        if i + 15 < len(NK):
            f.write(f'  {line},\n')
        else:
            f.write(f'  {line}\n')
    f.write(']\n')
    f.write(f'-- {len(NK)} elements\n')

print(f'Generated {len(NK)} entries')
