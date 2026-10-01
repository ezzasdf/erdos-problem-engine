#!/usr/bin/env python3
"""Verify 2^(162*59049) % 3^m = 1 for m = 6..12."""
for m in range(6, 13):
    mod = 3**m
    exp = 162 * 59049
    result = pow(2, exp, mod)
    print(f"2^({exp}) % 3^{m} = {result} {'✓' if result == 1 else '✗'}")

# Also verify 2^162 % 3^m for reference
print("\nReference: 2^162 % 3^m:")
for m in range(1, 13):
    result = pow(2, 162, 3**m)
    print(f"2^162 % 3^{m} = {result}")
