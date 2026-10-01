import Mathlib.Tactic

def uK (K : Nat) : Nat := 2 * 3 ^ (K - 1)

def digit₃ (n : Nat) (k : Nat) : Nat :=
  (n / 3 ^ k) % 3

-- Check K=9,10 for s=2 (expect digit 2 at K+3)
-- Check K=9,10 for s=8 (expect digit 2 at K+2)
#eval do
  for K in [9, 10, 12] do
    let s2 := 2 + uK K
    let s8 := 8 + uK K
    let d2 := digit₃ (2 ^ s2) (K + 3)
    let d8 := digit₃ (2 ^ s8) (K + 2)
    IO.println s!"K={K}: s=2 digit at K+3={d2}, s=8 digit at K+2={d8}"

-- Also verify the digit_eq_of_modPow relation
-- ternaryDigit (2^(2+uK K)) (K+3) should equal
-- (2^(2+uK K) mod 3^(K+4)) / 3^(K+3) % 3
#eval do
  for K in [6, 7, 8, 9] do
    let s := 2 + uK K
    let j := K + 3
    let d1 := digit₃ (2 ^ s) j
    let d2 := (2 ^ s % 3 ^ (j + 1)) / 3 ^ j % 3
    IO.println s!"K={K}, s=2: direct={d1}, modPow={d2}"

-- Verify s=8
#eval do
  for K in [6, 7, 8, 9] do
    let s := 8 + uK K
    let j := K + 2
    let d1 := digit₃ (2 ^ s) j
    let d2 := (2 ^ s % 3 ^ (j + 1)) / 3 ^ j % 3
    IO.println s!"K={K}, s=8: direct={d1}, modPow={d2}"
