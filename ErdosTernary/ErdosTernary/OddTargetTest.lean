import Mathlib.Tactic
import ErdosTernary.OddCaseDigit2

namespace OddTargetTest
open OddCaseDigit2

-- Test 1: Does `decide` work on oddTarget equality?
-- (decide uses kernel evaluation, not native code)

-- First: a trivial test that we know native_decide handles
-- (from the existing OddCaseDigit2.lean)
#check @hasDigit2Bounded

-- Test: prove hasDigit2Bounded for a known literal
example : hasDigit2Bounded 322477172 := by
  exact ⟨0, by omega, by native_decide⟩

-- Test 2: can we at least USE `native_decide` with `oddTarget` in ANY way?
-- What about: prove oddTarget 25 = 322477172?
-- (this requires kernel reduction of oddTarget 25)
-- The existing OddCaseDigit2 has hasDigit2Bounded 322477172 but never
-- proves oddTarget 25 = 322477172.

-- Test 3: What about omega on the digit3 expansion?
-- digit3 n j = 2 means n / 3^j % 3 = 2, which means
-- n = 3^j * q + r where q % 3 = 2 and r < 3^j.
-- Equivalently: 2 * 3^j ≤ n mod 3^{j+1} < 3 * 3^j

-- For omega to help, we need the mod and div to appear in a linear context.

-- Test 4: Does omega handle mod/div?
example (n : ℕ) : n % 3 = 2 → n % 3 < 3 := by
  intro h
  omega  -- this should work

example (n : ℕ) (h : n % 9 = 7) : n % 3 = 1 := by
  omega  -- should work too

-- Test 5: What about the OTHER direction?
-- We need: oddTarget d / 3^j % 3 = 2
-- This is: (oddTarget d / 3^j) % 3 = 2
-- If we knew oddTarget d = V for a known V, we could prove this.

-- Test 6: Try to prove oddTarget 25 = 322477172 using different tactics

-- First: does `native_decide` work on this equality?
-- (It might fail for the same kernel reason)

-- What if we use `norm_num`?
example : oddTarget 25 = 322477172 := by
  native_decide

end OddTargetTest
