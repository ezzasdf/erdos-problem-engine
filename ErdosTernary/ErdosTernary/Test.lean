/- Self-contained: test native_decide only -/

namespace Test

def ternaryAux : Nat → List Nat → List Nat
  | 0, acc => acc
  | n + 1, acc => ternaryAux ((n + 1) / 3) (((n + 1) % 3) :: acc)
termination_by n => n

def toTernary : Nat → List Nat
  | 0 => [0]
  | n => ternaryAux n []

def hasTwo : List Nat → Bool
  | [] => false
  | 0 :: ds => hasTwo ds
  | 1 :: ds => hasTwo ds
  | _ :: _ => true

-- native_decide only
example : hasTwo (toTernary (2 ^ 8)) = false := by native_decide

end Test
