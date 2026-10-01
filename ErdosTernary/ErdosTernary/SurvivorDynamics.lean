import ErdosTernary.BridgeCompute
import ErdosTernary.Narkiewicz

open ErdosTernary.BridgeCompute
open Narkiewicz

def qDigit (r K : Nat) : Nat := (r / uK K) % 3
def digit3 (n K : Nat) : Nat := (n / 3 ^ K) % 3

def padR (n : Nat) (s : String) : String :=
  s ++ String.mk (List.replicate (n - s.length) ' ')

def toStr (ds : List Nat) : String :=
  List.foldl (fun s d => s.push (Char.ofNat (48 + d))) "" ds

partial def toBase3 (n : Nat) : List Nat :=
  if n == 0 then [0] else go n []
where go : Nat → List Nat → List Nat
  | 0, acc => acc
  | v + 1, acc => go ((v + 1) / 3) (((v + 1) % 3) :: acc)

partial def firstDigit2Pos (r maxK : Nat) : Option Nat :=
  go 0
where go : Nat → Option Nat
  | K => if K >= maxK then none
    else if digit3 (pow2Mod r (3 ^ (K + 1))) K == 2 then some K
    else go (K + 1)

def dumpTraj (r maxK : Nat) : IO Unit := do
  IO.println s!"--- r = {r} ---"
  IO.println s!" K  | q_K        | q%3 | s_K       | digit_K | survives"
  IO.println s!"----|------------|-----|-----------|---------|--------"
  for K in List.range maxK do
    let K1 := K + 1
    let s := r % uK K1
    let q := r / uK K1
    let qd := q % 3
    let dk := digit3 (pow2Mod r (3 ^ (K + 1))) K
    let pow2r := pow2Mod r (3 ^ K1)
    let has2 := hasTrailingDigit2 pow2r K1
    let marker := if qd == 2 then " !!2!!" else ""
    IO.println s!" {padR 3 (toString K1)} | {padR 10 (toString q)} |  {qd}  | {padR 9 (toString s)} |   {dk}     | {if !has2 then "yes" else "NO"}{marker}"
  IO.println ""

#eval! do
  let n12 := computeNK 12
  let longLived := n12.filter (fun r => r != 0 && r != 2 && r != 8)
  IO.println "================================================================"
  IO.println "  KNOWN SURVIVORS: r = 0, 2, 8"
  IO.println "================================================================"
  dumpTraj 0 25
  dumpTraj 2 25
  dumpTraj 8 25
  IO.println "================================================================"
  IO.println "  CARRY DIGITS: known survivors vs long survivors"
  IO.println "================================================================"
  for r in [0, 2, 8] do
    let digits := (List.range 20).map (fun K => digit3 (pow2Mod r (3 ^ (K + 1))) K)
    IO.println s!"  r={padR 3 (toString r)}: {toStr digits}  SURVIVOR"
  IO.println ""
  for r in longLived.take 12 do
    let digits := (List.range 20).map (fun K => digit3 (pow2Mod r (3 ^ (K + 1))) K)
    let f2 := match firstDigit2Pos r 30 with | some p => s!"FAIL@K={p}" | none => "??"
    IO.println s!"  r={padR 3 (toString r)}: {toStr digits}  {f2}"
  IO.println ""
  IO.println "================================================================"
  IO.println "  HISTOGRAM: first digit-2 for N_12 non-{0,2,8}"
  let mut buckets : Array Nat := Array.mkArray 30 0
  for r in longLived do
    let f2 := match firstDigit2Pos r 40 with | some p => p | none => 29
    let f2c := if f2 < 30 then f2 else 29
    let cur := buckets.get! f2c
    buckets := buckets.set! f2c (cur + 1)
  IO.println s!"  Total: {longLived.length} values"
  for k in List.range 30 do
    let c := buckets.get! k
    if c > 0 then IO.println s!"  K={padR 3 (toString (k + 1))}: {c} fail here"
  IO.println ""
  IO.println "================================================================"
  IO.println "  TRAJECTORIES for sample long survivors"
  IO.println "================================================================"
  for r in longLived.take 3 do
    dumpTraj r 30
