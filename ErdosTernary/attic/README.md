# Attic — archived modules

These files are **not** part of the Lake build. They were moved here on 2026-11-27
during the pre-arXiv integrity pass. Nothing was deleted; each entry records what
would be required to restore it.

| File | Why it is here | To restore |
|---|---|---|
| `ErdosCleanFinal.lean` | Imports `ErdosTernary.CriticalInvariant`, which was removed in commit `4c90b63`. It asserts `theorem erdos_ternary_conjecture : memCantorNat (2^r) ↔ r = 0 ∨ r = 2 ∨ r = 8`, i.e. a complete proof of an open Erdős conjecture that was never actually completed. | Recover `CriticalInvariant.lean` from history, finish the 19 open error sites recorded in commit `7776d3d`, and only then re-enable the statement. Until then the honest statement of the reduction is `ErdosTernary.RepunitDiophantine.erdos_conjecture_iff_jointSurvivors_empty`. |
| `ErdosFinalGlue.lean` | Depends on `LargeBridge.lean`, which contains a `sorry`. | Discharge the `sorry` at `LargeBridge.lean:253` (the `K > 18` first-period bridge) and move both back. |
| `LargeBridge.lean` | One `sorry` at line 253. Outside the build, so it does not affect the audit. | Same as above. |
| `CarryAutomaton.lean` | One `sorry` at line 207 (`evalBit` expansion). Orphaned: nothing imports it. | Prove the finite sum identity by induction; the result is superseded by `RepunitCarryConnection.lean` for the `M = 4` case. |
| `OddTargetTest.lean` | Imports `ErdosTernary.OddCaseDigit2`, which does not exist. Scratch test file. | Recreate the missing module, or drop the file. |
| `RotationDecomp.lean` | Imports `ErdosTernary.ContinuedFraction`, which does not exist. Scratch file. | Recreate the missing module, or drop the file. |

## Invariant

After this move, every `.lean` file under `ErdosTernary/ErdosTernary/` either
compiles as part of `lake build` or is listed above. The library therefore has
zero `sorry` in the built target set, and `#print axioms` on any built
declaration reports at most `[propext, Classical.choice, Quot.sound]` (plus
`Lean.ofReduceBool` for `native_decide` certificates).
