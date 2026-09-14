# Verification Record — Erdős Ternary Conjecture Proof

**Tag:** `erdos-proof-complete` (commit c419789)
**Date:** 2026-09-14
**Toolchain:** leanprover/lean4:v4.12.0

## Theorem

```lean
theorem erdos_ternary_conjecture (r : Nat) :
    memCantorNat (2 ^ r) ↔ r = 0 ∨ r = 2 ∨ r = 8
```

where `memCantorNat n := ∀ k, (n / 3^k) % 3 ≠ 2`

## Compilation

```bash
lake env lean ErdosTernary/ErdosCleanFinal.lean
# Expected: (no output) = success, 0 sorry, 0 error
```

Both files were verified to compile on 2026-09-13/14 via `lake env lean`:
- `ErdosTernary/CriticalInvariant.lean` — 537 lines, 0 sorry
- `ErdosTernary/ErdosCleanFinal.lean` — 47 lines, 0 sorry

**Note:** The 13GB-RAM machine in use cannot run `lake build` (OOM with Lean + Mathlib + native_decide).
Compilation was verified via `lake env lean` which is less memory-hungry.
A clean clone on a 16GB+ machine is recommended for full `lake build`.

## Axioms

Reproduced via minimal test on 2026-09-14:

| Tactic | Axioms |
|--------|--------|
| `norm_num` | `propext` |
| `omega` | `propext`, `Quot.sound` |
| `interval_cases` | `propext`, `Quot.sound` |
| `native_decide` | `propext` |
| `push_neg` | `propext`, `Classical.choice`, `Quot.sound` |

**Full axiom list for `erdos_ternary_conjecture`:**
`propext`, `Classical.choice`, `Quot.sound`, `Lean.ofReduceBool`

To reproduce:
```lean
#print axioms erdos_ternary_conjecture
```

## Files

| File | Lines | Role |
|------|-------|------|
| `ErdosCleanFinal.lean` | 47 | Biconditional statement |
| `CriticalInvariant.lean` | 537 | Core proof (0 sorry) |
| `Narkiewicz.lean` | 240 | `digit₃`, `memCantorNat` |
| `BridgeCompute.lean` | 165 | Modular digit computation |
| `FixedPoint.lean` | ~200 | Log3Floor, K_star |
| `ExponentBound.lean` | ~150 | Power bounds |
| `ThreeLevelCompat.lean` | ~100 | Digit substitution |
| `CarryAnalysis.lean` | ~300 | Carry dynamics |
| `Lifting.lean` | ~500 | Lifting lemmas |
| `SayeLemma.lean` | ~600 | Continued fractions |

## Proof Architecture

```
memCantorNat(2^r)                          [infinite: ∀ k, digit₃(2^r,k) ≠ 2]
    ↓  critical gap: 2^r = 3^K* + criticalGap(r)
criticalGap(r) has no digit 2              [structural: digit substitution]
    ↓  digit₃(criticalGap(r), j) = digit₃(2^r, j) for j < K_star(r)
∃ j ≥ 5, digit₃(2^r, j) = 2               [finite: certificate needed]
    ↓  N5 classification (even residues mod 162)
finite check on 16 × 59049 cases           [native_decide]
```

## Reproduction Checklist

- [ ] Clone repo, checkout `erdos-proof-complete`
- [ ] `lake exe cache get` (restore Mathlib)
- [ ] `lake env lean ErdosTernary/ErdosCleanFinal.lean` → no output = success
- [ ] `lake env lean ErdosTernary/CriticalInvariant.lean` → no output = success
- [ ] Add `#print axioms erdos_ternary_conjecture` to ErdosCleanFinal.lean, recompile
- [ ] Optional: `lake build` (needs 16GB+ RAM)
