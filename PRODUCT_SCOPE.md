# Product scope — what "Erdős Software" means

The commercial tiers are permissions over a defined thing. This file defines the
thing, so that an agreement can name it and a customer cannot argue about where
it stops.

Status: inventory only. The tiers are **not** written yet; the proposed mapping
at the end is a draft awaiting decisions listed in "Open boundary questions".

## Definition

"Erdős Software" means components C1, C2, C3, and C4 below, at the commit named
in the agreement, excluding C5 and C6.

| | Component | Path | Size | License | In scope |
| --- | --- | --- | --- | --- | --- |
| C1 | Core Lean 4 formalization | `ErdosTernary/ErdosTernary/` | 133 files, 88,996 lines | PolyForm Strict 1.0.0 | yes |
| C2 | Python tools | `ErdosTernary/*.py`, `scripts/`, `verify_middle/`, 5 at root | 118 files, 20,674 lines | PolyForm Strict 1.0.0 | yes |
| C3 | Rust tools | `verify_erdos_rs/`, `verify_middle/` | 10 files, 2,073 lines, 2 crates | PolyForm Strict 1.0.0 | yes |
| C4 | Certificates and datasets | `verify_middle/*.csv`, `ErdosTernary/nk*.txt`, JSON manifests | 16 files, 11 MB | PolyForm Strict 1.0.0, to the extent copyright subsists | yes, see Q1 |
| C5 | Dependencies | see below | — | third-party | **no** |
| C6 | Papers | `paper/` | 2 manuscripts | Paper 1 CC BY 4.0, Paper 2 all rights reserved | **no** |

### C1 — Core Lean 4 formalization

Toolchain `leanprover/lean4:v4.12.0`, Mathlib pinned at
`809c3fb3b5c8`, plus `batteries`, `Qq`, `aesop`, `proofwidgets`, `Cli`,
`importGraph`, `LeanSearchClient`.

78 modules at the top level, plus `Archive_3AdicBarrier/` and
`ContinuedFraction/`.

### C2 — Python tools

Four groups, and they do different jobs:

| Group | Files | Role |
| --- | --- | --- |
| `ErdosTernary/` | 56 | certificate generation, failure analysis, searches |
| `scripts/cantor_multiplier/` | 32 | dimension scan (`verify_dimensions.py`) |
| `verify_middle/` | 25 | bridge verification drivers |
| repository root | 5 | `verify_conjecture.py`, `verify_coverage.py`, `verify_gap.py`, `verify_key_lemma.py`, `verify_large.py` |

Third-party imports: `numpy` and `sympy` (9 files), both BSD-3-Clause, both
excluded from the offer. There is no requirements file; a customer would need
one.

### C3 — Rust tools

`verify_erdos_rs` and `verify_middle`, both `publish = false`. Dependencies:
`num-bigint`, `num-traits`, `rayon`, `num-cpus`, `ctrlc`, all MIT or Apache-2.0,
all excluded from the offer.

### C4 — Certificates and datasets

The largest is `verify_middle/bridge_data_K15.csv` at 5.9 MB, followed by
`bridge_data_K12.csv` (0.7 MB) and the `nk17_*` chunk lists (0.6 MB each).

`ErdosTernary/build_errors.txt` (1.2 MB) is a build log, not an asset. It should
be removed from the repository and from the product definition.

### C5 — Dependencies, excluded

Lean 4, Mathlib, the seven Lake packages, `numpy`, `sympy`, and the five Rust
crates. None is sublicensed by this offer, and none is redistributed here. A
customer receives build instructions, not a bundle.

### C6 — Papers, separate

Paper 1 is CC BY 4.0 and published at DOI `10.5281/zenodo.24595631`. Anyone may
read, quote, and redistribute it, including commercially, and that cannot be
sold. Paper 2 is all rights reserved and unpublished.

## Out of scope, explicitly

- `ErdosTernary/attic/` — 7 archived files kept for restoration, not built.
- `.worktrees/` — untracked working copies.
- `contrib/palomar/` — separate repository, Apache-2.0.
- `contrib/formal-conjectures/` — Apache-2.0 contribution to an upstream project.
- `.lake/` — build artifacts.

## Open boundary questions

1. **Are the shipped certificates part of what a customer buys, or only the
   ability to regenerate them?** Tier 3 depends entirely on this answer.
2. **Who owns outputs a customer generates?** Proposed: outputs of the
   customer's own runs are the customer's; the shipped certificates remain
   licensed. This is the sentence Tier 3 needs, and it is the one most likely to
   be argued.
3. **Do the Python tools count as integrable software under Tier 2**, given they
   depend on `numpy` and `sympy` that the customer must supply?
4. **Is `attic/` excluded from all tiers?** Recommended: yes, unsupported and
   unwarranted.
5. **Does "specified software" in each tier mean all of C1–C4, or a named
   subset?** The tiers as drafted say "specified", which is only usable if the
   agreement enumerates the subset.

## Proposed tier mapping — draft, not in force

| | C1 Lean | C2 Python | C3 Rust | C4 Certificates |
| --- | --- | --- | --- | --- |
| Tier 1 — Research and internal use | run internally | run internally | run internally | read, not redistribute |
| Tier 2 — Integration and development | embed, modify per agreement | embed, modify per agreement | embed, modify per agreement | use internally |
| Tier 3 — Results and deployment | production use | production use | production use | deploy, plus agreed use of generated outputs |

Tiers are cumulative: Tier 3 includes Tier 1 and 2 rights unless the agreement
says otherwise.

## What has to be decided before the tiers are written

The five questions above. Until Q1 and Q2 are answered, Tier 3 cannot be written
without contradicting itself, because it would promise deployment of outputs
whose ownership the agreement has not settled.
