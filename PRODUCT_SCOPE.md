# Product scope — what "Erdős Software" means

The commercial tiers are permissions over a defined thing. This file defines the
thing, so that an agreement can name it and a customer cannot argue about where
it stops.

Status: boundary decided, tiers drafted. The tier tables below are the
permissions the agreement will grant, and Schedule A of the agreement names the
components and the commit.

## Definition

"Erdős Software" means components C1, C2, C3, and C4 below, at the commit named
in the agreement, excluding C5 and C6.

| | Component | Path | Size | License | In scope |
| --- | --- | --- | --- | --- | --- |
| C1 | Core Lean 4 formalization | `ErdosTernary/ErdosTernary/` | 133 files, 88,996 lines | PolyForm Strict 1.0.0 | yes |
| C2 | Python tools | `ErdosTernary/*.py`, `scripts/`, `verify_middle/`, 5 at root | 118 files, 20,674 lines | PolyForm Strict 1.0.0 | yes |
| C3 | Rust tools | `verify_erdos_rs/`, `verify_middle/` | 10 files, 2,073 lines, 2 crates | PolyForm Strict 1.0.0 | yes |
| C4 | Certificates and datasets | `verify_middle/*.csv`, `ErdosTernary/nk*.txt`, JSON manifests | 15 files, ~10 MB | PolyForm Strict 1.0.0, to the extent copyright subsists | yes, as reference outputs |
| C5 | Dependencies | see below | — | third-party | **no** |
| C6 | Papers | `paper/` | 2 manuscripts | Paper 1 CC BY 4.0, Paper 2 all rights reserved | **no** |

### C1 — Core Lean 4 formalization

Toolchain `leanprover/lean4:v4.12.0`, Mathlib pinned at `809c3fb3b5c8`, plus
`batteries`, `Qq`, `aesop`, `proofwidgets`, `Cli`, `importGraph`,
`LeanSearchClient`.

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

Third-party imports: `numpy` and `sympy` (9 files, all in
`scripts/cantor_multiplier/`), both BSD-3-Clause. They are excluded from the
offer and pinned in `requirements.txt`; the customer installs them. See
`INSTALL.md`.

### C3 — Rust tools

`verify_erdos_rs` and `verify_middle`, both `publish = false`. Dependencies:
`num-bigint`, `num-traits`, `rayon`, `num-cpus`, `ctrlc`, all MIT or Apache-2.0,
all excluded from the offer.

### C4 — Certificates and datasets

The largest is `verify_middle/bridge_data_K15.csv` at 5.9 MB, followed by
`bridge_data_K12.csv` (0.7 MB) and the `nk17_*` chunk lists (0.6 MB each).

These are reference outputs, not deliverables with a warranty. A customer
receives permission to use them; it does not acquire ownership of them.

The 1.2 MB build log that used to live at `ErdosTernary/build_errors.txt` was
removed from the repository. It remains in Git history and is not part of the
product.

### C5 — Dependencies, excluded

Lean 4, Mathlib, the seven Lake packages, `numpy`, `sympy`, and the five Rust
crates. None is sublicensed by this offer, and none is redistributed here. A
customer receives build instructions, not a bundle.

### C6 — Papers, separate

Paper 1 is CC BY 4.0 and published at DOI `10.5281/zenodo.24595631`. Anyone may
read, quote, and redistribute it, including commercially, and that cannot be
sold. Paper 2 is all rights reserved and unpublished.

## Out of scope, explicitly

- `ErdosTernary/attic/` — 7 archived files kept for restoration, not built, not
  covered by any tier.
- `.worktrees/` — untracked working copies.
- `contrib/palomar/` — separate repository, Apache-2.0.
- `contrib/formal-conjectures/` — Apache-2.0 contribution to an upstream
  project.
- `.lake/` — build artifacts.

## Decisions

| # | Question | Decision |
| --- | --- | --- |
| 1 | Are the shipped certificates sold? | Included as reference outputs, with permission to use them. Not transferred as owned property. |
| 2 | Who owns customer-generated outputs? | The customer owns its deliverable files and output rights, subject to the underlying intellectual property. See the rule below. |
| 3 | Do `numpy` and `sympy` block integration? | No. The tools are included; the customer supplies the dependencies. |
| 4 | Is `attic/` in scope? | Excluded from every tier. |
| 5 | What does "specified software" mean? | The exact components and commit are listed in Schedule A of the agreement. |

## Output ownership rule

This is the drafting basis for clause 10 of the agreement:

> The customer retains ownership of its input data and its own generated output
> files, subject to any third-party rights and any intellectual-property rights
> subsisting in the underlying Software or pre-existing materials.
>
> No ownership of the Software, its source code, or pre-existing certificates
> transfers to the customer by virtue of generating or receiving an output.

The rule does not claim that mathematical facts become anyone's exclusive
property, and it does not claim that every generated file is copyrightable.
Ownership of a file and ownership of the rights in what it expresses are
different things, and the agreement keeps them separate.

## Tiers

Cumulative: each tier includes the one below it. Tier 3 does **not** include
redistribution of source code; that needs its own explicit permission.

### Tier 1 — Research and internal use

For a company using the software for its own commercial research and
computational workflows.

| Permission | C1 Lean | C2 Python | C3 Rust | C4 Certificates |
| --- | --- | --- | --- | --- |
| Execute internally | yes | yes | yes | — |
| Analyse computational results | yes | yes | yes | yes |
| Produce internal research reports | yes | yes | yes | yes |
| Modify | no | no | no | no |
| Redistribute | no | no | no | no |
| Sublicense | no | no | no | no |

### Tier 2 — Integration and development

For a company embedding the software in its own systems.

| Permission | C1 Lean | C2 Python | C3 Rust | C4 Certificates |
| --- | --- | --- | --- | --- |
| Everything in Tier 1 | yes | yes | yes | yes |
| Embed in internal and production systems | yes | yes | yes | use internally |
| Modify, within the scope agreed in writing | yes | yes | yes | no |
| Distribute components inside the licensee's organization | yes | yes | yes | no |
| Distribute components to third parties | only as agreed in writing, per component | same | same | no |

### Tier 3 — Commercial results and deployment

For a company generating or verifying mathematical results in commercial
workflows.

| Permission | C1 Lean | C2 Python | C3 Rust | C4 Certificates |
| --- | --- | --- | --- | --- |
| Everything in Tier 1 and Tier 2 | yes | yes | yes | yes |
| Commercial computational runs at scale | yes | yes | yes | yes |
| Generate results and certificates | yes | yes | yes | — |
| Own and use its own generated outputs | per the output rule | per the output rule | per the output rule | — |
| Deploy to production, with support if purchased | yes | yes | yes | as reference outputs |
| Redistribute the shipped certificates | — | — | — | only as agreed in writing |
| Redistribute source code | no | no | no | no |

## What remains

The boundary and the permissions are settled. The agreement is where they become
enforceable: clause 3 selects a tier, Schedule A names the components and the
commit, and clause 10 carries the output rule. None of it has been reviewed by a
lawyer.
