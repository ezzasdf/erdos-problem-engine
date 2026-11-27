# Installation

Three toolchains: Python for the drivers, Lean for the formalization, Rust for
the two certificate verifiers. You do not need all three to run one group.

Nothing here redistributes a third-party dependency. Mathlib, the Lake
packages, `numpy`, `sympy`, and the Rust crates are fetched from their own
sources under their own licenses.

## 1. Python tools

Requires Python 3.10 or newer. Verified on 3.12.3.

```sh
python3 -m venv .venv
. .venv/bin/activate
pip install -r requirements.txt
```

Only `scripts/cantor_multiplier/` needs the two packages. The other 109 Python
files use the standard library only and will run without the step above.

Verified commands:

```sh
# Dimension scan: certify lambda_0 <= phi for every safe M <= 20.
python3 scripts/cantor_multiplier/verify_dimensions.py --scan 20
```

Prints `PASSED` with per-multiplier certificates. Raise the bound with
`--scan 500`; the full scan to 2000 takes minutes.

```sh
# Coverage of the j >= 38, K >= 26 gap.
python3 verify_coverage.py

# Bound check for the same gap; reports rows where Q(j)+18 may exceed uK(K-1).
python3 verify_gap.py
```

Both print a table and exit 0. `verify_gap.py` reporting `PROBLEMATIC` rows is
its normal output, not a failure: it is showing which (j, K) pairs need the
bound checked by hand.

Not verified here: the scripts in `ErdosTernary/*.py`. Most are development
drivers that read files produced by the Lean build and write results in place,
so they need a completed Lean build first and have no standalone entry point.

## 2. Lean formalization

Requires [elan](https://github.com/leanprover/elan). The toolchain is pinned to
`leanprover/lean4:v4.12.0` in `ErdosTernary/lean-toolchain`.

```sh
cd ErdosTernary
lake exe cache get     # Mathlib build cache, several GB
lake build
```

The build is heavy: Mathlib alone needs roughly 6 GB of disk for the cache, and
memory use during compilation of the bridge modules is high. A machine with
16 GB of RAM is comfortable; the largest modules were compiled on one with 7 GB
and heavy swap.

## 3. Rust verifiers

Two independent crates, both `publish = false`:

```sh
cd verify_erdos_rs   && cargo build --release
cd ../verify_middle  && cargo build --release
```

Their dependencies (`num-bigint`, `num-traits`, `rayon`, `num-cpus`, `ctrlc`)
are fetched by Cargo on first build, which needs network access. Not exercised
in the environment where this guide was written.

## What is not included

| Excluded | Why | How the user obtains it |
| --- | --- | --- |
| Lean 4 toolchain | third-party | `elan` |
| Mathlib and 7 Lake packages | third-party | `lake exe cache get` |
| `numpy`, `sympy` | third-party, BSD-3-Clause | `pip install -r requirements.txt` |
| Rust crates | third-party, MIT or Apache-2.0 | `cargo build` |

## Disk and time

| Step | Disk | Time |
| --- | --- | --- |
| Python environment | ~100 MB | under a minute |
| Lean cache and build | ~6 GB | 20 to 60 minutes, depending on cores |
| Rust release builds | ~300 MB | 1 to 3 minutes |
