# Spec: Phase 7 M1 — Middle-Digit Attack: First Data Run

Date: 2026-08-16
Status: Approved (design), pending implementation
Part of: ROADMAP Phase 7 (middle-digit attack), first milestone M1

## Objective

Produce the first-ever dataset measuring the **middle third** of the ternary digits of
`2ⁿ` (positions `[L/3, 2L/3)` where `L = ⌊n·log₃2⌋ + 1`), for all `n ≤ 10⁶`, and compare
it against the leading and trailing thirds of the same length. Lagarias (2009) notes that
the middle digits are exploited by neither the real (most-significant-digit) method nor the
3-adic (least-significant-digit) method; nobody has measured them. This run also validates
the computational algorithm that the rest of Phase 7 (independence test, Lean
formalization) and Phases 8–9 (dataset, two-sided search) will build on.

## Algorithm (Approach A — streaming carry-chain doubling)

Represent `2ⁿ` in base 3, digits least-significant-first, in a growable packed digit array
(2 bits per digit). Maintain the number for the current `n`; each step doubles it via the
2-state carry automaton:

- state `c ∈ {0, 1}` (carry), start `c = 0`
- at digit `d`: new digit `(2·d + c) mod 3`, new carry `⌊(2·d + c)/3⌋ ∈ {0, 1}`
- stop as soon as carry is `0`; if a carry survives past the top digit, append it.

Because ternary digits of `2ⁿ` are ~uniform over `{0,1,2}`, the expected carry-chain length
is `Σ (1/3)^j ≈ 1.5`, so the expected work per doubling is `O(1)` and the total for
`n ≤ N` is `O(N)` (plus a final array of length `O(αN)`).

Correctness invariants:
- after `n` doublings the array holds exactly the ternary digits of `2ⁿ`
  (least significant first);
- low `k` digits equal `2ⁿ mod 3^k` for every `k ≤` array length.

## Experiment (per n = 9..10⁶)

Definitions:
- `L(n) = ⌊n·log₃2⌋ + 1` — ternary length of `2ⁿ`
- `W = ⌊L(n)/3⌋` — window length (equal for all three windows)
- trailing window: positions `[0, W)`
- middle window: positions `[W, 2W)`
- leading window: positions `[2W, L(n))`

Per window, compute:
1. digit-2 frequency: `#{k in window : digit₃(2ⁿ,k) = 2} / |window|`
2. longest run of consecutive positions `k` in the window with `digit₃(2ⁿ,k) ≠ 2`
3. is the entire window 2-free? (boolean)
4. position of the first digit `2` within the window (or `∞` if 2-free)

Aggregate over `n`:
- min/max/mean digit-2 frequency per window type (middle vs leading vs trailing)
- record-holders per window type: n minimizing frequency, n maximizing 2-free run,
  all 2-free windows found
- the three window-frequency time series (as a table for later correlation analysis in M2)

## Validation / cross-check

- For `n ≤ 10⁵`: compare the digit array against the existing Rust brute force in
  `verify_erdos_rs` (`ternary_str` output) — must match exactly.
- Internal: for random `n`, check `low_k_digits == 2ⁿ mod 3^k` via Python big-int `pow`.
- Assert `L(n)` matches `⌊n·log₃2⌋ + 1` computed with a high-precision constant
  (e.g., `log(2)/log(3)` via `decimal` or `mpmath` at 50+ digits).

## Implementation plan

1. **Python prototype** `verify_middle/middle_analyzer.py`:
   - carry-chain streaming doubling; per-n window extraction and metrics;
   - records + aggregates; writes `verify_middle/results_m1.csv` (one row per n:
     `n, L, W, freq/run/flag/first for each of trailing/middle/leading`)
   - cross-check module comparing against brute force for `n ≤ 10⁵`.
2. **Timing gate**: prototype must finish `10⁶` in ≤ ~10 minutes in Python. If not,
   port the identical algorithm to Rust (`verify_middle/src/main.rs`, same crate layout
   as `verify_erdos_rs`) and run there. Decide at the gate; record the decision.
3. **M2 (independence test)**, same phase, after the dataset exists:
   - 1-digit cross-tabulation and mutual information between (trailing, middle),
     (leading, middle), (leading, trailing) digit patterns across n;
   - Spearman rank correlation of the per-n window frequencies;
   - test the Lagarias heuristic claim: most-significant and least-significant digits are
     "uncorrelated" — quantify it for the first time.
4. **M3 (Lean formalization)**, after M2:
   - formalize the base-3 doubling transducer `T` and prove correctness:
     `T` maps the ternary digit stream of `x` to that of `2·x`; hence the `k`-th output
     of `Tⁿ` applied to the stream `1, 0, 0, …` equals `digit₃ (2ⁿ) k`. Connect this to
     the existing `digit₃` definitions in `ErdosTernary/Narkiewicz.lean`.
5. **M4 (findings)**: `verify_middle/FINDINGS.md` — records table, middle-vs-ends
   comparison, independence-test summary, and the new conjecture.

## Deliverables

- `verify_middle/middle_analyzer.py` (and `verify_middle/src/main.rs` if ported)
- `verify_middle/crosscheck.py`
- `verify_middle/results_m1.csv`
- `verify_middle/FINDINGS.md`
- (M3) new Lean file `ErdosTernary/ErdosTernary/MiddleDigits.lean` with the transducer,
  zero sorries, `lake build` green.

## Success criteria (M1)

- Full run for `n = 9..10⁶` completes within the timing gate.
- Cross-check passes for all `n ≤ 10⁵`.
- `results_m1.csv` + `FINDINGS.md` produced, containing all four metrics per window and
  the three-window comparison.
- At least one concrete new observation recorded (e.g., no 2-free middle window in range,
  or a record 2-free run with its `n`).

## Out of scope (later phases)

- Phase 8: first-occurrence-of-2 statistics `f(n)` records and gap structure.
- Phase 9: two-sided (leading + trailing) pruning search to beat 5.9×10²¹.
- Any claimed proof of Erdős's conjecture.

## Risks

- Carry-chain amortized-O(1) assumption is heuristic; worst-case (e.g., long `1111…`
  runs) could slow pathological doublings, but frequency is governed by digit uniformity.
  Mitigation: timing gate; Rust fallback.
- Python big-int `pow` cross-check is O(k·log n) per sample — keep the sample set small.
- `⌊L/3⌋` boundary rounding: windows may overlap slightly or leave a gap of ≤ 2 positions;
  acceptable for a statistical first run, recorded in FINDINGS.md.