#!/usr/bin/env python3
"""Phase 7 M4: re-derive every constant in REFINED_CONJECTURES.md.

Reads the two existing, verified datasets and checks each stated constant:
the middle-window digit-2 frequency floor, the set of 2-free middle windows,
the longest 2-free middle run, the first-2-position record statistics, and the
log_{3/2} growth fit.  Every constant here is an EMPIRICAL measurement (or a
conjectural extrapolation labeled as such in REFINED_CONJECTURES.md) -- none of
these are proved results.  Python stdlib only. Run from repo root.
"""

import csv
import math
import statistics

M_FLOOR_EXPECTED = 0.24619289340101522
M_FLOOR_ARG_N = 1874
M_FREE_EXPECTED = {14, 24, 76}
M_LONG_EXPECTED = 61
M_LONG_ARG_N = 385178
RATIO_MAX_EXPECTED = 3.4361768249349467
RATIO_MAX_ARG_N = 121


def load_m1():
    with open("verify_middle/results_m1.csv") as f:
        return list(csv.DictReader(f))


def load_records():
    with open("verify_middle/first2_records.csv") as f:
        return list(csv.DictReader(f))


def check(name, cond, detail=""):
    print(f"{'PASS' if cond else 'FAIL'}  {name}{'  -- ' + detail if detail else ''}")
    return cond


def middle_floor(rows):
    best = None
    for r in rows:
        n = int(r["n"])
        if n <= 1000:
            continue
        freq = float(r["m_freq"])
        if best is None or freq < best[0]:
            best = (freq, n)
    return best


def main():
    rows = load_m1()
    records = load_records()
    results = []

    floor = middle_floor(rows)
    if floor is None:
        results.append(check("middle-window freq floor = 0.24619289340101522",
                             False, "no rows with n>1000 in results_m1.csv"))
    else:
        floor_val, floor_n = floor
        results.append(check("middle-window freq floor = 0.24619289340101522",
                             math.isclose(floor_val, M_FLOOR_EXPECTED, rel_tol=1e-12) and floor_n == M_FLOOR_ARG_N,
                             f"got {floor_val} at n={floor_n}"))

    free = {int(r["n"]) for r in rows if r["m_free"] == "true"}
    results.append(check("2-free middle windows = {14,24,76}",
                         free == M_FREE_EXPECTED, f"got {sorted(free)}"))

    longs = [(int(r["m_long"]), int(r["n"])) for r in rows]
    if not longs:
        results.append(check("longest middle 2-free run = 61 at n=385178",
                             False, "no rows in results_m1.csv"))
    else:
        longest, arg = max(longs)
        results.append(check("longest middle 2-free run = 61 at n=385178",
                             longest == M_LONG_EXPECTED and arg == M_LONG_ARG_N,
                             f"got {longest} at n={arg}"))

    ratios = [(int(r["f"]) / math.log(int(r["n"]), 3), int(r["n"])) for r in records if int(r["n"]) > 1]
    if not ratios:
        results.append(check("max f/log3(n) = 3.4361768249349467 at n=121",
                             False, "no records with n>1 in first2_records.csv"))
    else:
        rmax, rarg = max(ratios)
        results.append(check("max f/log3(n) = 3.4361768249349467 at n=121",
                             math.isclose(rmax, RATIO_MAX_EXPECTED, rel_tol=1e-12) and rarg == RATIO_MAX_ARG_N,
                             f"got {rmax} at n={rarg}"))

    sel = [(int(r["n"]), int(r["f"])) for r in records if int(r["n"]) > 0]
    if not sel:
        results.append(check("log_{3/2} growth fit slope a ~ 1.04",
                             False, "no records with n>0 in first2_records.csv"))
    else:
        xs = [math.log(n, 1.5) for n, _ in sel]
        ys = [f for _, f in sel]
        mx, my = statistics.mean(xs), statistics.mean(ys)
        a = sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / sum((x - mx) ** 2 for x in xs)
        b = my - a * mx
        results.append(check("log_{3/2} growth fit slope a ~ 1.04",
                             abs(a - 1.04) < 0.02, f"got a={a:.3f}, b={b:.3f}"))

    fs = [int(r["f"]) for r in records]
    mono = all(fs[i] < fs[i + 1] for i in range(len(fs) - 1))
    ratio_ok = all(math.isclose(float(r["ratio"]), int(r["f"]) / int(r["L"]), rel_tol=1e-9, abs_tol=1e-9) for r in records)
    gaps = [int(r["n"]) for r in records]
    gap_ok = all(gaps[i] - gaps[i - 1] == int(records[i]["gap_from_previous_record"]) for i in range(1, len(records)))
    results.append(check("record table consistent (f inc, ratio=f/L, gaps)",
                         mono and ratio_ok and gap_ok))

    print("\nAll checks passed." if all(results) else "\nSome checks FAILED.")
    raise SystemExit(0 if all(results) else 1)


if __name__ == "__main__":
    main()
