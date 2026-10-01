import csv
import math

rows = list(csv.DictReader(open("verify_middle/first2_records.csv")))
ns = [int(r["n"]) for r in rows]
fs = [int(r["f"]) for r in rows]
gaps = [int(r["gap_from_previous_record"]) for r in rows]
ratios = [float(r["ratio"]) for r in rows]

print(f"records: {len(rows)}")
print("n      f  L/1e6  ratio      gap   prefix")
for r in rows:
    print(f"{int(r['n']):<7d} {int(r['f']):<3d} {int(r['L'])/1e6:7.3f} {float(r['ratio']):.3e} {int(r['gap_from_previous_record']):<6d} {r['prefix']}")


def ls(xs, ys):
    n = len(xs)
    mx, my = sum(xs) / n, sum(ys) / n
    num = sum((x - mx) * (y - my) for x, y in zip(xs, ys))
    den = sum((x - mx) ** 2 for x in xs)
    return num / den, my - (num / den) * mx


lg = [math.log(max(n, 1)) / math.log(1.5) for n in ns]
slope, intercept = ls(lg, fs)
print(f"f ~ {slope:.3f} * log_(3/2)(n) + {intercept:.2f}")
print(f"max ratio f/L = {max(ratios):.3e} at n={ns[ratios.index(max(ratios))]}")
print(f"max gap = {max(gaps)} at n={ns[gaps.index(max(gaps))]}")