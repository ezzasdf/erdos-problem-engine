import csv
import math
import sys

events = {}
with open("verify_middle/events_m1.csv") as f:
    for r in csv.DictReader(f):
        if r["K"] == "1":
            events[int(r["L"])] = (int(r["N"]), float(r["P_A"]))

rows = list(csv.DictReader(open(sys.argv[1])))
bad = 0
for r in rows:
    l = int(r["L"])
    p = float(r["P_f_ge_L"])
    if l not in events:
        continue
    n, pa = events[l]
    se = math.sqrt(pa * (1 - pa) / n) if n else 0.0
    z = (p - pa) / se if se > 0 else 0.0
    print(f"L={l:2d} P(f>=L)={p:.6f} P(A_L)={pa:.6f} z={z:+.2f} (N={n})")
    if abs(z) > 3.5:
        bad += 1
print("cells with |z|>3.5:", bad)