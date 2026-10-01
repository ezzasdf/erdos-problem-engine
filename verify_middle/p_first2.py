import csv
import math

# Exact P(f>=L) = sum over length-L ternary strings s (s_0=1, rest in {0,1})
# of log_3((t_s + 3^{1-L}) / t_s),  t_s = sum_i s_i 3^{-i}.
# This equals meas(S_L), S_L = {x in [0,1): first L digits of 3^x are != 2},
# the equidistribution limit of P(f(n)>=L) for {n log_3 2}.

def P_exact(L):
    total = 0.0
    for m in range(2 ** (L - 1)):
        t = 1.0
        for i in range(1, L):
            if (m >> (L - 1 - i)) & 1:
                t += 3.0 ** (-i)
        total += math.log((t + 3.0 ** (1 - L)) / t, 3)
    return total

# asymptotic constant: P(f>=L) = C*(2/3)^L*(1 + O(3^{-L}))
C = P_exact(20) * (1.5) ** 20
print(f"asymptotic C = P(f>=L)/(2/3)^L = {C:.10f}  (error ~ 3^-20 = {3.0**-20:.1e})")

meas = {}
with open("verify_middle/first2_events.csv") as f:  # P_f_ge_L measured at N=10^6
    for r in csv.DictReader(f):
        meas[int(r["L"])] = (int(r["N"]), float(r["P_f_ge_L"]))

print("\n== ratio P(f>=L)/(2/3)^L: exact vs measured (z = sampling noise) ==")
print(f"{'L':>2} {'ratio_exact':>12} {'ratio_meas':>12} {'z':>7}")
for L in range(1, 21):
    pe = P_exact(L)
    re = pe / (2 / 3) ** L
    row = f"{L:>2} {re:12.6f}"
    if L in meas:
        n, pm = meas[L]
        pe_l = pe if L <= 20 else C * (2 / 3) ** L  # O(3^{-L}) approx beyond 20
        se = math.sqrt(pe_l * (1 - pe_l) / n)
        z = (pm - pe_l) / se if se > 0 else 0.0
        row += f" {pm/(2/3)**L:12.6f} {z:7.2f}"
    print(row)

print("\n== convergence: ratio -> C with ~3^{-L} corrections ==")
prev = None
for L in [5, 8, 10, 12, 14, 16, 20]:
    re = P_exact(L) / (2 / 3) ** L
    print(f"L={L:>2}: ratio={re:.8f}" + (f"  step={prev - re:+.2e}" if prev else ""))
    prev = re

print("\n== elementary upper bound  P(f>=L) <= 3/(2 ln3) * (2/3)^L ==")
C1 = 3.0 / (2.0 * math.log(3.0))
print(f"C1 = 3/(2 ln3) = {C1:.6f}  (true C = {C:.6f})")
viol = [L for L in range(1, 21) if P_exact(L) / (2 / 3) ** L > C1]
print(f"violations L=1..20: {viol if viol else 'none'}")

print("\n== refined upper bound via 1/(1+X) <= 1 - X + X^2 ==")
def C2(L):
    eX = sum(0.5 * 3.0 ** (-i) for i in range(1, L))
    eX2 = sum(0.5 * 3.0 ** (-2 * i) for i in range(1, L)) + \
          sum(0.25 * 3.0 ** (-(i + j)) for i in range(1, L) for j in range(1, L) if i != j)
    return (3.0 / (2.0 * math.log(3.0))) * (1.0 - eX + eX2)
for L in [1, 2, 5, 8, 12, 16, 20]:
    re = P_exact(L) / (2 / 3) ** L
    print(f"L={L:>2}: ratio_exact={re:.6f}  refined_bound={C2(L):.6f}  ok={re <= C2(L)}")
print(f"asymptotic refined bound: {(3.0/(2*math.log(3.0)))*(1 - 1/4 + 3/32):.6f}")

print("\n== measured residuals vs EXACT P (does C explain the deviation?) ==")
for L in [1, 2, 3, 4, 5, 6, 8, 10, 12, 16, 20, 24, 30]:
    if L not in meas:
        continue
    n, pm = meas[L]
    pe = P_exact(L) if L <= 20 else C * (2 / 3) ** L
    se = math.sqrt(pe * (1 - pe) / n)
    z = (pm - pe) / se if se > 0 else 0.0
    print(f"L={L:>2}: P_meas={pm:.6f} P_exact={pe:.6f} z={z:+.2f} (count={n*pm:.0f})")