import csv
import math
import sys


def read_rows(path):
    with open(path) as f:
        return list(csv.DictReader(f))


def cross_tab(rows, ca, cb):
    tab = [[0] * 3 for _ in range(3)]
    for r in rows:
        tab[int(r[ca])][int(r[cb])] += 1
    return tab


def chi_square(tab):
    total = sum(map(sum, tab))
    if total == 0:
        return 0.0
    row = [sum(row) for row in tab]
    col = [sum(tab[i][j] for i in range(3)) for j in range(3)]
    stat = 0.0
    for i in range(3):
        for j in range(3):
            e = row[i] * col[j] / total
            if e > 0:
                stat += (tab[i][j] - e) ** 2 / e
    return stat  # ~0 means independent; large means dependent


def spearman(xs, ys):
    def rank(v):
        order = sorted(range(len(v)), key=lambda i: v[i])
        r = [0.0] * len(v)
        i = 0
        while i < len(v):
            j = i
            while j + 1 < len(v) and v[order[j + 1]] == v[order[i]]:
                j += 1
            avg = (i + j) / 2.0 + 1
            for k in range(i, j + 1):
                r[order[k]] = avg
            i = j + 1
        return r

    rx, ry = rank(xs), rank(ys)
    n = len(xs)
    mx = sum(rx) / n
    my = sum(ry) / n
    cov = sum((rx[i] - mx) * (ry[i] - my) for i in range(n))
    vx = math.sqrt(sum((rx[i] - mx) ** 2 for i in range(n)))
    vy = math.sqrt(sum((ry[i] - my) ** 2 for i in range(n)))
    return cov / (vx * vy) if vx * vy > 0 else 0.0


def main(path):
    rows = read_rows(path)
    pairs = [("t0", "m0"), ("t1", "m0"), ("m0", "l0")]
    out = []
    out.append("# M2 Independence Test\n")
    out.append(f"Rows analyzed: {len(rows)}\n")
    for ca, cb in pairs:
        tab = cross_tab(rows, ca, cb)
        out.append(f"## cross-tab {ca} x {cb}\n")
        out.append("| |0|1|2|\n|---|---|---|---|\n")
        for i in range(3):
            out.append(f"|{i}|{tab[i][0]}|{tab[i][1]}|{tab[i][2]}|\n")
        out.append(f"chi-square = {chi_square(tab):.1f} (independent ~ 0)\n")
    fr = [("t_freq", "m_freq"), ("l_freq", "m_freq"), ("l_freq", "t_freq")]
    for ca, cb in fr:
        xs = [float(r[ca]) for r in rows]
        ys = [float(r[cb]) for r in rows]
        out.append(f"Spearman({ca}, {cb}) = {spearman(xs, ys):.4f}\n")
    with open(path.rsplit("/", 1)[0] + "/independence_summary.md", "w") as f:
        f.writelines(out)
    print("independence summary written")


if __name__ == "__main__":
    main(sys.argv[1])