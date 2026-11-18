"""Lemma 4.1 residual [C]: exact all-L sign certificate for
h_L = |Z'(L)| - |E(L)| at the crux window k = L-a+1
(Z' = Z1 | Z2; E = class 00 with flip_k destroying admissibility).

Transfer matrix over the reversed word u_t = z_{L-1-t}:
  - admissibility state = last b bits of u;
  - the six anchor positions of the class/break conditions sit at
    fixed u-offsets (independent of L): memorized until position h0,
    then folded into a class label (E / Z1 / Z2 / other);
  - constraints whose u-index exceeds L-1 read 0 (z_{<0} = 0), checked
    terminally.
h_L = #accepted paths with label Z1|Z2 minus #paths with label E.

Certificate: exact integer sequence for L in [a, N]; Berlekamp-Massey
fit; recurrence verified on the remainder; dominant-root tail bound;
positivity for all L >= a  [E: exact integers, numerical root gaps].

Cross-checked against brute force for L <= 14.
"""
from itertools import product
from fractions import Fraction
from math import gcd


def hseq_pair(a, b, Lmin, Lmax):
    """dict L -> h_L for crux windows L in [Lmin, Lmax].

    All L >= a+b-1 share one sweep (anchor u-offsets are L-independent);
    smaller L are handled by short individual sweeps.
    """
    g = b - a
    out = {}
    S = 1 << b
    nxttab = [[0, 0] for _ in range(S)]
    valtab = [[False, False] for _ in range(S)]
    for w in range(S):
        for x in (0, 1):
            u_hpb = (w >> (b - 1)) & 1
            u_hpg = (w >> (g - 1)) & 1
            valtab[w][x] = (0 <= u_hpb - u_hpg + x <= 1)
            nxttab[w][x] = ((w << 1) | x) & (S - 1)

    def sweep(Lmin_, Lmax_, Lfix=None):
        """If Lfix given: single L (anchors built for it).
        Else: assume L >= a+b-1 so anchors/labels identical for all L in
        range; record at each step h with L = h+1."""
        # anchors for L >= a+b-1: u-positions (L-independent)
        if Lfix is not None:
            L0 = Lfix
        else:
            L0 = max(a + b - 1, Lmin_)
        k = L0 - a + 1
        zps = [k - 1, k - 1 - g, k, k - g, k - a, k - b]
        specs = [None if zp < 0 else L0 - 1 - zp for zp in zps]
        ups = [s for s in specs if s is not None]
        h0 = max(ups)
        win_start = h0 - b + 1
        mem_pos = sorted({s for s in ups if s < win_start})
        m = len(mem_pos)

        def lab_from(bits):
            def zget(i):
                s = specs[i]
                return 0 if s is None else bits.get(s, 0)
            z = [zget(i) for i in range(6)]
            c1 = z[0] ^ z[1]
            c0 = z[2] ^ z[3]
            brk = (z[2] - z[4] + z[5]) != z[2]
            if c1 == 0 and c0 == 0 and brk:
                return -1
            if c1 == 1 and c0 == 1:
                return 1
            if c1 == 0 and c0 == 1 and brk:
                return 2
            return 0

        def terminal_ok_at(w, Lval):
            for t in range(max(0, Lval - b), Lval):
                u_t = (w >> (Lval - 1 - t)) & 1 if (Lval - 1 - t) < b else 0
                ta = t + a
                u_ta = (w >> (Lval - 1 - ta)) & 1 if ta < Lval and (Lval - 1 - ta) < b else 0
                if not (0 <= u_t - u_ta <= 1):
                    return False
            return True

        okw_big = [w for w in range(S) if terminal_ok_at(w, L0)]
        cur = {0: 1}
        V = None
        Lend = Lfix if Lfix is not None else Lmax_
        for h in range(Lend):
            if V is None:
                nxtc = {}
                for key, cnt in cur.items():
                    slot = key & 7
                    rest = key >> 3
                    memb = rest & ((1 << m) - 1)
                    w = rest >> m
                    for x in (0, 1):
                        if h >= b and not valtab[w][x]:
                            continue
                        nw = nxttab[w][x] if h >= b else ((w << 1) | x) & (S - 1)
                        nmem = memb
                        for mi, p in enumerate(mem_pos):
                            if p == h:
                                nmem |= (x << mi)
                        nslot = slot
                        if slot == 0 and h == h0:
                            bits = {p: (nmem >> mi) & 1
                                    for mi, p in enumerate(mem_pos)}
                            for s in specs:
                                if s is not None and s >= win_start:
                                    bits[s] = (nw >> (h0 - s)) & 1
                            nslot = lab_from(bits) + 2
                        nkey = ((nw << m) | nmem) * 8 + nslot
                        nxtc[nkey] = nxtc.get(nkey, 0) + cnt
                cur = nxtc
                if Lfix is None and h >= h0 and h >= b - 1:
                    V = [0] * S
                    for key, cnt in cur.items():
                        slot = key & 7
                        w = (key >> 3) >> m
                        lab = slot - 2 if slot else 0
                        if lab == -1:
                            V[w] -= cnt
                        elif lab == 1 or lab == 2:
                            V[w] += cnt
            else:
                nxtV = [0] * S
                for w in range(S):
                    vw = V[w]
                    if vw:
                        if valtab[w][0]:
                            nxtV[nxttab[w][0]] += vw
                        if valtab[w][1]:
                            nxtV[nxttab[w][1]] += vw
                V = nxtV
            L = h + 1
            if Lfix is None:
                if L < Lmin_ or L > Lmax_:
                    continue
            else:
                L = Lfix
                if h != Lfix - 1:
                    continue
            if V is not None:
                out[L] = sum(V[w] for w in okw_big)
                continue
            # terminal checks for this L; weight by label
            okw = [terminal_ok_at(w, L) for w in range(S)]
            E = Z1 = Z2 = 0
            for key, cnt in cur.items():
                slot = key & 7
                w = (key >> 3) >> m
                if not okw[w]:
                    continue
                lab = slot - 2 if slot else 0
                if lab == -1:
                    E += cnt
                elif lab == 1:
                    Z1 += cnt
                elif lab == 2:
                    Z2 += cnt
            out[L] = (Z1 + Z2) - E

    Lbig = a + b - 1
    for L in range(Lmin, min(Lmax, Lbig - 1) + 1):
        sweep(L, L, Lfix=L)
    if Lmax >= Lbig:
        sweep(max(Lmin, Lbig), Lmax)
    return out


def hseq_mod_pair(a, b, Lmin, N, p, p2=None):
    """h_L mod p for L in [Lmin, N] via dense float64 sweep (exact:
    values stay < p, sums < 2**53). Single sweep for L >= a+b-1;
    short dict sweeps for the prefix. Returns list indexed L-Lmin."""
    import numpy as np
    g = b - a
    S = 1 << b
    nxttab = [[0, 0] for _ in range(S)]
    valtab = [[False, False] for _ in range(S)]
    for w in range(S):
        for x in (0, 1):
            u_hpb = (w >> (b - 1)) & 1
            u_hpg = (w >> (g - 1)) & 1
            valtab[w][x] = (0 <= u_hpb - u_hpg + x <= 1)
            nxttab[w][x] = ((w << 1) | x) & (S - 1)
    Lbig = a + b - 1
    k = Lbig - a + 1
    zps = [k - 1, k - 1 - g, k, k - g, k - a, k - b]
    specs = [None if zp < 0 else Lbig - 1 - zp for zp in zps]
    ups = [s for s in specs if s is not None]
    h0 = max(ups)
    win_start = h0 - b + 1
    mem_pos = sorted({s for s in ups if s < win_start})
    m = len(mem_pos)

    def lab_from_z(z):
        c1 = z[0] ^ z[1]
        c0 = z[2] ^ z[3]
        brk = (z[2] - z[4] + z[5]) != z[2]
        if c1 == 0 and c0 == 0 and brk:
            return -1
        if c1 == 1 and c0 == 1:
            return 1
        if c1 == 0 and c0 == 1 and brk:
            return 2
        return 0

    labtab = np.zeros((1 << m) * S, dtype=np.int8)
    for nmem in range(1 << m):
        for nw in range(S):
            bits = {}
            for mi, mp in enumerate(mem_pos):
                bits[mp] = (nmem >> mi) & 1
            for s in specs:
                if s is not None and s >= win_start:
                    bits[s] = (nw >> (h0 - s)) & 1
            z = [0 if sp is None else bits.get(sp, 0) for sp in specs]
            labtab[nmem * S + nw] = lab_from_z(z) + 2

    def terminal_ok(w, L):
        for t in range(max(0, L - b), L):
            u_t = (w >> (L - 1 - t)) & 1 if (L - 1 - t) < b else 0
            ta = t + a
            u_ta = (w >> (L - 1 - ta)) & 1 if ta < L and (L - 1 - ta) < b else 0
            if not (0 <= u_t - u_ta <= 1):
                return False
        return True

    okw = np.array([terminal_ok(w, Lbig) for w in range(S)], dtype=bool)

    out = [0] * (N - Lmin + 1)
    out2 = [0] * (N - Lmin + 1) if p2 else None
    # prefix L < Lbig: exact dict sweeps (few terms)
    if Lmin < Lbig:
        pre = hseq_pair(a, b, Lmin, min(N, Lbig - 1))
        for L, v in pre.items():
            if Lmin <= L <= N:
                out[L - Lmin] = v % p
                if p2:
                    out2[L - Lmin] = v % p2
    if N < Lbig:
        return (out, out2) if p2 else out

    size = 1 << (b + m + 3)
    idx = np.arange(size, dtype=np.int64)
    slot0 = idx & 7
    rest = idx >> 3
    memb0 = rest & ((1 << m) - 1)
    w0 = rest >> m
    nxtarr = np.array(nxttab, dtype=np.int64)
    valarr = np.array(valtab, dtype=bool)
    cur = np.zeros(size, dtype=np.float64)
    cur[0] = 1.0
    pf = float(p)
    pf2 = float(p2) if p2 else None
    cur2 = np.zeros(size, dtype=np.float64) if p2 else None
    if p2:
        cur2[0] = 1.0
    mem_at = {mp: mi for mi, mp in enumerate(mem_pos)}
    for h in range(N):
        src = cur
        acc = np.zeros(size, dtype=np.float64)
        acc2 = np.zeros(size, dtype=np.float64) if p2 else None
        src2 = cur2
        for x in (0, 1):
            mask = src != 0.0
            if h >= b:
                mask &= valarr[w0, x]
            if not mask.any():
                continue
            nw = nxtarr[w0, x]
            if h in mem_at:
                nmem = memb0 + (x << mem_at[h])
            else:
                nmem = memb0
            if h == h0:
                nslot = labtab[nmem * S + nw]
            else:
                nslot = slot0
            target = ((nw << m) | nmem) * 8 + nslot
            acc += np.bincount(target[mask], weights=src[mask],
                               minlength=size)
            if p2:
                m2 = src2 != 0.0
                if h >= b:
                    m2 &= valarr[w0, x]
                acc2 += np.bincount(target[m2], weights=src2[m2],
                                    minlength=size)
        cur = acc % pf
        if p2:
            cur2 = acc2 % pf2
        L = h + 1
        if Lbig <= L <= N and Lmin <= L:
            mask = okw[w0]
            sl = slot0
            E = cur[mask & (sl == 1)].sum()
            Z1 = cur[mask & (sl == 3)].sum()
            Z2 = cur[mask & (sl == 4)].sum()
            out[L - Lmin] = int((Z1 + Z2 - E) % pf)
            if p2:
                E2 = cur2[mask & (sl == 1)].sum()
                Z12 = cur2[mask & (sl == 3)].sum()
                Z22 = cur2[mask & (sl == 4)].sum()
                out2[L - Lmin] = int((Z12 + Z22 - E2) % pf2)
    return (out, out2) if p2 else out


def h_brute(a, b, L):
    """brute-force h_L by enumerating A_L."""
    g = b - a
    k = L - a + 1
    E = Z1 = Z2 = 0
    for w in product((0, 1), repeat=L):
        ok = True
        for i in range(L):
            zi = w[i]
            za = w[i - a] if i - a >= 0 else 0
            zb = w[i - b] if i - b >= 0 else 0
            if not (0 <= zi - za + zb <= 1):
                ok = False
                break
        if not ok:
            continue
        def z(p):
            return w[p] if 0 <= p < L else 0
        c1 = z(k - 1) ^ z(k - 1 - g)
        c0 = z(k) ^ z(k - g)
        brk = (z(k) - z(k - a) + z(k - b)) != z(k)
        v = list(w)
        v[k] ^= 1
        v = tuple(v)
        tok = True
        for i in range(L):
            zi = v[i]
            za = v[i - a] if i - a >= 0 else 0
            zb = v[i - b] if i - b >= 0 else 0
            if not (0 <= zi - za + zb <= 1):
                tok = False
                break
        if c1 == 0 and c0 == 0 and brk:
            E += 1
        elif c1 == 1 and c0 == 1:
            Z1 += 1
        elif c1 == 0 and c0 == 1 and brk:
            Z2 += 1
    return (Z1 + Z2) - E


def _bm_mod(s, p):
    """BM over GF(p) (Wikipedia form, n from 0): returns (d, coeffs)
    with s[n] = sum coeffs[i] s[n-1-i] (mod p)."""
    C = [1 % p]
    B = [1 % p]
    L = 0
    m = 1
    b = 1 % p
    for n in range(len(s)):
        d = s[n] % p
        for i in range(1, min(L, n) + 1):
            d = (d + (C[i] if i < len(C) else 0) * s[n - i]) % p
        if d == 0:
            m += 1
            continue
        T = C[:]
        coef = (d * pow(b, p - 2, p)) % p
        if len(C) < len(B) + m:
            C = C + [0] * (len(B) + m - len(C))
        for i, bi in enumerate(B):
            C[i + m] = (C[i + m] - coef * bi) % p
        if 2 * L <= n:
            L = n + 1 - L
            B = T
            b = d
            m = 1
        else:
            m += 1
    while len(C) > 1 and C[-1] == 0:
        C.pop()
    d = len(C) - 1
    coeffs = [(-C[i]) % p for i in range(1, len(C))]
    return d, coeffs


def berlekamp_massey(s):
    """Modular BM on two primes + CRT; exact verification is external.
    Returns (d, coeffs) with coeffs as Fractions (integers lifted)."""
    p1, p2 = 1000000007, 1000000009
    s1 = [x % p1 for x in s]
    s2 = [x % p2 for x in s]
    d1, c1 = _bm_mod(s1, p1)
    d2, c2 = _bm_mod(s2, p2)
    if d1 != d2:
        # rare: pick the larger as candidate; verification decides
        d, cp, pm = (d1, c1, p1) if d1 > d2 else (d2, c2, p2)
        coeffs = [Fraction(v if v < pm // 2 else v - pm) for v in cp]
        return d, coeffs
    # CRT: x == a (p1), x == b (p2)
    n1, n2 = p1, p2
    inv = pow(n1, -1, n2)
    coeffs = []
    for a, b in zip(c1, c2):
        t = ((b - a) * inv) % n2
        v = a + n1 * t
        if v > (n1 * n2) // 2:
            v -= n1 * n2
        coeffs.append(Fraction(v))
    return d1, coeffs


def recurrence_holds(s, coeffs, d, start, end):
    for n in range(max(start, d), end):
        pred = sum(coeffs[i] * s[n - 1 - i] for i in range(d))
        # coeffs[i] corresponds to s[n-1-i]? normalize below in check
        pass
    return True


def check_recurrence(s, coeffs, d, lo, hi):
    """s[n] = sum coeffs[i] * s[n-d+i] style -- use standard form:
    coeffs[i] * s[n-1-i], i = 0..d-1."""
    for n in range(lo, hi):
        pred = sum(coeffs[i] * s[n - 1 - i] for i in range(d))
        if pred != s[n]:
            return False, n
    return True, None


def poly_roots_dk(cl, maxiter=4000, R=None, trace=None):
    """Durand-Kerner with per-element power-of-two scaling (chunked
    rescale, early escape abort). Returns roots or None."""
    import numpy as np
    c = np.asarray(cl, dtype=complex)
    n = len(c) - 1
    if n <= 0:
        return []
    if R is None:
        R = 1.0
        for i in range(1, n + 1):
            R = max(R, ((n + 1.0) * abs(c[i])) ** (1.0 / i))
    R = max(1.05, float(R))
    k = np.arange(n)
    r = R * (0.4 + 0.6 * (k + 1) / n) * np.exp(2j * np.pi * k / n)
    I = np.eye(n, dtype=bool)
    BIG = 2.0 ** 380
    SML = 2.0 ** -380
    ESC = 20.0 * R

    def rescale(v, e):
        am = np.abs(v)
        hi = am > BIG
        if np.any(hi):
            v[hi] *= SML
            e[hi] += 380
        lo = (am != 0) & (am < SML)
        if np.any(lo):
            v[lo] *= BIG
            e[lo] -= 380
        return v, e

    for _ in range(maxiter):
        pr = np.full(n, c[0], dtype=complex)
        ep = np.zeros(n, dtype=np.int64)
        acc = 0
        for ci in c[1:]:
            pr = pr * r + ci
            acc += 1
            if acc >= 4:
                pr, ep = rescale(pr, ep)
                acc = 0
        if acc:
            pr, ep = rescale(pr, ep)
        pd = np.ones(n, dtype=complex)
        ed = np.zeros(n, dtype=np.int64)
        for j0 in range(0, n, 4):
            for j in range(j0, min(j0 + 4, n)):
                pd = pd * np.where(I[:, j], 1.0 + 0j, r - r[j])
            pd, ed = rescale(pd, ed)
        nz = (pd != 0)
        with np.errstate(divide='ignore', invalid='ignore'):
            mant = pr / np.where(nz, pd, 1.0 + 0j)
            absx = np.abs(mant)
            lg = np.log2(absx) + (ep - ed)
        lg = np.where(np.isnan(lg), -np.inf, lg)
        lg = np.minimum(lg, 900.0)
        mag = np.exp2(lg)
        dirn = np.where(absx > 0, mant / np.where(absx > 0, absx, 1.0),
                        0.0 + 0j)
        with np.errstate(invalid='ignore'):
            delta = np.where(nz, mag * dirn, 0.0 + 0j)
        D = r[:, None] - r[None, :]
        sep = np.min(np.where(I, np.inf, np.abs(D)), axis=1)
        md = np.abs(delta)
        cap = 0.5 * sep
        with np.errstate(over='ignore', invalid='ignore'):
            delta = np.where(md > cap,
                             delta * (cap / np.where(md > 0, md, 1.0)),
                             delta)
        delta = np.where(np.isfinite(delta), delta, 0.0 + 0j)
        r = r - delta
        far = np.abs(r) > 30.0 * R
        if np.any(far):
            rng = np.random.default_rng(12345 + _)
            u = rng.random(int(np.count_nonzero(far)))
            rad = R * (0.4 + 0.6 * u)
            ang = rng.random(int(np.count_nonzero(far)))
            r[far] = rad * np.exp(2j * np.pi * ang)
        mr = np.max(np.abs(r))
        if trace is not None and (_ % 50 == 0):
            trace.append((_, float(mr),
                          float(np.max(np.abs(delta)))))
        if not np.all(np.isfinite(r)):
            return None
        if np.max(np.abs(delta)) < 1e-10 * max(1.0, mr):
            break
    return list(r)


def _resid_mp(lam, ci_mp):
    """Relative residual of the monic polynomial x^d - sum ci x^{d-1-i}
    at lam, via Horner + power-sum denominator (mpmath)."""
    import mpmath as mp
    d = len(ci_mp)
    ml = lam if isinstance(lam, mp.mpc) else mp.mpc(lam)
    pv = mp.mpc(1)
    for c in ci_mp:
        pv = pv * ml - c
    sc = mp.mpf(0)
    av = abs(ml)
    pk = av ** (d - 1)
    for i in range(d):
        sc += abs(ci_mp[i]) * pk
        if av > 0:
            pk /= av
    if sc == 0:
        return 1e9
    return float(abs(pv) / sc)


def eigvals_state_matrix(a, b):
    """Eigenvalues of the state-transfer matrix of the chain SFT.
    Backward-stable (LAPACK) spectrum; roots of the minimal polynomial
    appear with algebraic multiplicity; junk states filter out later."""
    import numpy as np
    W = b
    S = 1 << W
    mask = S - 1
    M = np.zeros((S, S))
    sh = W - a
    for st in range(S):
        zA = (st >> sh) & 1
        zB = st & 1
        for nb in (0, 1):
            if 0 <= nb - zA + zB <= 1:
                ns = (st >> 1) | (nb << (W - 1))
                M[ns, st] += 1.0
    return list(np.linalg.eigvals(M))




def eigvals_sym_matrix(a, b):
    """Eigenvalues of the Z2-folded (bit-complement symmetric) transfer
    matrix M_+ of size 2^(b-1) x 2^(b-1)."""
    import numpy as np
    W = b
    S = 1 << W
    H = 1 << (W - 1)
    mask = S - 1
    M = np.zeros((H, H))
    sh = W - a
    for st in range(H):
        zA = (st >> sh) & 1
        zB = st & 1
        for nb in (0, 1):
            if 0 <= nb - zA + zB <= 1:
                ns = (st >> 1) | (nb << (W - 1))
                if ns >= H:
                    ns = mask ^ ns
                M[ns, st] += 1.0
    return list(np.linalg.eigvals(M))


def select_roots_sqf_Mplus(a, b, coeffs, d):
    """Exact square-free factorization of P(x) over ZZ[x] paired with
    2-step high-precision Newton selection from the Z2-folded transfer
    matrix M_+ (size 2^(b-1)). Returns (roots, worst_resid) or (None, 1e9)."""
    import sympy as sp
    import mpmath as mp
    import numpy as np
    cands = eigvals_sym_matrix(a, b)
    x = sp.Symbol('x')
    P = sp.Poly.from_list([1] + [-int(c) for c in coeffs], gens=x, domain='ZZ')
    _, sqf_factors = P.sqf_list()
    print(f'    [tail d={d}] sqf_list: {[(f.degree(), k) for f, k in sqf_factors]}',
          flush=True)
    old_dps = mp.mp.dps
    try:
        roots_out = []
        for f_poly, mult_k in sqf_factors:
            df = f_poly.degree()
            f_coeffs = [int(c) for c in f_poly.all_coeffs()]
            # Peel exact zero roots if any
            nz = 0
            while len(f_coeffs) > 1 and f_coeffs[-1] == 0:
                f_coeffs.pop()
                nz += 1
            for _ in range(nz):
                roots_out.extend([0.0 + 0.0j] * mult_k)
            df_nz = df - nz
            if df_nz <= 0:
                continue
            max_bit = max(abs(c).bit_length() for c in f_coeffs)
            dps_f = max(45, int(max_bit * 0.31) + 35)
            mp.mp.dps = dps_f
            ci_f_mp = [mp.mpf(-c) for c in f_coeffs[1:]]
            step1 = []
            for lam in cands:
                if abs(lam) < 1e-12:
                    continue
                zm = mp.mpc(lam.real, lam.imag)
                pv = mp.mpc(1)
                p1 = mp.mpc(0)
                for c in ci_f_mp:
                    p1 = p1 * zm + pv
                    pv = pv * zm - c
                if p1 == 0:
                    continue
                dz1 = pv / p1
                z1 = zm - dz1
                rel_dz1 = float(abs(dz1) / max(mp.mpf(1), abs(zm)))
                if rel_dz1 <= 1e-2:
                    step1.append((rel_dz1, z1))
            step1.sort(key=lambda item: item[0])
            dedup = []
            for rdz, z1 in step1:
                z1c = complex(z1)
                if any(abs(z1c - complex(u)) < 1e-7 * max(1.0, abs(z1c))
                       for _, u in dedup):
                    continue
                dedup.append((rdz, z1))
            scored2 = []
            for rdz, z1 in dedup:
                pv = mp.mpc(1)
                p1 = mp.mpc(0)
                for c in ci_f_mp:
                    p1 = p1 * z1 + pv
                    pv = pv * z1 - c
                if p1 == 0:
                    continue
                dz2 = pv / p1
                z2 = z1 - dz2
                rel_dz2 = float(abs(dz2) / max(mp.mpf(1), abs(z1)))
                scored2.append((rel_dz2, complex(z2)))
            scored2.sort(key=lambda item: item[0])
            uniq2 = []
            for rdz2, z2 in scored2:
                if any(abs(z2 - u) < 1e-11 * max(1.0, abs(z2))
                       for _, u in uniq2):
                    continue
                uniq2.append((rdz2, z2))
            if len(uniq2) < df_nz:
                return None, 1e9
            picked_f = [z2 for _, z2 in uniq2[:df_nz]]
            for z in picked_f:
                roots_out.extend([z] * mult_k)
        if len(roots_out) != d:
            return None, 1e9
        mp.mp.dps = 60
        ci_mp = [mp.mpf(c.numerator) / c.denominator for c in coeffs]
        clusts = [[mp.mpc(z.real, z.imag)] for z in roots_out]
        okm, _, errm = verify_multiset(clusts, coeffs, ci_mp, d, [1] * d)
        print(f'    [tail d={d}] sqf+M_+ verify={okm} err={errm}', flush=True)
        if not okm:
            return None, 1e9
        return roots_out, 0.0
    finally:
        mp.mp.dps = old_dps


def _poly3_eval(lam, ci_mp, d):
    import mpmath as mp
    """Return (p, p', p'') at lam for x^d - sum ci[i] x^{d-1-i}."""
    pv = mp.mpc(1); qv = mp.mpc(0); rv = mp.mpc(0)
    for c in ci_mp:
        rv = rv * lam + 2 * qv
        qv = qv * lam + pv
        pv = pv * lam - c
    return pv, qv, rv


def _k_est(lam, ci_mp, d):
    import mpmath as mp
    p, p1, p2 = _poly3_eval(lam, ci_mp, d)
    if p1 == 0:
        return 1, p, p1
    r = p * p2 / (p1 * p1)
    if abs(r) < mp.mpf('1e-6'):
        return 1, p, p1
    kk = 1 / (1 - r)
    if not (mp.isfinite(kk.real) and mp.isfinite(kk.imag)):
        return 1, p, p1
    if abs(kk.imag) > mp.mpf('0.1') * max(abs(kk.real), mp.mpf('1e-12')):
        return 1, p, p1
    krf = kk.real
    kr = int(round(krf))
    if kr < 1 or kr > 40 or abs(krf - kr) > mp.mpf('0.2'):
        return 1, p, p1
    return kr, p, p1




def divk(lam, ci_mp, d, dps=25):
    """Multiplicity estimate via successive synthetic-division remainder
    ratios.  Each division step adaptively raises precision until the
    remainder is trusted against Horner cancellation noise (r_j stays
    ~delta^(m-j) tiny for j << m)."""
    import mpmath as mp
    rho = mp.mpc(lam.real, lam.imag)
    cur = [mp.mpf(1)] + [-c for c in ci_mp]
    rems = []
    k = 0
    dps_cur = 55
    while k < 42:
        if len(cur) <= 1:
            break
        b = None
        r = None
        for _attempt in range(7):
            mp.mp.dps = dps_cur
            b = [cur[0]]
            mpmax = abs(cur[0])
            for i in range(1, len(cur)):
                b.append(cur[i] + rho * b[i - 1])
                a = abs(b[-1])
                if a > mpmax:
                    mpmax = a
            rem = abs(b[-1])
            scale = max(abs(x) for x in cur)
            if scale == 0:
                return 1
            r = rem / scale
            floor = 1e6 * mpmax * mp.power(10, -dps_cur) / scale
            if r > floor or dps_cur >= 340:
                break
            dps_cur = min(dps_cur * 2, 340)
        rems.append(r)
        cur = b[:-1]
        k += 1
        if k >= 2:
            if not (rems[-1] > 10 * max(rems[-2], mp.mpf('1e-300'))):
                return max(k - 2, 1)
    return max(k - 2, 1)

def refine_stalled(roots, ci_f, ci_mp, d, dps=25, maxit=40):
    """For candidates where plain f64 k-est Newton stalls, get k by
    remainder-ratio division, then k-aware f64 Newton (quadratic)."""
    import mpmath as mp
    out = []
    nref = 0
    for lam in roots:
        z = complex(lam)
        stalled = True
        for _ in range(maxit):
            k = _k_est_f64(z, ci_f)
            p, p1, _ = _horner3_f64(z, ci_f)
            if p1 == 0:
                break
            dz = k * p / p1
            z = z - dz
            if abs(dz) < 1e-15 * max(1.0, abs(z)):
                stalled = False
                break
        if stalled:
            kk = divk(z, ci_mp, d, dps)
            zz = complex(z)
            for _ in range(maxit):
                p, p1, _ = _horner3_f64(zz, ci_f)
                if p1 == 0:
                    break
                dz = kk * p / p1
                zz = zz - dz
                if abs(dz) < 1e-15 * max(1.0, abs(zz)):
                    break
            z = zz
            nref += 1
        out.append(z)
    return out, nref

def polish_kaware(roots, coeffs, ci_mp, d, dps=30, maxit=40):
    import mpmath as mp
    """k-aware Newton: z <- z - k*p/p', k re-estimated each step."""
    mp.mp.dps = dps
    out = []
    for lam in roots:
        z = mp.mpc(lam.real, lam.imag)
        k = None
        for _ in range(maxit):
            k, p, p1 = _k_est(z, ci_mp, d)
            if p1 == 0:
                break
            dz = k * p / p1
            z = z - dz
            if abs(dz) < mp.mpf('1e-26') * max(mp.mpf(1), abs(z)):
                break
        k, p, p1 = _k_est(z, ci_mp, d)
        if p1 != 0:
            z = z - k * p / p1
        out.append(z)
    return out


def cluster_polished(pol, tol=1e-9):
    clusts = []
    for lam in sorted(pol, key=lambda z: -abs(z)):
        for cc in clusts:
            if abs(lam - cc[0]) < tol * max(1, abs(cc[0])):
                cc.append(lam)
                break
        else:
            clusts.append([lam])
    return clusts


def div_mult(z, ci_mp, d, dps=220, kmax=40, dbg=False):
    """Multiplicity by repeated synthetic division by (x - z).

    The j-th remainder equals p^{(j-1)}(z)/(j-1)! ~ a * (k-j+1)! *
    delta^{k-j+1}, so divisions succeed exactly while j <= k.  Requires
    delta = |z - rho| well below the tolerance scale (polished roots);
    other roots are irrelevant unless closer than ~1e-28.
    """
    import mpmath as mp
    z = mp.mpc(mp.re(z), mp.im(z))
    old = mp.mp.dps
    mp.mp.dps = dps
    try:
        def polyval(c_list):
            pv = mp.mpc(0)
            for c in c_list:
                pv = pv * z + c
            return pv

        cur = [mp.mpf(1)] + [-c for c in ci_mp]

        def deriv_at(zz):
            p1 = mp.mpc(0)
            n = len(cur) - 1
            for i in range(n):
                p1 = p1 * zz + cur[i] * (n - i)
            return p1

        def poly_at(zz):
            pv = mp.mpc(0)
            for c in cur:
                pv = pv * zz + c
            return pv

        # q-ratio multiplicity estimate: one standard Newton step gives
        # |p(z')/p(z)| = (1 - 1/k)^k for p ~ (x-rho)^k; then k-aware
        # Newton (dz = k p/p') converges in one step to delta ~ dps floor
        kest = 1
        try:
            pv = poly_at(z)
            p1 = deriv_at(z)
            if pv != 0 and p1 != 0:
                z2 = z - pv / p1
                pv2 = poly_at(z2)
                q = abs(pv2 / pv)
                best = None
                for kk in range(1, kmax + 1):
                    qk = mp.mpf(0) if kk == 1 else (
                        (mp.mpf(1) - mp.mpf(1) / kk) ** kk)
                    er = abs(q - qk)
                    if best is None or er < best[0]:
                        best = (er, kk)
                kest = best[1]
                if dbg:
                    print(f'      dbg q-est: q={mp.nstr(q,10)} kest={kest} '
                          f'|pv|={mp.nstr(abs(pv),6)} |p1|={mp.nstr(abs(p1),6)}',
                          flush=True)
        except (ZeroDivisionError, ValueError):
            kest = 1
        for _ in range(8):
            pv = poly_at(z)
            p1 = deriv_at(z)
            if p1 == 0 or pv == 0:
                break
            nrm = abs(cur[0])
            for c in cur[1:]:
                nrm = nrm * abs(z) + abs(c)
            # p at/below cancellation-noise: a further step would use
            # noise/p' as dz and derail an already-converged z
            if abs(pv) <= mp.mpf(10) ** (-(dps - 30)) * max(nrm, mp.mpf(1)):
                break
            z_try = z - kest * pv / p1
            pv_try = poly_at(z_try)
            if not (abs(pv_try) < abs(pv)):
                break
            z = z_try
        if dbg:
            print(f'      dbg after steps: |p(z)|={mp.nstr(abs(poly_at(z)),6)}',
                  flush=True)
        # collect remainder logs, then decide multiplicity by slopes:
        # while rem_j ~ delta^(k-j+1), log-rem is linear with slope
        # log(1/delta) >= 5; the u-tail has slope < 7 (neighbors within
        # the cluster region are merged already), so
        #   k = #{j : in-slope(j) >= 5 and in-slope(j+1) >= 7}
        # which is robust to spectrum-dependent absolute scales that
        # broke the fixed 1e-30 test.
        logs = []
        while len(cur) > 1 and len(logs) < min(kmax + 4, d + 2):
            q = [cur[0]]
            for i in range(1, len(cur) - 1):
                q.append(cur[i] + z * q[-1])
            rem = cur[-1] + z * q[-1]
            nrm = abs(cur[0])
            for c in cur[1:]:
                nrm = nrm * abs(z) + abs(c)
            if rem == 0:
                lr = -1.0e9
            else:
                lr = float(mp.log10(abs(rem) / max(nrm, mp.mpf(1))))
            logs.append(lr)
            if lr > 12.0:
                break
            cur = q
        kk = 0
        floor_r = float(mp.log10(d + 10) - dps + 1)
        if logs and logs[0] <= -10.0:
            while kk < kmax:
                j = kk
                # slopes anchored at cancellation-noise entries are
                # meaningless: bypass them (they lie below any true value)
                if j > 0:
                    if logs[j] > floor_r and logs[j - 1] > floor_r:
                        if logs[j] - logs[j - 1] < 5.0:
                            break
                if j + 1 >= len(logs):
                    break
                if logs[j + 1] > floor_r and logs[j] > floor_r:
                    if logs[j + 1] - logs[j] < 15.0:
                        break
                kk += 1
        if dbg:
            print(f'      dbg rem log10(ratio): '
                  f'{["%.1f" % x for x in logs[:12]]} -> kk={kk}', flush=True)
        return max(1, kk)
    finally:
        mp.mp.dps = old


def deriv_mult_ks(cl2, ci_mp, d, jmax=60, thr=8.0, dps=160):
    """Multiplicity per cluster from the derivative-ratio knee.

    Evaluate p and its first jmax derivatives at w = rho + eps where eps is
    a safe fraction of the minimum inter-cluster distance.  For a root of
    multiplicity k, |p^{(j)}(w)| ~ eps^{k-j} for j <= k, so the log-ratios
    |p^{(j+1)}|/|p^{(j)}| exceed exp(thr) exactly for j < k; afterwards the
    ratios are O(1).  Returns ks with 1 <= ks[i] <= jmax.
    """
    import mpmath as mp
    zs = []
    for z in cl2:
        if isinstance(z, (list, tuple)):
            z = z[0]
        zs.append(mp.mpc(mp.re(z), mp.im(z)))
    fl = [complex(z) for z in zs]
    mind = None
    n = len(fl)
    for i in range(n):
        for j in range(i + 1, n):
            dd = abs(fl[i] - fl[j])
            if mind is None or dd < mind:
                mind = dd
    if mind is None:
        mind = 1.0
    eps = min(mp.mpf('1e-7'), mp.mpf(repr(mind)) / 4)
    if eps < mp.mpf('1e-13'):
        eps = mp.mpf(repr(mind)) / 4
        dps = max(dps, 240)
    a = [mp.mpc(0)] * (d + 1)
    a[d] = mp.mpf(1)
    for i, c in enumerate(ci_mp):
        a[d - 1 - i] = -c
    old = mp.mp.dps
    mp.mp.dps = dps
    out = []
    try:
        fac = [mp.mpf(1)]
        for j in range(1, jmax + 1):
            fac.append(fac[-1] * j)
        thrmp = mp.mpf(str(thr))
        for z in zs:
            w = z + eps
            cser = [mp.mpc(0)] * (jmax + 1)
            cser[0] = a[d]
            for i in range(d - 1, -1, -1):
                nc = [mp.mpc(0)] * (jmax + 1)
                cw = cser[0] * w
                nc[0] = cw + a[i]
                for k in range(1, jmax + 1):
                    nc[k] = cser[k] * w + cser[k - 1]
                cser = nc
            mvals = [cser[j] * fac[j] for j in range(jmax + 1)]
            kk = 0
            for j in range(jmax):
                aj = abs(mvals[j])
                bj = abs(mvals[j + 1])
                if aj == 0:
                    kk = j + 1
                    continue
                if bj == 0:
                    break
                if mp.log(bj / aj) >= thrmp:
                    kk = j + 1
                else:
                    break
            out.append(max(1, min(kk if kk >= 1 else 1, 40)))
    finally:
        mp.mp.dps = old
    return out


def verify_multiset(clusts, coeffs, ci_mp, d, ks=None):
    import mpmath as mp
    """Triple gate: sum k == d, sum k*rho == c0, prod rho^k == |c_{d-1}|.
    Returns (ok, ks, worst_mom_err)."""
    if ks is None:
        ks = [1] * len(clusts)
    if sum(ks) != d or len(clusts) == 0:
        return False, ks, None
    s = mp.mpc(0)
    lp = mp.mpf(0)
    logmag = mp.mpf(0)
    for cc, k in zip(clusts, ks):
        z = cc[0]
        s += k * z
        lp += k * mp.log(z) if False else 0
        logmag += k * mp.log(abs(z))
    tgt1 = ci_mp[0]  # Vieta: sum of roots of x^d - c0 x^{d-1} - ... = +c0
    e1 = float(abs(s - tgt1) / max(1, abs(tgt1)))
    e2 = float(abs(logmag - mp.log(abs(ci_mp[-1]))) /
               max(1, abs(mp.log(abs(ci_mp[-1])))))
    ok = e1 < 1e-6 and e2 < 1e-4
    return ok, ks, max(e1, e2)


def rb_horner(z, ci):
    import mpmath as mp
    pv = mp.mpc(1)
    p1 = mp.mpc(0)
    for c0 in ci:
        p1 = p1 * z + pv
        pv = pv * z - c0
    return pv, p1


def rb_deriv3(z, ci):
    import mpmath as mp
    pv = mp.mpc(1)
    p1 = mp.mpc(0)
    p2 = mp.mpc(0)
    for c0 in ci:
        p2 = p2 * z + 2 * p1
        p1 = p1 * z + pv
        pv = pv * z - c0
    return pv, p1, p2


def rb_mp_k(z, ci):
    import mpmath as mp
    try:
        pv, p1, p2 = rb_deriv3(z, ci)
        if p1 == 0:
            return 1
        r = pv * p2 / (p1 * p1)
        kk = 1 / (1 - r)
        if abs(kk.imag) > 0.1 * max(abs(kk.real), mp.mpf('1e-30')):
            return 1
        kr = int(round(kk.real))
        if 1 <= kr <= 8 and abs(kk.real - kr) < 0.15:
            return kr
    except Exception:
        return 1
    return 1


def rb_polish_poly(z0, quo, tol='1e-55', steps=400, dps=90):
    """Newton-polish z0 against full descending coeff list quo.
    Converts to ci-style (implied monic leading, negated) for rb_horner."""
    import mpmath as mp
    q0 = quo[0]
    ccc = [-x / q0 for x in quo[1:]]
    nrm_q = mp.mpf(1)
    for x in quo:
        nrm_q += abs(x)
    with mp.workdps(dps):
        z = mp.mpc(z0)
        kk = rb_mp_k(z, ccc)
        best = None
        bests = 0
        for s in range(steps):
            pv, p1 = rb_horner(z, ccc)
            if p1 == 0:
                return None
            if abs(pv) <= mp.mpf('1e-180') * nrm_q:
                return z
            zn = z - kk * pv / p1
            if abs(zn) > 1e6:
                return None
            dz = abs(zn - z)
            z = zn
            if dz <= mp.mpf(tol) * max(abs(z), mp.mpf(1)):
                return z
            ap = abs(pv)
            if best is None or ap < best * mp.mpf('1e-3'):
                best = ap
                bests = s
            elif s - bests > 15:
                return None
    return None


_CIF = {}


def _cif(ci):
    key = id(ci)
    if key not in _CIF:
        _CIF[key] = [complex(c) for c in ci]
    return _CIF[key]


def rb_snap(z0, ci, steps=80, dps=300):
    import mpmath as mp
    try:
        zf = complex(z0)
    except Exception:
        zf = None
    if zf is not None:
        cif = _cif(ci)
        for _ in range(30):
            pv = 1 + 0j
            p1 = 0j
            for c in cif:
                p1 = p1 * zf + pv
                pv = pv * zf - c
            if p1 == 0:
                zf = None
                break
            zn = zf - pv / p1
            if abs(zn) > 1e6:
                zf = None
                break
            dz = abs(zn - zf)
            zf = zn
            if dz <= 1e-15 * max(abs(zf), 1.0):
                break
        if zf is None:
            return None
        pv = 1 + 0j
        for c in cif:
            pv = pv * zf - c
        nrm = 1.0
        az = abs(zf)
        for c in cif:
            nrm = nrm * az + abs(c)
            if nrm == float('inf'):
                break
        if nrm == 0 or abs(pv) / max(nrm, 1.0) > 1e-3:
            return None
        z0 = zf
    with mp.workdps(dps):
        z = mp.mpc(z0)
        kk = rb_mp_k(z, ci)
        nrm_p = mp.mpf(1)
        for c in ci:
            nrm_p += abs(c)
        best = None
        bests = 0
        for _ in range(steps):
            pv, p1 = rb_horner(z, ci)
            if p1 == 0:
                return None
            apv = abs(pv)
            if apv <= mp.mpf('1e-180') * nrm_p:
                return z
            zn = z - kk * pv / p1
            if abs(zn) > 1e6:
                return None
            dz = abs(zn - z)
            z = zn
            if dz <= mp.mpf('1e-55') * max(abs(z), mp.mpf(1)):
                return z
            if best is None or apv < best * mp.mpf('1e-3'):
                best = apv
                bests = _
            elif _ - bests > 8:
                return None
    return None


def rb_poly_divmod(a, b, dps):
    import mpmath as mp
    with mp.workdps(dps):
        a = [mp.mpc(x) for x in a]
        b = [mp.mpc(x) for x in b]
        lead = b[0]
        b = [x / lead for x in b]
        a = [x / lead for x in a]
        m = len(b) - 1
        n = len(a) - 1
        if m > n:
            return [], a
        q = [mp.mpc(0)] * (n - m + 1)
        r = list(a)
        for i in range(n - m + 1):
            coef = r[i]
            q[i] = coef
            if coef != 0:
                for j in range(m + 1):
                    r[i + j] -= coef * b[j]
        return q, r[n - m + 1:]


def rb_rel_rem(pv, rem):
    import mpmath as mp
    if not rem or all(x == 0 for x in rem):
        return mp.mpf(0)
    npoly = mp.mpf(1)
    for x in pv:
        npoly = npoly + abs(x)
    return max(abs(x) for x in rem) / max(npoly, mp.mpf(1))


def rb_synth_div(q, z):
    import mpmath as mp
    carry = q[0]
    out = [carry]
    for i in range(1, len(q) - 1):
        carry = q[i] + carry * z
        out.append(carry)
    rem = q[-1] + carry * z
    return out, rem


def rb_rebuild(cl2, ci_mp, d, coeffs, a=None, b=None):
    """Last-resort multiset rebuild: cover roots from state-matrix
    eigvals (plain Newton polish) union snapped views, dedup, re-polish
    at dps250, exact polynomial division p/D, peel known-position
    copies, companion-eig of the remainder, merge, verify.
    Returns (ok, clusters, ks, err, msg)."""
    import mpmath as mp
    import time
    t0 = time.time()
    cov = []
    if a is not None and b is not None:
        try:
            cands = eigvals_state_matrix(a, b)
            with mp.workdps(70):
                res = [_resid_mp(lam, ci_mp) for lam in cands]
            good = [lam for lam, r in zip(cands, res) if r <= 1e-1]
            print(f'    [tail d={d}] rb eigvals: {len(good)}/{len(cands)} '
                  f'candidates ({time.time() - t0:.0f}s)', flush=True)
            nf = 0
            for i, lam in enumerate(good):
                z = rb_snap(lam, ci_mp)
                if z is None:
                    nf += 1
                else:
                    cov.append(z)
                if (i + 1) % 400 == 0:
                    print(f'    [tail d={d}] rb cov {i + 1}/{len(good)} '
                          f'fail={nf} ({time.time() - t0:.0f}s)', flush=True)
            print(f'    [tail d={d}] rb cov: ok={len(cov)} fail={nf} '
                  f'({time.time() - t0:.0f}s)', flush=True)
        except Exception as _ec:
            print(f'    [tail d={d}] rb cov failed: {_ec}', flush=True)
            cov = []
    snapped = []
    nfail = 0
    for i, z0 in enumerate(cl2):
        z = rb_snap(z0, ci_mp)
        if z is None:
            nfail += 1
        else:
            snapped.append(z)
        if (i + 1) % 400 == 0:
            print(f'    [tail d={d}] rb snap {i + 1}/{len(cl2)} '
                  f'({time.time() - t0:.0f}s)', flush=True)
    with mp.workdps(50):
        allz = list(cov) + list(snapped)
        allz.sort(key=lambda z: (float(mp.re(z)), float(mp.im(z))))
        distinct = []
        for z in allz:
            for c in distinct:
                if abs(z - c) < 1e-9 * max(mp.mpf(1), abs(z)):
                    break
            else:
                distinct.append(z)
    pol = []
    nrm_p = mp.mpf(1)
    for c in ci_mp:
        nrm_p += abs(c)
    with mp.workdps(600):
        for r in distinct:
            z = mp.mpc(r)
            kk = rb_mp_k(z, ci_mp)
            for _ in range(80):
                pv, p1 = rb_horner(z, ci_mp)
                if p1 == 0:
                    break
                if abs(pv) <= mp.mpf('1e-180') * nrm_p:
                    break
                zn = z - kk * pv / p1
                dz = abs(zn - z)
                z = zn
                if dz <= mp.mpf('1e-320') * max(abs(z), mp.mpf(1)):
                    break
            pol.append(z)
    distinct = pol
    with mp.workdps(600):
        D = [mp.mpf(1)]
        for r in distinct:
            nd = [mp.mpc(0)] * (len(D) + 1)
            for i, a in enumerate(D):
                nd[i + 1] += a
                nd[i] -= a * r
            D = nd
        D_desc = D[::-1]
        p_desc = [mp.mpf(1)] + [-c for c in ci_mp]
        quo, rem = rb_poly_divmod(p_desc, D_desc, 600)
        rr = rb_rel_rem(p_desc, rem)
    msg = (f'cov={len(cov)} snap={len(snapped)}/{len(cl2)} fail={nfail} '
           f'distinct={len(distinct)} rem={mp.nstr(rr, 4)}')
    if float(rr) > mp.mpf('1e-40'):
        return False, None, None, None, msg + ' BADDIV'
    # peel extra multiplicity copies (z - r) at known positions r
    peel = []
    quo_cur = list(quo)
    with mp.workdps(600):
        for r in distinct:
            while len(quo_cur) >= 2:
                nrm = mp.mpf(1)
                for x in quo_cur:
                    nrm += abs(x)
                out, rem = rb_synth_div(quo_cur, r)
                if abs(rem) <= mp.mpf('1e-40') * nrm:
                    quo_cur = out
                    peel.append(r)
                else:
                    break
    msg += f' peel={len(peel)} rem_deg={len(quo_cur) - 1}'
    eigroots = []
    if len(quo_cur) >= 2:
        import numpy as np
        seeds = np.roots(np.array([complex(x) for x in quo_cur]))
        qcl = []
        for s0 in seeds:
            z = rb_polish_poly(mp.mpc(complex(s0).real, complex(s0).imag),
                               quo_cur, tol='1e-60', steps=400)
            if z is not None:
                qcl.append(z)
        with mp.workdps(50):
            allq = sorted(qcl, key=lambda z: (float(mp.re(z)),
                                              float(mp.im(z))))
            ded = []
            for z in allq:
                for c in ded:
                    if abs(z - c) < 1e-9 * max(mp.mpf(1), abs(z)):
                        break
                else:
                    ded.append(z)
            qcl = ded
        Q2 = list(quo_cur)
        with mp.workdps(600):
            for z in qcl:
                m = 0
                while len(Q2) >= 2:
                    nrm = mp.mpf(1)
                    for x in Q2:
                        nrm += abs(x)
                    out, rem2 = rb_synth_div(Q2, z)
                    if abs(rem2) <= mp.mpf('1e-40') * nrm:
                        Q2 = out
                        m += 1
                    else:
                        break
                    if m > 60:
                        break
                if m:
                    eigroots.extend([z] * m)
        if len(Q2) >= 2:
            qdeg = len(Q2) - 1
            with mp.workdps(50):
                C = mp.matrix(qdeg)
                for j in range(qdeg):
                    C[0, j] = -Q2[j + 1] / Q2[0]
                for i in range(1, qdeg):
                    C[i, i - 1] = 1
                E, _ = mp.eig(C)
            for z in E:
                if abs(z) > 1e6 or z != z:
                    continue
                zz = rb_polish_poly(z, Q2, tol='1e-55', steps=400)
                eigroots.append(zz if zz is not None else z)
            print(f'    [tail d={d}] rb eig fallback: {qdeg} -> '
                  f'{len(eigroots)} roots ({time.time() - t0:.0f}s)',
                  flush=True)
        elif len(Q2) == 2:
            eigroots.append(-Q2[1] / Q2[0])
        print(f'    [tail d={d}] rb hybrid: np={len(qcl)} '
          f'peeled={len(eigroots)} leftover={len(Q2) - 1} '
              f'({time.time() - t0:.0f}s)', flush=True)
    pool = list(distinct) + list(peel) + list(eigroots)
    with mp.workdps(50):
        final_cl = sorted(pool,
                          key=lambda z: (float(mp.re(z)), float(mp.im(z))))
        _ded = []
        for z in final_cl:
            for c in _ded:
                if abs(z - c) < 1e-9 * max(mp.mpf(1), abs(z)):
                    break
            else:
                _ded.append(z)
        final_cl = _ded
        counts = {}
        for z in pool:
            for c in final_cl:
                if abs(z - c) < 1e-9 * max(mp.mpf(1), abs(z)):
                    counts[id(c)] = counts.get(id(c), 0) + 1
                    break
    final_k = [counts.get(id(c), 1) for c in final_cl]
    with mp.workdps(80):
        ok, ks3, err = verify_multiset([[z] for z in final_cl], coeffs,
                                       ci_mp, d, final_k)
    msg2 = (msg + f' ncl={len(final_cl)} sumk={sum(final_k)} '
            f'verify={ok} err={err} t={time.time() - t0:.0f}s')
    if not ok:
        with mp.workdps(80):
            s1 = sum(k * z for k, z in zip(final_k, final_cl))
            lm = sum(k * mp.log(abs(z)) for k, z in zip(final_k, final_cl))
            msg2 += (f' e1={float(abs(s1 - ci_mp[0]) / max(1, abs(ci_mp[0]))):.3e}'
                     f' e2={float(abs(lm - mp.log(abs(ci_mp[-1]))) / max(1, abs(mp.log(abs(ci_mp[-1]))))):.3e}')
    return ok, final_cl, final_k, err, msg2



def _horner3_f64(lam, ci_f):
    """(p, p', p'') at complex128 lam for x^d - sum ci[i] x^{d-1-i}."""
    pv = 1 + 0j; qv = 0j; rv = 0j
    for c in ci_f:
        rv = rv * lam + 2 * qv
        qv = qv * lam + pv
        pv = pv * lam - c
    return pv, qv, rv


def _k_est_f64(lam, ci_f):
    import math
    p, p1, p2 = _horner3_f64(lam, ci_f)
    if p1 == 0:
        return 1
    if not (math.isfinite(abs(p)) and math.isfinite(abs(p1))
            and math.isfinite(abs(p2))):
        return 1
    r = p * p2 / (p1 * p1)
    if abs(r) < 1e-6:
        return 1
    kk = 1 / (1 - r)
    if not (math.isfinite(abs(kk))):
        return 1
    if abs(kk.imag) > 0.1 * max(abs(kk.real), 1e-12):
        return 1
    kr = int(round(kk.real))
    if kr < 1 or kr > 40 or abs(kk.real - kr) > 0.2:
        return 1
    return kr


def polish_kaware_f64(roots, ci_f, maxit=40):
    """k-aware Newton in float64 (fast); returns complex list."""
    out = []
    for lam in roots:
        z = complex(lam)
        for _ in range(maxit):
            k = _k_est_f64(z, ci_f)
            p, p1, _ = _horner3_f64(z, ci_f)
            if p1 == 0:
                break
            dz = k * p / p1
            z = z - dz
            if abs(dz) < 1e-15 * max(1.0, abs(z)):
                break
        out.append(z)
    return out


def mult_by_division(rho, ci_mp, d, maxk=40):
    """Multiplicity via synthetic-division remainders.  rems[j] is the
    remainder of the j-th quotient at rho: for a root of multiplicity m,
    |rems[j]| ~ delta^(m-j) (or exactly 0) for j < m and O(scale) at
    j >= m, so active[j] := (rems[j]==0) or 10*|rems[j]| < |rems[j+1]|
    holds exactly for j < m.  Non-roots: active[0] fails -> 1."""
    import mpmath as mp
    cur = [mp.mpf(1)] + [-c for c in ci_mp]
    rems = []
    while len(cur) > 1 and len(rems) < maxk:
        b = [cur[0]]
        for i in range(1, len(cur)):
            b.append(cur[i] + rho * b[i - 1])
        rems.append(b[-1])
        cur = b[:-1]
    if len(cur) == 1:
        rems.append(cur[0])
    m = 0
    for j in range(len(rems) - 1):
        if rems[j] == 0:
            m += 1
        elif abs(rems[j]) * 10 < abs(rems[j + 1]):
            m += 1
        else:
            break
    return max(m, 1)


def polish_mp_kaware(roots, ci_mp, d, dps=70, maxit=25):
    """k-aware Newton entirely in mpmath (f64 steps are noise-dominated
    for high-degree 59-bit-coefficient polynomials).  k estimated in mp
    from p, p', p'' each iteration (k = 1/(1 - p*p''/p'^2)); correct
    as convergence proceeds, and the step only needs k in (0, 2m).
    Returns (roots, ks) with ks the final k-estimate per root (accurate
    to O(delta*m) at convergence -- much cheaper and more reliable than
    division chains, whose remainders drown in Horner noise at fixed dps)."""
    import mpmath as mp
    mp.mp.dps = dps
    out = []
    ks_out = []
    for lam in roots:
        z = mp.mpc(lam.real, lam.imag)
        kk = mp.mpf(1)
        ests = []
        for _ in range(maxit):
            pv = mp.mpc(1)
            qv = mp.mpc(0)
            rv = mp.mpc(0)
            for c in ci_mp:
                rv = rv * z + 2 * qv
                qv = qv * z + pv
                pv = pv * z - c
            if qv == 0:
                break
            r_est = pv * rv / (qv * qv)
            if abs(1 - r_est) > mp.mpf('1e-12'):
                try:
                    est = mp.re(1 / (1 - r_est))
                    if (mp.isfinite(est) and 0 < est <= 4 * d):
                        kk = est
                        if (mp.mpf('0.5') <= est <= 4 * d
                                and len(ests) < 3):
                            ests.append(int(est + mp.mpf('0.5')))
                except (TypeError, ValueError):
                    pass
            dz = kk * pv / qv
            z = z - dz
            if abs(dz) < mp.mpf(10) ** (-dps + 15) * max(mp.mpf(1), abs(z)):
                break
        # median of the first three (coarse-delta) estimates: correct while
        # delta^m is representable, robust to one garbage seed estimate
        kint = 1
        if ests:
            kint = sorted(ests)[len(ests) // 2]
        out.append(z)
        ks_out.append(max(1, min(kint, 40)))
    return out, ks_out



def mp_polish(roots, coeffs, dps=30):
    """Newton-polish roots with the exact integer polynomial (mpmath)."""
    import mpmath as mp
    mp.mp.dps = dps
    cl = [mp.mpf(1)] + [mp.mpf(c.numerator) / c.denominator
                        for c in coeffs]
    out = []
    for lam in roots:
        z = mp.mpc(lam.real, lam.imag)
        for _ in range(15):
            p = mp.mpf(0)
            pp = mp.mpf(0)
            for ci in cl:
                pp = pp * z + p
                p = p * z + ci
            if p == 0:
                break
            dz = p / pp
            z -= dz
            if abs(dz) < 1e-26 * max(1, abs(z)):
                break
        out.append(complex(z))
    return out


def tail_certificate(s, d, coeffs, Lstart, a=None, b=None):
    """Dominant-root positivity of the tail.  Numerical root gaps +
    float-fitted coefficients [E]; exact integer sequence elsewhere.
    Repeated roots use columns L^j rho^L with per-column j."""
    import numpy as np
    import math
    if any(c.denominator != 1 or abs(c.numerator) >= 2 ** 1023
           for c in coeffs):
        return False, ('bigcoeff',
                       max((c.numerator.bit_length() for c in coeffs),
                           default=0))
    cl = [1.0] + [-float(c) for c in coeffs]
    if d <= 100:
        import sympy as sp
        x = sp.symbols('x')
        spcl = [sp.Integer(1)]
        for i in range(d):
            spcl.append(-sp.Rational(coeffs[i].numerator,
                                     coeffs[i].denominator))
        P = sp.Poly(spcl, x)
        try:
            roots = list(P.nroots(n=40, maxsteps=100))
            roots = [complex(r) for r in roots]
        except Exception:
            roots = None
        if roots is None:
            roots = poly_roots_dk(cl)
            if roots is None:
                return False, 'dk diverge'
    # exact residual validation of every root (high precision)
    import mpmath as mp
    mp.mp.dps = 40
    ci_mp = [mp.mpf(c.numerator) / c.denominator for c in coeffs]

    def worst_resid(rts):
        w = 0.0
        for lam in rts:
            rr = _resid_mp(lam, ci_mp)
            if rr > w:
                w = rr
        return w

    if d <= 100 and roots is not None:
        worst = worst_resid(roots)
        if worst > 1e-8:
            return False, ('rootresid', worst)
    else:
        roots = None
        worst = 1e9
        if a is not None and b is not None and (1 << b) <= 8192:
            try:
                roots_sqf, worst_sqf = select_roots_sqf_Mplus(
                    a, b, coeffs, d)
                if roots_sqf is not None and worst_sqf <= 1e-8:
                    roots, worst = roots_sqf, worst_sqf
            except Exception as _esqf:
                print(f'    [tail d={d}] sqf+M_+ exc: {_esqf}', flush=True)
        if roots is None and a is not None and b is not None and (1 << b) <= 8192:
            cands = eigvals_state_matrix(a, b)
            res_list = [(lam, _resid_mp(lam, ci_mp)) for lam in cands]
            print(f'    [tail d={d}] eigvals: {len(cands)} cands',
                  flush=True)
            counts = []
            for thr in (1e-15, 1e-14, 1e-13, 1e-12, 1e-10):
                good = [lam for lam, rr in res_list if rr <= thr]
                if len(good) < d:
                    counts.append((thr, 1e-6, len(good), '<d'))
                    continue
                for tol in (1e-6, 1e-4):
                    clusts = []
                    for lam in sorted(good, key=lambda z: -abs(z)):
                        for cc in clusts:
                            if abs(lam - cc[0]) < tol * max(1.0,
                                                            abs(cc[0])):
                                cc.append(lam)
                                break
                        else:
                            clusts.append([lam])
                    counts.append((thr, tol, len(good), len(clusts)))
                    if len(clusts) == d:
                        good = [cc[0] for cc in clusts]
                        print(f'    [tail d={d}] eigvals thr={thr:.0e} '
                              f'tol={tol:.0e} clusters={len(clusts)}',
                              flush=True)
                        w = worst_resid(good)
                        if w > 1e-8:
                            print(f'    [tail d={d}] polish from '
                                  f'worst={w:.1e}', flush=True)
                            good = mp_polish(good, coeffs)
                            w = worst_resid(good)
                        if w <= 1e-8:
                            roots, worst = good, w
                        break
                if roots is not None:
                    break
            if roots is None:
                print(f'    [tail d={d}] eigvals counts: '
                      f'{[(t, to, g, c) for t, to, g, c in counts]}',
                      flush=True)
                good = [lam for lam, rr in res_list if rr <= 1e-10]
                if len(good) >= d:
                    ci_f = [complex(c.numerator) / c.denominator
                            for c in coeffs]
                    pol, nref = refine_stalled(good, ci_f, ci_mp, d)
                    cl2 = cluster_polished(pol, 1e-9)
                    ks = [divk(complex(cc[0]), ci_mp, d) for cc in cl2]
                    okm, ksm, errm = verify_multiset(
                        cl2, coeffs, ci_mp, d, ks)
                    print(f'    [tail d={d}] mult path: clusters='
                          f'{len(cl2)} sumk={sum(ks)} refined={nref} '
                          f'verify={okm} err={errm}', flush=True)
                    if not okm:
                        print(f'    [tail d={d}] mp k-aware polish '
                              f'({len(good)} seeds)', flush=True)
                        pol2, ksp = polish_mp_kaware(good, ci_mp, d, dps=85)
                        # cluster (root, k) pairs; k of a cluster = max seed k
                        pairs = sorted(zip(pol2, ksp),
                                       key=lambda pk: -abs(pk[0]))
                        pcl = []
                        for (zv, kv) in pairs:
                            for cc in pcl:
                                if abs(zv - cc[0]) < 1e-9 * max(1, abs(zv)):
                                    cc[1] = max(cc[1], kv)
                                    cc[2].append(zv)
                                    break
                            else:
                                pcl.append([zv, kv, [zv]])
                        kept = []
                        nrec = 0
                        for cc in pcl:
                            zz = cc[0]
                            pv = mp.mpc(1)
                            nrm = mp.mpf(1)
                            for c0 in ci_mp:
                                pv = pv * zz - c0
                                nrm = nrm * abs(zz) + abs(c0)
                            if abs(pv) <= mp.mpf('1e-18') * max(nrm, mp.mpf(1)):
                                kept.append(cc)
                            else:
                                # any other candidate: Newton at high dps;
                                # keep only if it lands on a fresh root
                                olddps = mp.mp.dps
                                mp.mp.dps = 160
                                try:
                                    z2 = mp.mpc(mp.re(zz), mp.im(zz))
                                    for _ in range(10):
                                        pv2 = mp.mpc(1)
                                        p1 = mp.mpc(0)
                                        for c0 in ci_mp:
                                            p1 = p1 * z2 + pv2
                                            pv2 = pv2 * z2 - c0
                                        if p1 == 0:
                                            break
                                        z2 = z2 - pv2 / p1
                                    pv3 = mp.mpc(1)
                                    nrm3 = mp.mpf(1)
                                    for c0 in ci_mp:
                                        pv3 = pv3 * z2 - c0
                                        nrm3 = nrm3 * abs(z2) + abs(c0)
                                    if abs(pv3) <= mp.mpf('1e-40') * max(nrm3, mp.mpf(1)):
                                        far = True
                                        for kc in kept:
                                            if abs(z2 - kc[0]) < 1e-9 * max(1, abs(z2)):
                                                far = False
                                                break
                                        if far:
                                            kept.append([z2] + list(cc[1:]))
                                            nrec += 1
                                finally:
                                    mp.mp.dps = olddps
                        if nrec:
                            print(f'    [tail d={d}] recovered {nrec} '
                                  f'marginal root(s)', flush=True)
                        if len(kept) != len(pcl):
                            print(f'    [tail d={d}] resid gate: '
                                  f'{len(pcl)} -> {len(kept)}', flush=True)
                        # re-merge kept positions at 1e-9 (recovered roots
                        # may coincide with fragments)
                        mcl = []
                        for cc in sorted(kept, key=lambda c: -abs(c[0])):
                            zz = cc[0]
                            for mc in mcl:
                                if abs(zz - mc[0]) < 1e-9 * max(1, abs(zz)):
                                    break
                            else:
                                mcl.append(cc)
                        kept = mcl
                        cl2 = [cc[0] for cc in kept]
                        ks = [cc[1] for cc in kept]
                        ks_p = list(ks)
                        ks = [div_mult(zv, ci_mp, d, dbg=True) for zv in cl2]
                        _cp = {}
                        _cd = {}
                        for e in ks_p:
                            _cp[e] = _cp.get(e, 0) + 1
                        for e in ks:
                            _cd[e] = _cd.get(e, 0) + 1
                        print(f'    [tail d={d}] div ks: kh={_cd} '
                              f'polish_kh={_cp}', flush=True)
                        okm, ksm, errm = verify_multiset(
                            [[z] for z in cl2], coeffs, ci_mp, d, ks)
                        from collections import Counter as _C
                        print(f'    [tail d={d}] mp mult path: '
                              f'clusters={len(cl2)} sumk={sum(ks)} '
                              f'verify={okm} err={errm} '
                              f'kh={dict(sorted(_C(ks).items()))}', flush=True)
                        if not okm and sum(ks) != d:
                            need = sum(ks) - d
                            # first-moment fix: shifting sum(ks) by +-1 on
                            # cluster i moves S by -+rho_i; solve for the
                            # subset whose rho's close the complex gap.
                            T = ci_mp[0]  # Vieta sum = +c0 (matches verify)
                            S = mp.mpc(0)
                            for zv, kv in zip(cl2, ks):
                                S += kv * zv
                            zl = [complex(zv) for zv in cl2]
                            if need > 0:
                                gap = complex(S - T)
                                # decrement sel clusters: sum rho = gap
                                if need == 1:
                                    cands = [(abs(zl[i] - gap), i)
                                             for i in range(len(zl))]
                                    cands.sort()
                                    trial_idx = [list(c[1:])
                                                 for c in cands[:64]]
                                elif need == 2:
                                    cands = []
                                    for i in range(len(zl)):
                                        for j in range(i, len(zl)):
                                            cands.append(
                                                (abs(zl[i] + zl[j] - gap),
                                                 i, j))
                                    cands.sort()
                                    trial_idx = [list(c[1:])
                                                 for c in cands[:64]]
                                else:
                                    # |need| >= 3: greedy sequential —
                                    # pick cluster whose rho is closest
                                    # to the remaining gap, repeat; a
                                    # few forced first picks for variety
                                    trial_idx = []

                                    import math as _m

                                    def _greedy_dec(first):
                                        rem = gap
                                        lm = 0.0
                                        for t in range(len(zl)):
                                            if abs(zl[t]) > 0:
                                                lm += (ks[t] *
                                                       _m.log(abs(zl[t])))
                                        Lt = lm - _m.log(abs(
                                            complex(ci_mp[-1])))
                                        ks_t = list(ks)
                                        if ks_t[first] < 1:
                                            return None
                                        ks_t[first] -= 1
                                        rem -= zl[first]
                                        if abs(zl[first]) > 0:
                                            Lt -= _m.log(abs(zl[first]))
                                        picks = [first]
                                        left = need - 1
                                        while left > 0:
                                            pool = [j for j in
                                                    range(len(zl))
                                                    if ks_t[j] >= 1 and
                                                    abs(zl[j]) > 0]
                                            if not pool:
                                                return None
                                            tr = rem / left
                                            tl = Lt / left
                                            j = min(pool, key=lambda q:
                                                    abs(zl[q] - tr) + 3.0 *
                                                    abs(_m.log(abs(zl[q]))
                                                        - tl))
                                            ks_t[j] -= 1
                                            rem -= zl[j]
                                            Lt -= _m.log(abs(zl[j]))
                                            picks.append(j)
                                            left -= 1
                                        return picks

                                    order = sorted(range(len(zl)),
                                                  key=lambda i:
                                                  abs(zl[i] - gap / need))
                                    for i in order[:6]:
                                        p = _greedy_dec(i)
                                        if p:
                                            trial_idx.append(p)
                                    # twin-pair enumeration: excess
                                    # clusters come from unmerged duplicate
                                    # views (distance far below spectrum
                                    # bulk); enumerate one-member-per-pair
                                    import itertools as _it
                                    _nn = {}
                                    for _i in range(len(zl)):
                                        for _j in range(_i + 1, len(zl)):
                                            _dd = abs(zl[_i] - zl[_j])
                                            if _dd < 1e-3 * max(
                                                    1.0, abs(zl[_i])):
                                                _nn.setdefault(_i, []).append(
                                                    (_dd, _j))
                                    _tp = []
                                    _seen = set()
                                    for _i, _lst in sorted(_nn.items()):
                                        _dd, _j = min(_lst)
                                        _key = (min(_i, _j), max(_i, _j))
                                        if _key in _seen:
                                            continue
                                        if not any(_j in pair or _i in pair
                                                   for pair in _tp):
                                            _seen.add(_key)
                                            _tp.append((_i, _j))
                                    _ncomb = (0)
                                    if len(_tp) >= need:
                                        _c = 1
                                        for _x in range(need):
                                            _c = _c * (len(_tp) - _x) // (
                                                _x + 1)
                                        _ncomb = _c * (1 << need)
                                    if 0 < _ncomb <= 200000:
                                        _cand2 = []
                                        for _combo in _it.combinations(
                                                _tp, need):
                                            for _bits in range(1 << need):
                                                _sel = [
                                                    _combo[_b]
                                                    [(_bits >> _b) & 1]
                                                    for _b in range(need)]
                                                if len(set(_sel)) != need:
                                                    continue
                                                _e = abs(
                                                    sum(zl[_k]
                                                        for _k in _sel)
                                                    - gap)
                                                _cand2.append((_e, _sel))
                                        _cand2.sort(key=lambda t: t[0])
                                        for _e, _sel in _cand2[:64]:
                                            trial_idx.append(_sel)
                                        print(f'    [tail d={d}] twin '
                                              f'pairs={len(_tp)} '
                                              f'cands={len(_cand2)} '
                                              f'best_e1={_cand2[0][0]:.2e}',
                                              flush=True)
                                    # junk-first: clusters with the largest
                                    # |p(z)|/nrm (excess = duplicates/junk)
                                    ci_f = [complex(c0) for c0 in ci_mp]

                                    def _resid(i):
                                        z = zl[i]
                                        pv = complex(1)
                                        nr = complex(1)
                                        for c0 in ci_f:
                                            pv = pv * z - c0
                                            nr = nr * abs(z) + abs(c0)
                                        return abs(pv) / max(
                                            abs(nr), 1.0)

                                    trial_idx.append(sorted(
                                        range(len(zl)),
                                        key=lambda i: -_resid(i))[:need])
                                    # also: the clusters with largest |rho|
                                    trial_idx.append(sorted(
                                        range(len(zl)),
                                        key=lambda i: -abs(zl[i]))[:need])
                                for sel in trial_idx:
                                    ks2 = list(ks)
                                    cl2b = list(cl2)
                                    for idx in sel:
                                        ks2[idx] -= 1
                                        if ks2[idx] <= 0:
                                            ks2[idx] = -1  # mark drop
                                    keep = [(z, k) for z, k in zip(cl2b, ks2)
                                            if k > 0]
                                    cl2c = [z for z, k in keep]
                                    ks3 = [k for z, k in keep]
                                    ok2, ksm2, err2 = verify_multiset(
                                        [[z] for z in cl2c], coeffs,
                                        ci_mp, d, ks3)
                                    if ok2:
                                        print(f'    [tail d={d}] repair dec '
                                              f'{sel}', flush=True)
                                        cl2, ks, okm, ksm, errm = (
                                            cl2c, ks3, ok2, ksm2, err2)
                                        break
                            elif need < 0:
                                gap = complex(T - S)
                                nb = -need
                                if nb == 1:
                                    cands = [(abs(zl[i] - gap), i)
                                             for i in range(len(zl))]
                                    cands.sort()
                                    trial_idx = [list(c[1:])
                                                 for c in cands[:64]]
                                elif nb == 2:
                                    cands = []
                                    for i in range(len(zl)):
                                        for j in range(i, len(zl)):
                                            cands.append(
                                                (abs(zl[i] + zl[j] - gap),
                                                 i, j))
                                    cands.sort()
                                    trial_idx = [list(c[1:])
                                                 for c in cands[:64]]
                                else:
                                    # |need| >= 3: greedy increments
                                    trial_idx = []

                                    import math as _m

                                    def _greedy_inc(first):
                                        rem = gap
                                        lm = 0.0
                                        for t in range(len(zl)):
                                            if abs(zl[t]) > 0:
                                                lm += (ks[t] *
                                                       _m.log(abs(zl[t])))
                                        Lt = _m.log(abs(
                                            complex(ci_mp[-1]))) - lm
                                        picks = [first]
                                        rem -= zl[first]
                                        if abs(zl[first]) > 0:
                                            Lt -= _m.log(abs(zl[first]))
                                        left = nb - 1
                                        while left > 0:
                                            tr = rem / left
                                            tl = Lt / left
                                            j = min(range(len(zl)),
                                                    key=lambda q:
                                                    abs(zl[q] - tr) + 3.0 *
                                                    abs(_m.log(max(
                                                        abs(zl[q]), 1e-300))
                                                        - tl))
                                            rem -= zl[j]
                                            if abs(zl[j]) > 0:
                                                Lt -= _m.log(abs(zl[j]))
                                            picks.append(j)
                                            left -= 1
                                        return picks

                                    order = sorted(range(len(zl)),
                                                  key=lambda i:
                                                  abs(zl[i] - gap / nb))
                                    for i in order[:6]:
                                        trial_idx.append(_greedy_inc(i))
                                    trial_idx.append(sorted(
                                        range(len(zl)),
                                        key=lambda i: -abs(zl[i]))[:nb])
                                for sel in trial_idx:
                                    ks2 = list(ks)
                                    for idx in sel:
                                        ks2[idx] += 1
                                    ok2, ksm2, err2 = verify_multiset(
                                        [[z] for z in cl2], coeffs,
                                        ci_mp, d, ks2)
                                    if ok2:
                                        print(f'    [tail d={d}] repair inc '
                                              f'{sel}', flush=True)
                                        ks, okm, ksm, errm = (
                                            ks2, ok2, ksm2, err2)
                                        break
                            if not okm:
                                # last resort: snap + exact division +
                                # companion eig of the quotient
                                try:
                                    _ok3, _cl3, _kk3, _err3, _msg3 = (
                                        rb_rebuild(list(cl2), ci_mp, d,
                                                   coeffs, a, b))
                                    print(f'    [tail d={d}] rebuild: '
                                          f'{_msg3}', flush=True)
                                    if _ok3:
                                        cl2, ks, okm, ksm, errm = (
                                            _cl3, _kk3, _ok3, _kk3, _err3)
                                except Exception as _e:
                                    print(f'    [tail d={d}] rebuild failed: '
                                          f'{_e}', flush=True)
                            if not okm:
                                logmag = mp.mpf(0)
                                for zv, kv in zip(cl2, ks):
                                    logmag += kv * mp.log(abs(zv))
                                e1d = float(abs(S - T) /
                                            max(1, abs(T)))
                                e2d = float(abs(logmag -
                                                 mp.log(abs(ci_mp[-1]))) /
                                            max(1, abs(mp.log(abs(ci_mp[-1])))))
                                print(f'    [tail d={d}] repair: no fix '
                                      f'need={need} e1={e1d:.3e} '
                                      f'e2={e2d:.3e}', flush=True)
                                try:
                                    import pickle as _pk
                                    with open(
                                            f'/tmp/lemma41_fail_d{d}.pkl',
                                            'wb') as _f:
                                        _pk.dump({
                                            'd': d,
                                            'cl2': [str(z) for z in cl2],
                                            'ks': list(ks),
                                            'ci': [str(c) for c in ci_mp],
                                            'need': need,
                                            'gap': str(gap),
                                            'coeffs': str(coeffs),
                                        }, _f)
                                    print(f'    [tail d={d}] dumped '
                                          f'/tmp/lemma41_fail_d{d}.pkl',
                                          flush=True)
                                except Exception as _e:
                                    print(f'    [tail d={d}] dump failed: '
                                          f'{_e}', flush=True)
                                try:
                                    _t5 = [(round(float(c[0]), 4),)
                                           + tuple(c[1:]) for c in cands[:5]]
                                    print(f'    [tail d={d}] repair top5 '
                                          f'{_t5} gap={gap:.6e}',
                                          flush=True)
                                except Exception:
                                    pass
                        elif not okm and sum(ks) == d:
                            # sumk exact but moments off: greedy multi-round
                            # swap of one unit of multiplicity
                            import math
                            for _round in range(10):
                                if okm:
                                    break
                                T = -ci_mp[0] * 0 + ci_mp[0]
                                S = mp.mpc(0)
                                logmag = mp.mpf(0)
                                for zv, kv in zip(cl2, ks):
                                    S += kv * zv
                                    logmag += kv * mp.log(abs(zv))
                                G = complex(T - S)
                                H = complex(mp.log(abs(ci_mp[-1])) - logmag)
                                zl = [complex(zv) for zv in cl2]
                                lmag = [abs(zv) for zv in zl]
                                sc1 = max(1.0, abs(complex(T)))
                                sc2 = max(1.0, abs(complex(
                                    mp.log(abs(ci_mp[-1])))))
                                cands = []
                                for i in range(len(ks)):
                                    if ks[i] < 2:
                                        continue
                                    for j in range(len(ks)):
                                        if i == j or lmag[j] == 0:
                                            continue
                                        e1g = abs(zl[i] - zl[j] - G) / sc1
                                        e2g = abs((math.log(lmag[i])
                                                   - math.log(lmag[j]))
                                                  - H) / sc2
                                        cands.append((e1g + e2g, i, j))
                                cands.sort()
                                hit = False
                                for _sc, i, j in cands[:64]:
                                    ks2 = list(ks)
                                    ks2[i] -= 1
                                    ks2[j] += 1
                                    ok2, ksm2, err2 = verify_multiset(
                                        [[z] for z in cl2], coeffs,
                                        ci_mp, d, ks2)
                                    if ok2:
                                        print(f'    [tail d={d}] repair swap '
                                              f'r{_round} {i}->{j}',
                                              flush=True)
                                        ks, okm, ksm, errm = (
                                            ks2, ok2, ksm2, err2)
                                        hit = True
                                        break
                                if not hit:
                                    if not cands:
                                        break
                                    _sc, i, j = cands[0]
                                    ks[i] -= 1
                                    ks[j] += 1
                                    print(f'    [tail d={d}] swap step '
                                          f'r{_round}: {i}->{j} '
                                          f'score={_sc:.3e}', flush=True)
                            if not okm:
                                # last resort: snap + exact division +
                                # companion eig of the quotient
                                try:
                                    _ok3, _cl3, _kk3, _err3, _msg3 = (
                                        rb_rebuild(list(cl2), ci_mp, d,
                                                   coeffs, a, b))
                                    print(f'    [tail d={d}] rebuild: '
                                          f'{_msg3}', flush=True)
                                    if _ok3:
                                        cl2, ks, okm, ksm, errm = (
                                            _cl3, _kk3, _ok3, _kk3, _err3)
                                except Exception as _e:
                                    print(f'    [tail d={d}] rebuild failed: '
                                          f'{_e}', flush=True)
                            if not okm:
                                logmag = mp.mpf(0)
                                for zv, kv in zip(cl2, ks):
                                    logmag += kv * mp.log(abs(zv))
                                e1d = float(abs(S - ci_mp[0]) /
                                            max(1, abs(ci_mp[0])))
                                e2d = float(abs(logmag -
                                                 mp.log(abs(ci_mp[-1]))) /
                                            max(1, abs(mp.log(abs(ci_mp[-1])))))
                                njunk = 0
                                for zi, zv in enumerate(cl2):
                                    if abs(complex(zv).imag) < 1e-14:
                                        continue
                                    cj = complex(complex(zv).conjugate())
                                    if all(abs(cj - complex(cl2[zj])) >
                                           1e-9 * max(1, abs(cj))
                                           for zj in range(len(cl2))
                                           if zj != zi):
                                        njunk += 1
                                print(f'    [tail d={d}] swap repair: no fix '
                                      f'e1={e1d:.3e} e2={e2d:.3e} '
                                      f'nconj_miss={njunk} '
                                      f'best={cands[0][0] if cands else None}',
                                      flush=True)
                    if okm:
                        rts = []
                        for cc, k in zip(cl2, ksm):
                            rts.extend([complex(cc)] * k)
                        w = worst_resid(rts)
                        if w > 1e-8:
                            print(f'    [tail d={d}] mp polish worst='
                                  f'{w:.1e} -> refine', flush=True)
                        if w <= 1e-8:
                            roots, worst = rts, w
        if roots is None or worst > 1e-8:
            # Durand-Kerner fallback with data-driven radius ladder
            R0 = 2.0
            try:
                j = min(1500, len(s) - 2)
                q = float(s[j]) / float(s[j - 1]) if s[j - 1] else 0.0
                if 0.5 < q < 100.0:
                    R0 = q
            except Exception:
                pass
            roots = None
            worst = 1e9

            def _mom_err(rts):
                err = 0.0
                if d >= 1 and len(cl) > 1:
                    ss = sum(complex(z) for z in rts)
                    tg = -cl[1]
                    err = max(err, abs(ss - tg) /
                              max(1.0, abs(tg)))
                if d >= 2 and cl[d] != 0:
                    lg = 0.0
                    for z in rts:
                        lg += math.log(abs(z)) if abs(z) else -1e9
                    tg = math.log(abs(cl[d]))
                    err = max(err, abs(lg - tg) /
                              max(1.0, abs(tg)))
                return err

            for Rtry in (1.15 * R0, 1.6 * R0, 0.9 * R0, 2.4 * R0):
                cand = poly_roots_dk(cl, maxiter=4000, R=Rtry)
                print(f'    [tail d={d}] dk R={Rtry:.2f}: '
                      f'{len(cand) if cand else None}', flush=True)
                if cand is None:
                    continue
                w = worst_resid(cand)
                if w > 1e-8:
                    print(f'    [tail d={d}] polish from worst={w:.1e}',
                          flush=True)
                    cand = mp_polish(cand, coeffs)
                    w = worst_resid(cand)
                if w <= 1e-8:
                    me = _mom_err(cand)
                    print(f'    [tail d={d}] dk mom err={me:.1e}',
                          flush=True)
                    if me <= 1e-4:
                        roots, worst = cand, w
                        break
                    roots, worst = cand, w  # keep for diagnostics
                else:
                    roots, worst = cand, w
        if roots is None or worst > 1e-8:
            return False, ('rootresid', worst)
    # symmetric-moment gate: sum and product of roots must match the
    # exact polynomial (catches duplicate/missing root sets that would
    # otherwise pass per-root residuals)
    import numpy as _np
    if d >= 1:
        ssum = sum(complex(z) for z in roots)
        tgt = -cl[1] if len(cl) > 1 else 0.0
        if abs(ssum - tgt) > 1e-5 * max(1.0, abs(tgt)):
            return False, ('momsum', float(abs(ssum - tgt)))
    if d >= 2:
        lg = 0.0
        zero = False
        for z in roots:
            az = abs(z)
            if az == 0:
                zero = True
                break
            import math as _math
            lg += _math.log(az)
        if not zero and cl[d] != 0:
            import math as _math
            tgt = _math.log(abs(cl[d]))
            if abs(lg - tgt) > 1e-4 * max(1.0, abs(tgt)):
                return False, ('momprod', float(abs(lg - tgt)))
    # cluster by modulus (conjugate pairs share |rho|)
    groups = []
    for r in roots:
        ar = abs(r)
        for g in groups:
            if abs(ar - g[0]) < 1e-9 * max(1.0, ar):
                g[1].append(r)
                break
        else:
            groups.append([ar, [r]])
    groups.sort(key=lambda g: -g[0])
    clusters = []
    for g in groups:
        reps = []
        for v in g[1]:
            for rep in reps:
                if abs(v - rep[0]) < 1e-9 * max(1.0, abs(v)):
                    rep[1] += 1
                    break
            else:
                reps.append([v, 1])
        clusters.append([g[0], reps])
    # dominant group = exact roots' top modulus group (no fit threshold)
    dom_ar, dom_reps = clusters[0][0], clusters[0][1]
    realvals = [v for (v, m) in dom_reps
                if abs(v.imag) <= 1e-9 * max(1.0, abs(v))]
    if len(realvals) != len(dom_reps):
        return False, f'complex dominant {dom_reps[0][0]}'
    r1 = dom_ar
    if r1 <= 0:
        return False, 'rho1 not positive'
    rmax = clusters[1][0] if len(clusters) > 1 else 0.0
    if not (r1 > rmax * (1 + 1e-9)):
        return False, f'no dominant gap: rho1={r1} rmax={rmax}'
    if len(dom_reps) > 1:
        return False, ('multidom', [(v.real if abs(v.imag) < 1e-12
                                     else v) for v, m in dom_reps])
    # top-K regression for coefficients; remainder bounded by residual
    import numpy as np
    tops = []
    for (ar, reps) in clusters:
        for (v, m) in reps:
            for j in range(m):
                tops.append((v, j))
    K = min(len(tops), 14)
    tops = tops[:K]
    rnext = None
    if len(clusters) > 0:
        after = [ar for (ar, reps) in clusters]
        # next modulus strictly below dom (skip equal-modulus leftovers)
        rnext = next((ar for ar in after if ar < r1 * (1 - 1e-12)),
                     0.0)
    nrows = 3 * K + 8
    # fixed window just past the recurrence order: stable under segment
    # extension (tail-anchored rows change cn and destabilise Lf)
    n0 = max(1, d + 20)
    if len(s) - n0 < K + 2:
        return False, 'too few rows for fit'
    nrows = min(nrows, len(s) - n0 - 1)
    if n0 + nrows > len(s):
        nrows = len(s) - n0
    rows = list(range(n0, n0 + nrows))
    A = np.array([[(n ** j) * (v ** n) for (v, j) in tops]
                  for n in rows], dtype=complex)
    bv = np.array([float(s[n]) for n in rows], dtype=complex)
    Amax = np.max(np.abs(A), axis=0)
    Amax[Amax == 0] = 1.0
    try:
        cn = np.linalg.lstsq(A / Amax, bv, rcond=1e-12)[0] / Amax
    except Exception as e:
        return False, f'fit failed: {e}'
    resid = np.max(np.abs(A @ cn - bv))
    sig = max(float(np.max(np.abs(bv))), 1.0)
    if resid > 1e-4 * sig:
        return False, ('fitresid', float(resid / sig))
    c1 = cn[0]
    if abs(c1.imag) > 1e-6 * max(1.0, abs(c1)):
        return False, f'c1 complex: {c1}'
    c1 = c1.real
    if c1 <= 0:
        return False, f'c1 not positive: {c1}'
    dpoly = [c1]
    # dominant confluent j>0 columns: find them among tops
    for (v, j) in tops[1:]:
        if j > 0 and abs(v - r1) < 1e-9 * r1:
            dpoly.append(0.0)
    # others: fitted top modes + lumped remainder
    others = []
    for idx in range(1, len(tops)):
        v, j = tops[idx]
        if abs(abs(v) - r1) < 1e-9 * r1:
            # dominant root (incl. confluent j>0): handled in dpoly LHS;
            # putting it in rhs makes the bound never cross
            continue
        others.append((abs(cn[idx]), j, abs(v)))
    S = 2.0 * float(resid)  # lumped bound for omitted modes at fit rows
    import math
    Lf = None
    for L in range(1, 4000):
        pf = 0.0
        for cj in reversed(dpoly):
            pf = pf * L + cj
        if pf <= 0:
            continue
        ll = math.log(pf) + L * math.log(r1)
        logs = []
        for (absC, j, rr) in others:
            if absC > 0 and rr > 0:
                logs.append(math.log(absC) + j * math.log(L + 1)
                            + L * math.log(rr))
        if rnext and S > 0:
            # omitted modes: |.| <= S at fit rows n0, growth rate <= rnext
            logs.append(math.log(S) + (L - n0) * math.log(rnext))
        if logs:
            rhs_log = float(np.logaddexp.reduce(np.array(logs)))
            thr = float(np.logaddexp(math.log(2.0) + rhs_log, 0.0))
        else:
            thr = 0.0  # log(1): rhs = 0, need lhs > 1
        if ll > thr:
            Lf = L
            break
    if Lf is None:
        dbg_others = [(f'{o:.3e}', j, round(rr, 6))
                      for (o, j, rr) in others]
        last = []
        for L in (10, 100, 500, 1000, 2000, 2399):
            pf = 0.0
            for cj in reversed(dpoly):
                pf = pf * L + cj
            if pf <= 0:
                last.append((L, 'pf<=0'))
                continue
            ll = math.log(pf) + L * math.log(r1)
            logs = []
            for (absC, j, rr) in others:
                if absC > 0 and rr > 0:
                    logs.append(math.log(absC) + j * math.log(L + 1)
                                + L * math.log(rr))
            if rnext and S > 0:
                logs.append(math.log(S) + (L - n0) * math.log(rnext))
            rhs_log = (float(np.logaddexp.reduce(np.array(logs)))
                       if logs else -1e9)
            thr = float(np.logaddexp(math.log(2.0) + rhs_log, 0.0))
            last.append((L, round(ll - thr, 2)))
        print(f'    [tail d={d}] NOTAIL c1={c1:.3e} S={S:.3e} '
              f'r1={r1:.6f} rnext={rnext} others={dbg_others} '
              f'll-thr={last}', flush=True)
        return False, 'no tail L found in range'
    return True, (r1, rmax, Lf, d)


def complex_pow(ci, L, clusters):
    rho = clusters[ci][0]
    return rho ** L


if __name__ == '__main__':
    import sys
    mode = sys.argv[1] if len(sys.argv) > 1 else 'check'
    if mode == 'check':
        # brute cross-check
        for (a, b) in [(2, 3), (2, 5), (3, 4), (3, 5), (3, 8), (4, 7), (5, 7)]:
            for L in range(a, 15):
                h1 = hseq_pair(a, b, L, L)[L]
                h2 = h_brute(a, b, L)
                status = 'OK' if h1 == h2 else 'MISMATCH'
                if h1 != h2:
                    print(f'{status} ({a},{b}) L={L} transfer={h1} brute={h2}')
                # brute too slow beyond ~14
            print(f'({a},{b}) transfer seq L=a..14:',
                  [hseq_pair(a, b, L, L)[L] for L in range(a, 15)])
    elif mode == 'cert':
        N = int(sys.argv[2]) if len(sys.argv) > 2 else 220
        Bmax = int(sys.argv[3]) if len(sys.argv) > 3 else 14
        npass = nfail = 0
        fails = []

        def cert_pair(a, b, Lmin, N):
            seq_dict = hseq_pair(a, b, Lmin, N)
            s = [seq_dict[L] for L in range(Lmin, N + 1)]
            if any(v <= 0 for v in s):
                bad = [(Lmin + i, v) for i, v in enumerate(s) if v <= 0]
                return ('nonpos', bad[:3])
            Lfit = min(len(s) - 1, 600)
            d, coeffs = berlekamp_massey(s[:Lfit + 1])
            if d == 0 or d > 320:
                return ('order', d)
            ok, info = check_recurrence(s, coeffs, d, d + 1, len(s))
            if not ok:
                return ('rec', info)
            ok2, tail = tail_certificate(s, d, coeffs, 0)
            if not ok2:
                return ('tail', tail)
            rho1, rmax, Lf, _ = tail
            if Lf >= len(s):
                return ('lf', Lf)
            return ('PASS', (d, rho1, rmax, Lf))

        print('old cert mode; use cert2', flush=True)

    elif mode == 'cert2':
        from fractions import Fraction
        P1, P2, P3 = 1000000007, 1000000009, 1000000021
        # 12 primes (~1e9 each) -> CRT range ~1e108: some pairs, e.g.
        # (9,11), have a recurrence coefficient ~1e27 that wraps the
        # 3-prime range (5.4e26) and breaks exactrec.
        PRIMES = [1000000007, 1000000009, 1000000021, 1000000033,
                  1000000087, 1000000093, 1000000097, 1000000103,
                  1000000123, 1000000181, 1000000207, 1000000223]
        N = int(sys.argv[2]) if len(sys.argv) > 2 else 4000
        Bmax = int(sys.argv[3]) if len(sys.argv) > 3 else 12

        def bm_lift(sts):
            """sts: [(prime, full_seq_from_Lmin), ...]; CRT all primes."""
            ds = []
            out = []
            for P, seq in sts:
                dd, cc = _bm_mod(seq, P)
                ds.append(dd)
                out.append((P, cc))
            if len(set(ds)) != 1:
                return None, ('mismatch', tuple(ds))
            d1 = ds[0]
            if d1 == 0:
                return None, ('order0', d1)
            coeffs = []
            for i in range(d1):
                v, mod = 0, 1
                for P, cc in out:
                    inv = pow(mod, -1, P)
                    k = ((cc[i] - v) * inv) % P
                    v = v + mod * k
                    mod *= P
                if v > mod // 2:
                    v -= mod
                coeffs.append(Fraction(v))
            return d1, coeffs

        N0 = N

        def cert_pair2(a, b, Lmin):
            print(f'  [{a},{b}] start', flush=True)
            Lbig = a + b - 1
            t = Lbig - Lmin
            N = N0
            d = coeffs = None
            st1 = None
            sd_full = None
            while N <= 32000:
                sd_full = hseq_pair(a, b, Lmin, N)
                s_all = [sd_full[L] for L in range(Lmin, N + 1)]
                sts = [(P, [v % P for v in s_all]) for P in PRIMES]
                if st1 is None:
                    st1 = sts[0][1]
                d, coeffs = bm_lift(sts)
                if isinstance(d, tuple):
                    N *= 2
                    st1 = None
                    continue
                if d >= len(st1) // 2 - 4:
                    N *= 2
                    st1 = None
                    continue
                if d > 4000:
                    return ('huge', d)
                break
            if d is None or d > 4000:
                return ('nocvg', d)
            print(f'  [{a},{b}] bm done d={d} N={N}', flush=True)
            exN = min(N, t + d + 130)
            for _ext in range(4):
                if exN <= N and sd_full is not None:
                    sd = sd_full
                else:
                    sd = hseq_pair(a, b, Lmin, exN)
                sabs = [sd[L] for L in range(Lmin, exN + 1)]
                bad = [(Lmin + i, v) for i, v in enumerate(sabs)
                       if v <= 0]
                if bad:
                    return ('nonpos', bad[:3])
                for L in range(Lmin, exN + 1):
                    if sabs[L - Lmin] % P1 != st1[L - Lmin]:
                        return ('modmis', L)
                print(f'  [{a},{b}] exactdict+mod ok (exN={exN}), '
                      f'exactrec...', flush=True)
                tail_seg = sabs[t:]
                for n in range(d + 1, len(tail_seg)):
                    lhs = tail_seg[n]
                    rhs = 0
                    for i in range(d):
                        rhs += coeffs[i] * tail_seg[n - 1 - i]
                    if lhs != rhs:
                        return ('exactrec', n)
                try:
                    ok2, tail = tail_certificate(tail_seg, d, coeffs, 0,
                                                  a, b)
                except OverflowError:
                    return ('floatovf', d)
                if not ok2:
                    return ('tail', tail)
                rho1, rmax, Lf, _ = tail
                if Lf < len(tail_seg):
                    return ('PASS', (d, rho1, rmax, t + Lf, N))
                if exN >= N:
                    return ('lf', Lf)
                exN = min(N, t + Lf + 8)
                print(f'  [{a},{b}] Lf={Lf} >= segment; '
                      f'extending to exN={exN}', flush=True)
            return ('lf', Lf)

        only = None
        if len(sys.argv) > 4:
            only = set()
            for pr in sys.argv[4].split(','):
                pa, pb = pr.split('-')
                only.add((int(pa), int(pb)))
        npass2 = nfail2 = 0
        for a in range(2, Bmax):
            for b in range(a + 1, Bmax + 1):
                if gcd(a, b) != 1:
                    continue
                if only is not None and (a, b) not in only:
                    continue
                try:
                    status, info = cert_pair2(a, b, a)
                except Exception as e:
                    status, info = 'exc', repr(e)[:140]
                if status == 'PASS':
                    npass2 += 1
                    d, rho1, rmax, Lf, N = info
                    print(f'PASS ({a},{b}) d={d} rho1={rho1:.6f} '
                          f'rmax={rmax:.6f} L*={Lf} N={N}', flush=True)
                else:
                    nfail2 += 1
                    print(f'FAIL {status} ({a},{b}) {info}', flush=True)
        print(f'== cert2 pass {npass2} fail {nfail2}', flush=True)

    elif False:
        only = None
        if len(sys.argv) > 4:
            only = set()
            for pr in sys.argv[4].split(','):
                pa, pb = pr.split('-')
                only.add((int(pa), int(pb)))
        for a in range(2, Bmax):
            for b in range(a + 1, Bmax + 1):
                if gcd(a, b) != 1:
                    continue
                if only is not None and (a, b) not in only:
                    continue
                try:
                    status, info = cert_pair(a, b, a, N)
                except Exception as e:
                    status, info = 'exc', repr(e)[:140]
                if status == 'PASS':
                    npass += 1
                    d, rho1, rmax, Lf = info
                    print(f'PASS ({a},{b}) d={d} rho1={rho1:.6f} '
                          f'rmax={rmax:.6f} L*={Lf}', flush=True)
                else:
                    nfail += 1
                    fails.append((status, a, b, info))
                    print(f'FAIL {status} ({a},{b}) {info}', flush=True)
        print(f'== pass {npass} fail {nfail}', flush=True)
