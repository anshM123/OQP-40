"""Stronger Hankel test (K up to 28, several scales) for f(lam) = p_{n,m}(e^{Z+(1-th) lam T}, e^{Z-th lam T}), T_d = 0."""
import mpmath as mp, random, sys
from bmv_p_test import herm, expmh, word_avg, taylor
mp.mp.dps = 80
rng = random.Random(int(sys.argv[1]))
K = 28
for trial in range(int(sys.argv[2])):
    d = [2, 3, 3, 4, 2, 3][trial % 6]
    sz, st = rng.choice([0.3, 1.0, 2.5]), rng.choice([0.3, 1.0, 2.5])
    Z = herm(d, rng, sz); T = herm(d, rng, st)
    ev, U = mp.eighe(Z)
    Tz = U.H * T * U
    for i in range(d): Tz[i, i] = 0
    T = U * Tz * U.H
    n, m = [(1, 1), (2, 1), (2, 2), (3, 2), (1, 3), (3, 3)][trial % 6]
    th = mp.mpf(n) / (n + m)
    f = lambda lam: word_avg(expmh(Z + (1 - th) * lam * T), expmh(Z - th * lam * T), n, m)
    # radius: scale so that coefficients are well resolved
    R = mp.mpf(1) / max(st, 0.5)
    c = taylor(f, K, R)
    mom = [mp.re(c[k]) * mp.factorial(k) for k in range(K + 1)]
    out = []
    for J in (6, 10, 14):
        H = mp.matrix(J + 1, J + 1)
        for i in range(J + 1):
            for j in range(J + 1):
                H[i, j] = mom[i + j]
        Dg = [1 / mp.sqrt(abs(H[i, i])) for i in range(J + 1)]
        for i in range(J + 1):
            for j in range(J + 1):
                H[i, j] *= Dg[i] * Dg[j]
        e = mp.eigsy(H)[0]
        out.append(mp.nstr(min(e[i] for i in range(J + 1)), 4))
    print(f"d={d} (n,m)=({n},{m}) scales Z {sz} T {st}: min eig normalised Hankel J=6,10,14: {out}", flush=True)
