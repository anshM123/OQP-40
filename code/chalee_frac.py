"""(F) p_{n,m}(A,B) >= tr (A^{n/m} B)^m on the Cha-Lee family and on random singular / near-rank-one families
(high precision, mpmath)."""
import random
from math import comb

import mpmath as mp

mp.mp.dps = 50


def word_average(A, B, n, m):
    d = A.rows
    coeffs = [mp.eye(d)]
    for _ in range(n + m):
        new = [mp.zeros(d, d) for _ in range(len(coeffs) + 1)]
        for j, C in enumerate(coeffs):
            new[j] += C * A
            new[j + 1] += C * B
        coeffs = new
    return mp.re(sum(coeffs[m][i, i] for i in range(d))) / comb(n + m, n)


def psd_pow(A, a):
    E, Q = mp.eighe(A) if A.__class__ is not mp.matrix else (None, None)
    return None


def hpow(A, a):
    E, Q = mp.eighe(A)
    return Q * mp.diag([max(mp.re(e), 0) ** a if mp.re(e) > 0 else 0 for e in E]) * Q.transpose_conj()


def frac(A, B, n, m):
    S = hpow(A, mp.mpf(n) / (2 * m))
    M = S * B * S
    E, _ = mp.eighe((M + M.transpose_conj()) / 2)
    return sum(max(mp.re(e), 0) ** m for e in E)


def report(tag, A, B, cases):
    worst = None
    for n, m in cases:
        p = word_average(A, B, n, m)
        f = frac(A, B, n, m)
        g = frac(B, A, m, n)
        r = min(p / f if f > 0 else mp.inf, p / g if g > 0 else mp.inf)
        worst = r if worst is None else min(worst, r)
    print(f"{tag}: min over (n,m) of p / max-side frac bound = {mp.nstr(worst, 10)}", flush=True)
    return worst


cases = [(3, 3), (3, 4), (4, 4), (5, 5), (3, 6), (5, 7), (6, 6)]
for x in ["0.3", "0.1", "0.01", "0.001", "1e-5"]:
    x = mp.mpf(x)
    A = mp.matrix([[1, 0, 0], [0, x, -x], [0, -x, x]])
    B = mp.matrix([[x, -x, 0], [-x, x, 0], [0, 0, 1]])
    report(f"Cha-Lee x={mp.nstr(x, 3)}", A, B, cases)

random.seed(3)


def rnd_unit(d):
    v = mp.matrix([mp.mpc(random.gauss(0, 1), random.gauss(0, 1)) for _ in range(d)])
    return v / mp.norm(v)


overall = mp.inf
for trial in range(60):
    d = random.choice([3, 4])
    eps = mp.mpf(10) ** (-random.choice([1, 2, 3, 4]))
    # A, B = sums of a few weighted rank-one projectors, weights spanning several scales (singular-ish)
    def rank_sum(k):
        M = mp.zeros(d, d)
        for _ in range(k):
            v = rnd_unit(d)
            w = eps ** random.choice([0, 1, 2])
            M += w * (v * v.transpose_conj())
        return M
    A, B = rank_sum(random.choice([1, 2, 3])), rank_sum(random.choice([1, 2, 3]))
    r = report(f"trial {trial} d={d} eps={mp.nstr(eps, 2)}", A, B, [(3, 3), (3, 4), (4, 5), (5, 5)])
    overall = min(overall, r)
print("overall min ratio (random singular families):", mp.nstr(overall, 10))
