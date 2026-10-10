"""Conjecture M: for fixed m >= 1, n -> p_{n,m}/L_{n,m} is nondecreasing (n >= 0).  Exact word averages, float64."""
import sys
import numpy as np
from math import comb

def word_avgs_all(A, B, Nmax):
    """p[n][m] for n+m <= Nmax via the coefficient recursion of (sA + tB)^N."""
    d = A.shape[0]
    P = {(0, 0): np.eye(d, dtype=complex)}
    out = {}
    for N in range(1, Nmax + 1):
        Q = {}
        for (n, m), C in P.items():
            Q[(n + 1, m)] = Q.get((n + 1, m), 0) + C @ A
            Q[(n, m + 1)] = Q.get((n, m + 1), 0) + C @ B
        P = Q
        for (n, m), C in P.items():
            out[(n, m)] = np.trace(C).real / comb(n + m, m)
    return out

def Lval(LA, LB, n, m):
    return np.sum(np.exp(np.linalg.eigvalsh(n * LA + m * LB)))

def logm_h(X):
    w, V = np.linalg.eigh(X)
    return (V * np.log(w)) @ V.conj().T

if __name__ == '__main__':
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 0
    rng = np.random.default_rng(seed)
    def rand_pd(d, spread):
        X = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))
        Q, _ = np.linalg.qr(X)
        return (Q * np.exp(spread * rng.normal(size=d))) @ Q.conj().T
    Nmax = 12
    worst = {}
    for trial in range(400):
        d = int(rng.integers(2, 6)); sp = float(rng.choice([0.3, 1.0, 2.0, 3.0]))
        A, B = rand_pd(d, sp), rand_pd(d, sp)
        LA, LB = logm_h(A), logm_h(B)
        p = word_avgs_all(A, B, Nmax)
        for m in range(1, 6):
            r_prev = 1.0
            for n in range(1, Nmax - m + 1):
                r = p[(n, m)] / Lval(LA, LB, n, m)
                step = np.log(r) - np.log(r_prev)
                key = m
                if key not in worst or step < worst[key][0]:
                    worst[key] = (step, n, d, sp, trial)
                r_prev = r
    for m in sorted(worst):
        print(f"m={m}: min step log(r_n/r_(n-1)) = {worst[m][0]: .3e} at n={worst[m][1]} (d={worst[m][2]}, spread={worst[m][3]}, trial {worst[m][4]})")
