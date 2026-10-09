"""Is the word-average functional L(tau^n s^m) = A_{n,m}(A,B) a positive functional (moments of a positive
measure on R^2)? Test: the moment matrix M[(n,m),(n',m')] = A_{n+n',m+m'}(A,B) over monomials of bidegree <= (k,k)
must be positive semidefinite if L comes from a positive measure. For commuting pairs it does (joint spectral
measure). DINH.md (reading of D5) calls the comparison of L for (A,B) and (A,E_A(B)) a 'convex order'.

Exact rational arithmetic for the decisive cases (sign of a quadratic form value).
usage: python c6_moment_matrix.py SEED
"""
import sys
from math import comb

import numpy as np
from flint import fmpq, fmpq_mat

rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 5)


def word_avgs(A, B, Nmax):
    d = A.shape[0]
    out = {(0, 0): float(d)}
    coeffs = [np.eye(d)]
    for N in range(1, Nmax + 1):
        new = [np.zeros((d, d)) for _ in range(N + 1)]
        for j, C in enumerate(coeffs):
            new[j] += C @ A
            new[j + 1] += C @ B
        coeffs = new
        for m in range(N + 1):
            out[(N - m, m)] = np.trace(coeffs[m]) / comb(N, m)
    return out


def word_avgs_exact(A, B, Nmax):
    d = A.nrows()
    I = fmpq_mat(d, d, [1 if i == j else 0 for i in range(d) for j in range(d)])
    tr = lambda M: sum((M[i, i] for i in range(d)), fmpq(0))
    out = {(0, 0): fmpq(d)}
    coeffs = [I]
    for N in range(1, Nmax + 1):
        new = [None] * (N + 1)
        for j, C in enumerate(coeffs):
            CA, CB = C * A, C * B
            new[j] = CA if new[j] is None else new[j] + CA
            new[j + 1] = CB if new[j + 1] is None else new[j + 1] + CB
        coeffs = new
        for m in range(N + 1):
            out[(N - m, m)] = tr(coeffs[m]) / comb(N, m)
    return out


def main():
    k = 2
    monos = [(n, m) for n in range(k + 1) for m in range(k + 1)]
    worst = (np.inf, None)
    for trial in range(3000):
        d = int(rng.integers(2, 4))
        X = rng.integers(-3, 4, size=(d, d)); A = (X @ X.T).astype(float)      # PSD integer
        Y = rng.integers(-3, 4, size=(d, d)); B = (Y @ Y.T).astype(float)
        if np.allclose(A @ B, B @ A):
            continue
        wa = word_avgs(A, B, 4 * k)
        M = np.array([[wa[(a[0] + b[0], a[1] + b[1])] for b in monos] for a in monos])
        ev, V = np.linalg.eigh(M)
        rel = ev[0] / ev[-1]
        if rel < worst[0]:
            worst = (rel, (A.astype(int), B.astype(int), V[:, 0]))
    rel, (A, B, v) = worst
    print(f"smallest eigenvalue / largest eigenvalue of the (bidegree<={k}) moment matrix over 3000 integer PSD pairs: "
          f"{rel:.3e}")
    # exact certificate: evaluate L(p^2) for a rational p close to the eigenvector
    Aq = fmpq_mat(A.shape[0], A.shape[0], [int(x) for x in A.flatten()])
    Bq = fmpq_mat(B.shape[0], B.shape[0], [int(x) for x in B.flatten()])
    wa = word_avgs_exact(Aq, Bq, 4 * k)
    coef = [fmpq(int(round(c * 10 ** 6)), 10 ** 6) for c in v]
    val = fmpq(0)
    for i, a in enumerate(monos):
        for j, b in enumerate(monos):
            val += coef[i] * coef[j] * wa[(a[0] + b[0], a[1] + b[1])]
    print(f"exact L(p^2) for the rationalised eigenvector p: {float(val):.6e}  (negative => L is not a positive functional)")
    print("A =", A.tolist(), " B =", B.tolist())
    print("p coefficients over monomials tau^n s^m", monos, "=", [str(c) for c in coef])


if __name__ == "__main__":
    main()
