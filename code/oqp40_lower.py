"""Adversarial search on the LOWER half of IQOQI Open Quantum Problem 40 (Hagele; formal-conjectures issue #3457):

    p_{n,m}(A,B) >= tr exp(n log A + m log B)      for A, B > 0,

where p_{n,m} = A_{n,m} is the average of tr W over the C(n+m,n) words with n letters A and m letters B.
The ratio is invariant under A -> aA, B -> bB, so we minimise
    f = log p_{n,m}(A,B) - log tr exp(n log A + m log B)
over A = U diag(e^alpha) U^*, B = diag(e^beta), U = exp(skew-Hermitian). f < 0 is a counterexample.

Usage: python oqp40_lower.py SEED [d] [n] [m]"""
import sys
from math import comb

import numpy as np
from scipy.linalg import expm, logm
from scipy.optimize import minimize

seed = int(sys.argv[1]) if len(sys.argv) > 1 else 0
rng = np.random.default_rng(seed)


def word_average(A, B, n, m):
    d = A.shape[0]
    coeffs = [np.eye(d, dtype=complex)]
    for _ in range(n + m):
        new = [np.zeros((d, d), dtype=complex) for _ in range(len(coeffs) + 1)]
        for j, C in enumerate(coeffs):
            new[j] += C @ A
            new[j + 1] += C @ B
        coeffs = new
    return np.trace(coeffs[m]).real / comb(n + m, n)


def unpack(x, d):
    alpha, beta = x[:d], x[d:2 * d]
    S = np.zeros((d, d), dtype=complex)
    iu = np.triu_indices(d, 1)
    k = len(iu[0])
    S[iu] = x[2 * d:2 * d + k] + 1j * x[2 * d + k:2 * d + 2 * k]
    S = S - S.conj().T
    U = expm(S)
    A = U @ np.diag(np.exp(alpha)) @ U.conj().T
    B = np.diag(np.exp(beta)).astype(complex)
    return A, B, alpha, beta, U


def objective(x, d, n, m):
    A, B, alpha, beta, U = unpack(x, d)
    p = word_average(A, B, n, m)
    logA = U @ np.diag(alpha) @ U.conj().T
    logB = np.diag(beta)
    lb = np.trace(expm(n * logA + m * logB)).real
    if p <= 0:
        return -50.0                   # would refute BMV itself; flag loudly
    return np.log(p) - np.log(lb)


def run(d, n, m, restarts=40):
    best = (np.inf, None)
    k = d * (d - 1) // 2
    for r in range(restarts):
        spread = rng.choice([0.5, 2.0, 5.0, 10.0])
        x0 = np.concatenate([rng.normal(scale=spread, size=2 * d), rng.normal(scale=1.0, size=2 * k)])
        res = minimize(objective, x0, args=(d, n, m), method="Nelder-Mead",
                       options={"maxiter": 4000 * (2 * d + 2 * k), "xatol": 1e-10, "fatol": 1e-14})
        res = minimize(objective, res.x, args=(d, n, m), method="BFGS", options={"gtol": 1e-12})
        if res.fun < best[0]:
            best = (res.fun, res.x)
    return best


if __name__ == "__main__":
    cases = [(2, 3, 3), (3, 3, 3), (2, 4, 4), (3, 4, 4), (3, 3, 5), (3, 5, 5), (4, 3, 3), (4, 4, 4), (3, 2, 6)]
    if len(sys.argv) > 4:
        cases = [(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]))]
    for d, n, m in cases:
        fbest, xbest = run(d, n, m)
        print(f"d={d} (n,m)=({n},{m}): min log-ratio {fbest:+.3e}", flush=True)
        if fbest < -1e-9:
            A, B, *_ = unpack(xbest, d)
            np.set_printoptions(precision=6, linewidth=160)
            print("  COUNTEREXAMPLE CANDIDATE\n  A =\n", A, "\n  B =\n", B, flush=True)
