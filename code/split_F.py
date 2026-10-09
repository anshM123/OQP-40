"""Test the split of conjecture (F) through the continuous-Dirichlet intermediate
    P_cont = (d/ds)^m tr exp(n log A + s B) |_{s=0}  (= E_{u~Dir(1^m)} tr prod_j (B A^{n u_j})):
  (F1)  p_{n,m}(A,B) >= P_cont,      (F2)  P_cont >= tr (A^{n/m} B)^m.
Also cross-checks P_cont against a Monte Carlo Dirichlet average. Random PD pairs, near-singular pairs, Cha-Lee."""
from math import comb, factorial

import numpy as np
from scipy.linalg import expm

rng = np.random.default_rng(5)


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


def hfun(A, f):
    w, V = np.linalg.eigh(A)
    return (V * f(w)) @ V.conj().T


def p_cont(A, B, n, m, K=96):
    H = hfun(A, np.log)
    r = 0.5 / max(np.linalg.norm(B, 2), 1e-300)
    s = r * np.exp(2j * np.pi * np.arange(K) / K)
    vals = np.array([np.trace(expm(n * H + sk * B)) for sk in s])
    cm = np.sum(vals * np.exp(-2j * np.pi * np.arange(K) * m / K)) / K / r ** m
    return (factorial(m) * cm).real


def p_cont_mc(A, B, n, m, samples=20000):
    w, V = np.linalg.eigh(A)
    tot = 0.0
    u = rng.dirichlet(np.ones(m), size=samples)
    for uu in u:
        M = np.eye(A.shape[0], dtype=complex)
        for j in range(m):
            M = M @ B @ ((V * w ** (n * uu[j])) @ V.conj().T)
        tot += np.trace(M).real
    return tot / samples


def frac(A, B, n, m):
    S = hfun(A, lambda w: np.maximum(w, 0) ** (n / (2 * m)))
    return np.sum(np.maximum(np.linalg.eigvalsh(S @ B @ S), 0) ** m)


def rand_pd(d, spread):
    X = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))
    Hh = (X + X.conj().T) / 2
    return hfun(Hh * spread / np.linalg.norm(Hh, 2), np.exp)


A, B = rand_pd(3, 1.0), rand_pd(3, 1.0)
print("P_cont: Cauchy-FFT vs Monte Carlo:", p_cont(A, B, 3, 3), p_cont_mc(A, B, 3, 3))

worst1, worst2 = np.inf, np.inf
for trial in range(400):
    d = int(rng.integers(2, 5))
    spread = float(rng.choice([0.3, 1.0, 2.0, 4.0]))
    A, B = rand_pd(d, spread), rand_pd(d, spread)
    n, m = int(rng.integers(1, 7)), int(rng.integers(2, 7))
    p, pc, fr = word_average(A, B, n, m), p_cont(A, B, n, m), frac(A, B, n, m)
    worst1, worst2 = min(worst1, p / pc), min(worst2, pc / fr)
print(f"random PD (400 cases): min p/P_cont = {worst1:.6f}   min P_cont/frac = {worst2:.6f}")

for x in [0.3, 0.1, 0.03]:
    d = 1e-9
    A = np.array([[1, 0, 0], [0, x, -x], [0, -x, x]], dtype=complex) + d * np.eye(3)
    B = np.array([[x, -x, 0], [-x, x, 0], [0, 0, 1]], dtype=complex) + d * np.eye(3)
    for n, m in [(3, 3), (5, 5), (4, 6)]:
        p, pc, fr = word_average(A, B, n, m), p_cont(A, B, n, m), frac(A, B, n, m)
        print(f"Cha-Lee x={x} (n,m)=({n},{m}): p={p:.4e}  P_cont={pc:.4e}  frac={fr:.4e}  "
              f"p/P_cont={p / pc:.4f}  P_cont/frac={pc / fr:.4f}")
