"""Measure form of the lower half of OQP 40 (fixed m, moments in n):
  p_{n,m} = int tau^n dpi'_m,   pi'_m = sum_{i in [d]^m} beta(i) Law(sum_j u_j alpha_{i_j}),  u ~ Dir(1^m)   (>= 0 by D1)
  L_{n,m} = int sigma^n dnu~'_m, nu~'_m = exp-push-forward of the BMV measure of t -> tr e^{mK + tH}   (>= 0, Stahl)
Tests, for random PD pairs (d = 3, m = 3):
  (R) real exponents:  p_{x,m} >= L_{x,m} for real x in [0.25, 6]  (x >= 1 is implied by icx order; x < 1 is not)
  (I) icx order:       int (tau - c)_+ dpi'_m  >=  int (sigma - c)_+ dnu~'_m  for c on a grid.
pi'_m functionals are computed exactly as sums over index cycles of Dirichlet expectations (Monte Carlo over u with a
common sample, 4e5 points); nu~'_m functionals via the identity  int f(sigma) dnu~'_m = sum_k f-weighted ... is not
available in closed form, so (I) uses the representation  nu~'_m = law of exp(T) where T has Laplace transform
tr e^{mK + tH} / tr B^m; we recover int (e^T - c)_+ by numerically inverting through a fine grid of real t moments
(Gauss quadrature on [h_min, h_max] via a nonnegative least squares fit).  (I) is therefore approximate."""
import itertools

import numpy as np
from scipy.optimize import nnls

rng = np.random.default_rng(31)


def hfun(M, f):
    w, V = np.linalg.eigh(M)
    return (V * f(w)) @ V.conj().T


def setup(d, spread):
    X = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))
    Hh = (X + X.conj().T) / 2
    H = np.diag(np.sort(rng.uniform(-spread, spread, size=d)))
    K = hfun(Hh * spread / np.linalg.norm(Hh, 2), lambda w: w)
    return H, K


def pi_functional(alpha, B, m, f, U):
    """sum_i beta(i) E_u f(sum_j u_j alpha_{i_j}); U: Dirichlet samples (S, m)."""
    d = len(alpha)
    tot = 0.0
    for idx in itertools.product(range(d), repeat=m):
        beta = 1.0 + 0j
        for j in range(m):
            beta *= B[idx[j], idx[(j + 1) % m]]
        if abs(beta) < 1e-300:
            continue
        x = U @ alpha[list(idx)]
        tot += (beta * np.mean(f(x))).real
    return tot


worst_R = {}
for trial in range(40):
    d, m = 3, 3
    H, K = setup(d, float(rng.choice([0.5, 1.0, 2.0])))
    alpha = np.exp(np.diag(H).real)
    B = hfun(K, np.exp)                      # A = diag(alpha) is diagonal, so B is in A's eigenbasis
    U = rng.dirichlet(np.ones(m), size=400000)
    for x in [0.25, 0.5, 0.75, 1.0, 1.5, 2.0, 3.0, 4.5, 6.0]:
        p = pi_functional(alpha, B, m, lambda t: t ** x, U)
        L = np.sum(np.exp(np.linalg.eigvalsh(x * H + m * K)))
        worst_R[x] = min(worst_R.get(x, np.inf), p / L)
print("(R) min over 40 cases of p_{x,3}/L_{x,3} by real exponent x:")
for x, v in worst_R.items():
    print(f"   x = {x:4.2f}: {v:.6f}")
