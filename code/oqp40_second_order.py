"""Second-order (near-commuting) test of the lower half of OQP 40:  p_{n,m}(A,B) >= tr exp(n log A + m log B).

Take A = diag(a), B = exp(diag(k) + eps V), V Hermitian with zero diagonal. To order eps^2 the difference splits
into independent 2x2 pieces, one per pair {i,j}. With b = e^k, E(x,y) = (e^x-e^y)/(x-y),
F(x,y) = d/dx E(x,y) (second divided difference f[x,y,x] of exp), and x_i = n log a_i + m k_i, the coefficient of
|v_ij|^2 eps^2 in p - L is
  Delta = m [a_i^n b_i^{m-1} F(k_i,k_j) + a_j^n b_j^{m-1} F(k_j,k_i)]
        + m(m-1) E(k_i,k_j)^2 int_0^1 (th a_i + (1-th) a_j)^n (th b_i + (1-th) b_j)^{m-2} dth
        - m^2 E(x_i,x_j).
The script checks this formula against a direct 2x2 computation and then minimises Delta / scale over the pair data."""
from math import comb

import numpy as np
from scipy.integrate import quad
from scipy.linalg import expm
from scipy.optimize import minimize

rng = np.random.default_rng(11)


def E(x, y):
    return np.exp(x) if abs(x - y) < 1e-12 else (np.exp(x) - np.exp(y)) / (x - y)


def F(x, y):
    if abs(x - y) < 1e-6:
        return np.exp(x) / 2
    return (np.exp(x) * (x - y) - (np.exp(x) - np.exp(y))) / (x - y) ** 2


def delta(n, m, ai, aj, ki, kj):
    bi, bj = np.exp(ki), np.exp(kj)
    first = m * (ai ** n * bi ** (m - 1) * F(ki, kj) + aj ** n * bj ** (m - 1) * F(kj, ki))
    integ = quad(lambda th: (th * ai + (1 - th) * aj) ** n * (th * bi + (1 - th) * bj) ** (m - 2), 0, 1,
                 epsabs=1e-14, epsrel=1e-13)[0] if m >= 2 else 0.0
    second = m * (m - 1) * E(ki, kj) ** 2 * integ
    xi, xj = n * np.log(ai) + m * ki, n * np.log(aj) + m * kj
    return first + second - m * m * E(xi, xj)


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


def direct(n, m, ai, aj, ki, kj, eps=1e-4):
    A = np.diag([ai, aj]).astype(complex)
    V = np.array([[0, 1], [1, 0]], dtype=complex)
    vals = []
    for e in (eps, -eps):
        K = np.diag([ki, kj]) + e * V
        B = expm(K)
        L = np.trace(expm(n * np.diag(np.log([ai, aj])) + m * K)).real
        vals.append(word_average(A, B, n, m) - L)
    return (vals[0] + vals[1]) / 2 / eps ** 2        # p - L is even in eps; zero at eps = 0


print("formula vs direct 2x2 (coefficient of eps^2 per unordered pair; |v|=1):")
for _ in range(6):
    n, m = int(rng.integers(1, 6)), int(rng.integers(2, 6))
    ai, aj = np.exp(rng.normal(size=2))
    ki, kj = rng.normal(size=2)
    print(f"  (n,m)=({n},{m}) formula {delta(n, m, ai, aj, ki, kj):+.6e}  direct {direct(n, m, ai, aj, ki, kj):+.6e}")

print("minimise Delta / (m^2 E(x_i,x_j)) over pair data (scale-free):")
for n, m in [(1, 2), (2, 2), (3, 3), (2, 5), (5, 2), (4, 4), (5, 5), (6, 3), (3, 6), (8, 8)]:
    best = np.inf
    for r in range(60):
        x0 = rng.normal(scale=rng.choice([0.5, 2, 6]), size=4)
        f = lambda x: delta(n, m, np.exp(x[0]), np.exp(x[1]), x[2], x[3]) / (
            m * m * E(n * x[0] + m * x[2], n * x[1] + m * x[3]))
        res = minimize(f, x0, method="Nelder-Mead", options={"maxiter": 4000, "xatol": 1e-10, "fatol": 1e-14})
        best = min(best, res.fun)
    print(f"  (n,m)=({n},{m}): min relative second-order gap {best:+.4e}", flush=True)
