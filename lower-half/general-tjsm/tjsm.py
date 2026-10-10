"""Tracial joint spectral measure (Heinavaara, arXiv:2310.03227) for PD pairs, numerically.

mu_{A,B} >= 0 on R^2 with  tr H(f)(xA+yB) = int f(ax+by) dmu,  H(f)(x) = int_0^1 (1-t)/t f(xt) dt.
For f = t^N: H(f) = t^N/(N(N+1)), so the word average p_{n,m} = N(N+1) int a^n b^m dmu  (N = n+m).
mu = mu_s + mu_c:
  mu_s = sum_{v in E(A^{-1}B)} int_0^1 (1-t)/t delta_{t(<Av,v>, <Bv,v>)} dt   (unit eigenvectors v)
  dmu_c/dm2 = c0 * sum_i |Im lambda_i(C1(a,b))|,  C1 = (I - (aA+bB)/(a^2+b^2)) (bA - aB)^{-1};  c0 calibrated below.
Polar coordinates (a,b) = r(cos phi, sin phi), phi in (0, pi/2) for PD A, B.
"""
import numpy as np


def word_avg(A, B, n, m):
    d = A.shape[0]
    P = [np.eye(d, dtype=complex)]
    for _ in range(n + m):
        Q = [np.zeros((d, d), dtype=complex) for _ in range(len(P) + 1)]
        for j, C in enumerate(P):
            Q[j] = Q[j] + C @ A
            Q[j + 1] = Q[j + 1] + C @ B
        P = Q
    from math import comb
    return np.trace(P[m]).real / comb(n + m, m)


def singular_points(A, B):
    w, V = np.linalg.eig(np.linalg.solve(A, B))
    pts = []
    for k in range(V.shape[1]):
        v = V[:, k] / np.linalg.norm(V[:, k])
        pts.append(((v.conj() @ A @ v).real, (v.conj() @ B @ v).real))
    return pts


def density_polar(A, B, r, phi):
    """r * dmu_c/dm2 at (r cos phi, r sin phi), without the constant c0 (i.e. sum |Im lambda|)."""
    c, s = np.cos(phi), np.sin(phi)
    a, b = r * c, r * s
    C1 = (np.eye(A.shape[0]) - (a * A + b * B) / (r * r)) @ np.linalg.inv(b * A - a * B)
    lam = np.linalg.eigvals(C1)
    return r * np.sum(np.abs(lam.imag))
