"""Careful check of the 2x2 second-order formula on the (C^{1,1}) TF kernel: larger e with Richardson extrapolation,
and the sphere integral computed on a fine grid of sub-intervals (Gauss-Legendre per cell), double precision ok."""
import numpy as np
from numpy.polynomial.legendre import leggauss

def make(th, u0):
    N0 = 1 / th
    lv = lambda a, b: th * np.log(a) + (1 - th) * np.log(b)
    def g(v):
        return np.where(v > u0, (np.exp(N0 * v) - (N0 + 1) * np.exp(N0 * u0) + N0 * np.exp((N0 + 1) * u0 - v)) / (N0 * (N0 + 1)), 0.0)
    def dg(v):
        return np.where(v > u0, (np.exp(N0 * v) - np.exp((N0 + 1) * u0 - v)) / (N0 + 1), 0.0)
    def d2g(v):
        return np.where(v > u0, (N0 * np.exp(N0 * v) + np.exp((N0 + 1) * u0 - v)) / (N0 + 1), 0.0)
    F = lambda a, b: g(lv(a, b))
    dF = lambda a, b: (dg(lv(a, b)) * th / a, dg(lv(a, b)) * (1 - th) / b)
    Fab = lambda a, b: d2g(lv(a, b)) * th * (1 - th) / (a * b)
    return F, dF, Fab

xg, wg = leggauss(12)
def sphere_pairing(F, dF, a1, a2, b1, b2, e, n_p=400, n_c=400):
    a0, az = (a1 + a2) / 2, (a1 - a2) / 2
    b0, bz = (b1 + b2) / 2, (b1 - b2) / 2
    pe = np.linspace(0, np.pi, n_p + 1); ce = np.linspace(0, 2 * np.pi, n_c + 1)
    P = ((pe[:-1, None] + pe[1:, None]) / 2 + (pe[1:, None] - pe[:-1, None]) / 2 * xg[None, :]).ravel()
    Wp = ((pe[1:, None] - pe[:-1, None]) / 2 * wg[None, :]).ravel()
    Cc = ((ce[:-1, None] + ce[1:, None]) / 2 + (ce[1:, None] - ce[:-1, None]) / 2 * xg[None, :]).ravel()
    Wc = ((ce[1:, None] - ce[:-1, None]) / 2 * wg[None, :]).ravel()
    pp, cc = np.meshgrid(P, Cc, indexing='ij')
    W = np.outer(Wp, Wc)
    nz, nx = np.cos(pp), np.sin(pp) * np.cos(cc)
    da = az * nz; db = bz * (np.cos(2 * e) * nz + np.sin(2 * e) * nx)
    a, b = a0 + da, b0 + db
    Fa, Fb = dF(a, b)
    val = (F(a, b) + Fa * da + Fb * db) * np.sin(pp)
    return 2 * np.sum(val * W) / (4 * np.pi)

def segment_formula(Fab, a1, a2, b1, b2):
    u = np.linspace(0, 1, 200001); a = a2 + u * (a1 - a2); b = b2 + u * (b1 - b2)
    f = Fab(a, b)
    return -2 * (a1 - a2) * (b1 - b2) * np.trapezoid(f, u)

a1, a2, b1, b2 = 2.3, 0.7, 0.5, 1.9
th = 0.3
for off in (-0.4, -0.1, 0.0):
    u0 = th * np.log(a2) + (1 - th) * np.log(b2) + off
    F, dF, Fab = make(th, u0)
    v0 = sphere_pairing(F, dF, a1, a2, b1, b2, 0.0)
    ests = []
    for e in (0.04, 0.02, 0.01):
        d2 = (sphere_pairing(F, dF, a1, a2, b1, b2, e) - 2 * v0 + sphere_pairing(F, dF, a1, a2, b1, b2, -e)) / e ** 2
        ests.append(d2)
    rich = [(4 * ests[i + 1] - ests[i]) / 3 for i in range(2)]
    print(f"offset {off}: second differences (e=.04,.02,.01) {[round(v, 6) for v in ests]}; Richardson {[round(v, 6) for v in rich]}; formula {segment_formula(Fab, a1, a2, b1, b2):.6f}")
