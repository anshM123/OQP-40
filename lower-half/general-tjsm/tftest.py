"""Conjecture TF(theta): with N0 = 1/min(theta, 1-theta), for all u:
   T(u) := int_{v>u} e^{N0 v} d(mu^theta - kappa^theta)(v) >= 0.
At u = -inf, T = [p_{x0,y0} - L_{x0,y0}] / (N0(N0+1)) at the point with min exponent 1 (Golden-Thompson).
TF(theta) => p >= L at every point of the ray with N >= N0."""
import sys
import numpy as np
from tailtest import radial_tables, logm_h
from tjsm import singular_points

def kappa_tilted_tail(us, zeta, N0):
    # int_{v>u} e^{N0 v} k(v - z) dv, k(w) = (1 - e^w)_+  (w < 0)
    out = np.zeros_like(us)
    for z in zeta:
        lo = np.minimum(us, z)
        # int_lo^z e^{N0 v}(1 - e^{v-z}) dv = [e^{N0 v}/N0 - e^{(N0+1)v - z}/(N0+1)]_lo^z
        val = (np.exp(N0 * z) / N0 - np.exp(N0 * z) / (N0 + 1)) - (np.exp(N0 * lo) / N0 - np.exp((N0 + 1) * lo - z) / (N0 + 1))
        out += np.where(us < z, val, 0.0)
    return out

def tf_curve(A, B, th, PHI, R, MASS, pts, ngrid=3000):
    N0 = 1.0 / min(th, 1 - th)
    ell = np.log(R) + th * np.log(np.cos(PHI)) + (1 - th) * np.log(np.sin(PHI))
    zS = np.array([th * np.log(a) + (1 - th) * np.log(b) for a, b in pts])
    zeta = np.linalg.eigvalsh(th * logm_h(A) + (1 - th) * logm_h(B))
    lo = min(zeta.min(), zS.min(), ell.min()) - 15.0
    hi = max(zeta.max(), zS.max(), ell.max()) + 0.1
    us = np.linspace(lo, hi, ngrid)
    wc = MASS * np.exp(N0 * ell)
    order = np.argsort(ell); es, ws = ell[order], wc[order]
    tail = np.concatenate([np.cumsum(ws[::-1])[::-1], [0.0]])
    Tc = tail[np.searchsorted(es, us, side='right')]
    Ts = kappa_tilted_tail(us, zS, N0)
    Tk = kappa_tilted_tail(us, zeta, N0)
    return us, Tc + Ts - Tk, Tk, N0

if __name__ == '__main__':
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 0
    rng = np.random.default_rng(seed)
    def rand_pd(d, spread):
        X = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))
        Q, _ = np.linalg.qr(X)
        return (Q * np.exp(spread * rng.normal(size=d))) @ Q.conj().T
    for trial in range(10):
        d = [2, 2, 3, 3, 4, 4, 5, 3, 4, 3][trial]; sp = [1, 2, 1, 2, 1, 2, 1, 3, 3, 0.5][trial]
        A, B = rand_pd(d, sp), rand_pd(d, sp)
        PHI, R, MASS = radial_tables(A, B, 400, 200)
        pts = singular_points(A, B)
        res = []
        for th in (0.5, 1/3, 0.25, 0.2):
            us, T, Tk, N0 = tf_curve(A, B, th, PHI, R, MASS, pts)
            k = np.argmin(T / np.maximum(Tk, 1e-300))
            res.append(f"th={th:.3f}: min T/Tk={T[k]/Tk[k]: .2e} (u={us[k]:.2f}); T(-inf)/Tk={T[0]/Tk[0]: .2e}")
        print(f"[d={d} sp={sp}] " + " | ".join(res), flush=True)
