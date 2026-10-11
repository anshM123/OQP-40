"""General-d lens test.  Lambda(u) := <Pi, 1[l > u]> = m(u) - m'(u), m = density of mu^theta (l-marginal of
Heinavaara's measure).  2x2 lens lemma: Lambda(u) <= #{zeta_i > u} for u in (v_min, v_max).
Here: m(u) = sum_v k(u - z_v) [pencil part] + m_c(u),  m_c(u) = int dphi rho~(u - c(phi), phi),
rho~(t, phi) = (1/2pi) r * density_polar(A,B,r,phi), r = e^t, c(phi) = th log cos phi + (1-th) log sin phi."""
import os
import sys
import numpy as np
from scipy import integrate
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'general-tjsm'))
from tjsm import density_polar, singular_points

def fun(M, f):
    w, V = np.linalg.eigh((M + M.conj().T) / 2); return (V * f(w)) @ V.conj().T

def rand_pd(d, spread, rng):
    X = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))
    Q, _ = np.linalg.qr(X)
    return (Q * np.exp(spread * rng.normal(size=d))) @ Q.conj().T

def setup(A, B, th):
    d = A.shape[0]
    pencil = np.sort(np.linalg.eigvals(np.linalg.solve(A, B)).real)
    phis = np.arctan(pencil)                     # extreme directions of W
    zeta = np.linalg.eigvalsh(th * fun(A, np.log) + (1 - th) * fun(B, np.log))
    pts = singular_points(A, B)
    zv = np.array([th * np.log(a) + (1 - th) * np.log(b) for a, b in pts])
    return d, phis, zeta, zv

def m_c(u, A, B, th, phis):
    d = A.shape[0]
    def integrand(phi):
        c, s = np.cos(phi), np.sin(phi)
        Cp = c * A + s * B
        ev = np.linalg.eigvalsh(Cp)
        t = u - (th * np.log(c) + (1 - th) * np.log(s))
        r = np.exp(t)
        if r <= ev[0] or r >= ev[-1]:
            return 0.0
        return r * density_polar(A, B, r, phi) / (2 * np.pi)
    edges = list(phis)
    val = 0.0
    for lo, hi in zip(edges[:-1], edges[1:]):
        v, _ = integrate.quad(integrand, lo, hi, limit=400, epsabs=1e-12, epsrel=1e-10)
        val += v
    return val

def m_total(u, A, B, th, phis, zv):
    return np.sum(np.where(zv > u, 1 - np.exp(u - zv), 0.0)) + m_c(u, A, B, th, phis)

if __name__ == '__main__':
    seed = int(sys.argv[1]); rng = np.random.default_rng(seed)
    th = float(sys.argv[2]) if len(sys.argv) > 2 else 0.5
    for trial in range(int(sys.argv[3]) if len(sys.argv) > 3 else 3):
        d = [2, 3, 3, 4][trial % 4]; sp = [0.6, 0.8, 1.2, 0.7][trial % 4]
        A, B = rand_pd(d, sp, rng), rand_pd(d, sp, rng)
        d, phis, zeta, zv = setup(A, B, th)
        # v_min, v_max over W: scan unit vectors
        X = rng.normal(size=(20000, d)) + 1j * rng.normal(size=(20000, d)); X /= np.linalg.norm(X, axis=1, keepdims=True)
        la = np.einsum('ij,jk,ik->i', X.conj(), A, X).real; lb = np.einsum('ij,jk,ik->i', X.conj(), B, X).real
        lv = th * np.log(la) + (1 - th) * np.log(lb)
        vmin, vmax = lv.min(), lv.max()
        us = np.linspace(vmin + 0.02 * (vmax - vmin), vmax - 0.02 * (vmax - vmin), 41)
        h = 1e-3 * (vmax - vmin)
        worst = -np.inf; out = []
        for u in us:
            m0 = m_total(u, A, B, th, phis, zv)
            mp_ = m_total(u + h, A, B, th, phis, zv); mm_ = m_total(u - h, A, B, th, phis, zv)
            Lam = m0 - (mp_ - mm_) / (2 * h)
            cnt = np.sum(zeta > u)
            U = Lam - cnt
            out.append((u, U))
            worst = max(worst, U)
        print(f"trial {trial} d={d} th={th}: zeta={np.round(zeta,3)} v_min~{vmin:.3f} v_max~{vmax:.3f}; "
              f"max over u in (v_min,v_max) of [Lambda(u) - #zeta>u] = {worst:.4f}", flush=True)
        bad = [(round(u,3), round(U,3)) for u, U in out if U > 1e-3]
        if bad: print('   positive at', bad[:8], flush=True)
