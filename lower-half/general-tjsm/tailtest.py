"""Conjecture T: for theta in [0,1] and all u,
   F_mu(u) = mu{theta log a + (1-theta) log b > u}  >=  F_kappa(u) = sum_i K(u - zeta_i),
   K(v) = e^v - 1 - v (v < 0), 0 (v >= 0);  zeta_i = eig(theta log A + (1-theta) log B).
T implies the lower half at every (n,m) with n/(n+m) = theta (integrate e^{Nu} against dF)."""
import sys
import numpy as np
from numpy.polynomial.legendre import leggauss
from tjsm import singular_points

def logm_h(X):
    w, V = np.linalg.eigh(X)
    return (V * np.log(w)) @ V.conj().T

def Kfun(v):
    v = np.asarray(v, dtype=float)
    return np.where(v < 0, np.expm1(np.minimum(v, 0)) - v, 0.0)

def radial_tables(A, B, nphi=400, nr=200):
    """Nodes (phi_k, weight_k) and, per phi, radial nodes r_j with mass w_j = (1/2pi) r |Im| dr dphi."""
    w = np.linalg.eigvals(np.linalg.solve(A, B)).real
    sing = sorted(s for s in np.arctan(w) if 0 < s < np.pi / 2)
    edges = [0.0] + sing + [np.pi / 2]
    xg, wg = leggauss(nphi)
    xr, wr = leggauss(nr)
    PHI, R, MASS = [], [], []
    d = A.shape[0]
    for lo, hi in zip(edges[:-1], edges[1:]):
        # cluster nodes at both ends (integrable singularities at singular angles): phi = lo + (hi-lo) * (1-cos(pi t))/2
        t = (xg + 1) / 2
        phi = lo + (hi - lo) * (1 - np.cos(np.pi * t)) / 2
        jac = (hi - lo) * np.pi * np.sin(np.pi * t) / 2 * wg / 2
        for ph, jw in zip(phi, jac):
            c, s = np.cos(ph), np.sin(ph)
            Cp = c * A + s * B
            Dp = s * A - c * B
            ev = np.linalg.eigvalsh(Cp)
            Dinv = np.linalg.inv(Dp)
            # radial nodes on [ev0, ev-1], clustered at the ends
            tr = (xr + 1) / 2
            r = ev[0] + (ev[-1] - ev[0]) * (1 - np.cos(np.pi * tr)) / 2
            jr = (ev[-1] - ev[0]) * np.pi * np.sin(np.pi * tr) / 2 * wr / 2
            dens = np.empty(nr)
            for j, rr in enumerate(r):
                lam = np.linalg.eigvals((np.eye(d) - Cp / rr) @ Dinv) / rr
                dens[j] = rr * np.sum(np.abs(lam.imag))
            PHI.append(np.full(nr, ph))
            R.append(r)
            MASS.append(dens * jr * jw / (2 * np.pi))
    return np.concatenate(PHI), np.concatenate(R), np.concatenate(MASS)

def test_pair(A, B, thetas, label, nphi=400, nr=200, verbose=True):
    PHI, R, MASS = radial_tables(A, B, nphi, nr)
    pts = singular_points(A, B)
    worst = np.inf
    for th in thetas:
        ell_c = np.log(R) + th * np.log(np.cos(PHI)) + (1 - th) * np.log(np.sin(PHI))
        zS = np.array([th * np.log(a) + (1 - th) * np.log(b) for a, b in pts])
        Z = th * logm_h(A) + (1 - th) * logm_h(B)
        zeta = np.linalg.eigvalsh(Z)
        lo, hi = min(zeta.min(), zS.min(), ell_c.min()) - 2.0, max(zeta.max(), zS.max(), ell_c.max()) + 0.2
        us = np.linspace(lo, hi, 600)
        order = np.argsort(ell_c)
        ell_sorted, mass_sorted = ell_c[order], MASS[order]
        tail = np.concatenate([np.cumsum(mass_sorted[::-1])[::-1], [0.0]])
        idx = np.searchsorted(ell_sorted, us, side='right')
        Fc = tail[idx]
        Fs = Kfun(us[:, None] - zS[None, :]).sum(1)
        Fk = Kfun(us[:, None] - zeta[None, :]).sum(1)
        diff = Fc + Fs - Fk
        k = np.argmin(diff)
        worst = min(worst, diff[k])
        if verbose:
            # sanity: reproduce p along the ray for N = 2 (p_{2th, 2(1-th)} via mu): N(N+1) int e^{Nu} dmu
            N = 2.0
            pc = N * (N + 1) * np.sum(MASS * np.exp(N * ell_c))
            ps = np.sum(np.exp(N * zS))
            pk = np.sum(np.exp(N * zeta))
            print(f"{label} theta={th:.2f}: min_u (F_mu - F_kappa) = {diff[k]: .3e} at u={us[k]: .3f} "
                  f"(F_kappa there {Fk[k]:.3e}); p_N=2 via mu {pc + ps:.6f} vs L {pk:.6f}", flush=True)
    return worst

if __name__ == '__main__':
    rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 0)
    def rand_pd(d, spread=1.0):
        X = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))
        Q, _ = np.linalg.qr(X)
        ev = np.exp(spread * rng.normal(size=d))
        return (Q * ev) @ Q.conj().T
    for trial in range(6):
        d = [2, 3, 3, 4, 4, 5][trial]
        A, B = rand_pd(d, 1.0), rand_pd(d, 1.0)
        test_pair(A, B, [0.25, 0.5, 0.75], f"[trial {trial} d={d}]")
