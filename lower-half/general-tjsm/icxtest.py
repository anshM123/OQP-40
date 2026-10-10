"""icx order of the projected measures: G(u) = int_u^inf (F_mu - F_kappa) dv >= 0 for all u.
icx implies p >= L along the ray for every real N > 0 (hence the lower half at all (n,m) on that ray)."""
import sys
import numpy as np
from tailtest import radial_tables, Kfun, logm_h
from tjsm import singular_points

def Gcurve(A, B, th, PHI, R, MASS, pts, ngrid=4000):
    ell = np.log(R) + th * np.log(np.cos(PHI)) + (1 - th) * np.log(np.sin(PHI))
    zS = np.array([th * np.log(a) + (1 - th) * np.log(b) for a, b in pts])
    zeta = np.linalg.eigvalsh(th * logm_h(A) + (1 - th) * logm_h(B))
    lo = min(zeta.min(), zS.min(), ell.min()) - 12.0
    hi = max(zeta.max(), zS.max(), ell.max()) + 0.1
    us = np.linspace(lo, hi, ngrid)
    order = np.argsort(ell); es, ms = ell[order], MASS[order]
    tail = np.concatenate([np.cumsum(ms[::-1])[::-1], [0.0]])
    Fc = tail[np.searchsorted(es, us, side='right')]
    g = Fc + Kfun(us[:, None] - zS[None, :]).sum(1) - Kfun(us[:, None] - zeta[None, :]).sum(1)
    du = us[1] - us[0]
    G = np.concatenate([np.cumsum(((g[1:] + g[:-1]) / 2 * du)[::-1])[::-1], [0.0]])
    # scale: compare with int_u^inf F_kappa
    gk = Kfun(us[:, None] - zeta[None, :]).sum(1)
    Gk = np.concatenate([np.cumsum(((gk[1:] + gk[:-1]) / 2 * du)[::-1])[::-1], [0.0]])
    return us, g, G, Gk, zeta

if __name__ == '__main__':
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 0
    rng = np.random.default_rng(seed)
    def rand_pd(d, spread=1.0):
        X = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))
        Q, _ = np.linalg.qr(X)
        ev = np.exp(spread * rng.normal(size=d))
        return (Q * ev) @ Q.conj().T
    for trial in range(8):
        d = [2, 2, 3, 3, 4, 4, 5, 3][trial]
        spread = [1.0, 2.0, 1.0, 2.0, 1.0, 2.0, 1.0, 3.0][trial]
        A, B = rand_pd(d, spread), rand_pd(d, spread)
        PHI, R, MASS = radial_tables(A, B, 400, 200)
        pts = singular_points(A, B)
        for th in (0.2, 0.5, 0.8):
            us, g, G, Gk, zeta = Gcurve(A, B, th, PHI, R, MASS, pts)
            k = np.argmin(G)
            print(f"[d={d} spread={spread}] theta={th}: min G = {G[k]: .3e} at u={us[k]: .3f} (rel to int F_kappa: {G[k]/max(Gk[k],1e-300): .2e}); G(-inf)={G[0]: .3e}; min g={g.min(): .2e}", flush=True)
