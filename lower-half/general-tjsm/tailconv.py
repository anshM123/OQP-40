import numpy as np
from tailtest import radial_tables, Kfun, logm_h
from tjsm import singular_points, word_avg
rng = np.random.default_rng(0)
def rand_pd(d, spread=1.0):
    X = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))
    Q, _ = np.linalg.qr(X)
    ev = np.exp(spread * rng.normal(size=d))
    return (Q * ev) @ Q.conj().T
A, B = rand_pd(2), rand_pd(2)
pts = singular_points(A, B)
th = 0.5
Z = th * logm_h(A) + (1 - th) * logm_h(B); zeta = np.linalg.eigvalsh(Z)
zS = np.array([th * np.log(a) + (1 - th) * np.log(b) for a, b in pts])
for nphi, nr in [(200, 100), (400, 200), (800, 400), (1600, 400)]:
    PHI, R, MASS = radial_tables(A, B, nphi, nr)
    ell = np.log(R) + th * np.log(np.cos(PHI)) + (1 - th) * np.log(np.sin(PHI))
    errs = []
    for n in (1, 2, 3):
        N = 2 * n
        pm = N * (N + 1) * np.sum(MASS * np.exp(N * ell)) + np.sum(np.exp(N * zS))
        errs.append(pm / word_avg(A, B, n, n) - 1)
    order = np.argsort(ell); es, ms = ell[order], MASS[order]
    tail = np.concatenate([np.cumsum(ms[::-1])[::-1], [0.0]])
    us = np.linspace(-1.5, 0.8, 461)
    Fc = tail[np.searchsorted(es, us, side='right')]
    diff = Fc + Kfun(us[:, None] - zS[None, :]).sum(1) - Kfun(us[:, None] - zeta[None, :]).sum(1)
    k = np.argmin(diff)
    print(nphi, nr, 'moment rel errors', ['%.1e' % e for e in errs], 'min diff %.4e at u=%.3f' % (diff[k], us[k]), 'total cont mass', MASS.sum())
print('zeta', zeta, 'zS', zS)
