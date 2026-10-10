"""Numerical check of the constants of Lemma T / T' (RESULTS 8.3): maxima over circles |zeta - b| = 1 (maximum modulus
principle: for analytic functions the disc maximum is attained on the circle)."""
import mpmath as mp
mp.mp.dps = 40
lam, eta = mp.mpf(7) / 100, mp.mpf(7) / 10
def G(z): return 1 - (1 + z) * mp.exp(-z) - z ** 2 / 2 * mp.exp(-2 * z / 3)
def q(z): return ((z - 1 + mp.exp(-z)) * mp.exp(-(mp.mpf(1) / 2 - lam) * z) / z + z / 2 * mp.exp(-(mp.mpf(1) / 6 - lam) * z)) / (1 - mp.exp(-z) + mp.sqrt(G(z)))
def y(z): return eta * z * mp.exp(-(mp.mpf(1) / 2 + lam) * z) * (1 - q(z)) / mp.sqrt(G(z))
def phit(z):
    yy = y(z)
    ell = -mp.log1p(-yy) / yy
    return mp.sqrt(ell * eta * (1 - q(z)) / mp.sqrt(G(z)))
for b in (30, 31, 40, 64, 100):
    M = {'1-G': 0, 'q': 0, 'y': 0, 'phit': 0}
    for k in range(720):
        z = b + mp.expjpi(mp.mpf(2 * k) / 720)
        M['1-G'] = max(M['1-G'], abs(1 - G(z))); M['q'] = max(M['q'], abs(q(z)))
        M['y'] = max(M['y'], abs(y(z))); M['phit'] = max(M['phit'], abs(phit(z)))
    print(f"b={b}: max|1-G|={mp.nstr(M['1-G'], 3)} (claim 2e-6)  max|q|={mp.nstr(M['q'], 4)} (0.47)  max|y|={mp.nstr(M['y'], 3)} (2e-6)  max|phit|={mp.nstr(M['phit'], 5)} (1.02)")
for zr in (400, 512, 600):
    m = 0
    for k in range(720):
        z = zr + mp.expjpi(mp.mpf(2 * k) / 720)
        m = max(m, abs(phit(z) - mp.sqrt(eta)))
    print(f"z={zr}: max|phit - sqrt(eta)| on the circle = {mp.nstr(m, 3)}, claimed bound 2(z+1)e^(-(1/6-lam)(z-1)) = {mp.nstr(2 * (zr + 1) * mp.exp(-(mp.mpf(1) / 6 - lam) * (zr - 1)), 3)}")
