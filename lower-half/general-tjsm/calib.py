import numpy as np
from scipy import integrate
from tjsm import word_avg, singular_points, density_polar

rng = np.random.default_rng(1)


def rand_pd(d):
    X = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))
    H = X @ X.conj().T / d
    return H + 0.3 * np.eye(d)


def moment_c(A, B, n, m):
    N = n + m
    w = np.linalg.eigvals(np.linalg.solve(A, B)).real
    sing = sorted(np.arctan(w))
    pts = [0.0] + [s for s in sing if 0 < s < np.pi / 2] + [np.pi / 2]

    def inner(phi):
        Cp = np.cos(phi) * A + np.sin(phi) * B
        ev = np.linalg.eigvalsh(Cp)
        f = lambda r: r ** N * np.cos(phi) ** n * np.sin(phi) ** m * density_polar(A, B, r, phi)
        val, _ = integrate.quad(f, ev[0], ev[-1], limit=200, points=list(ev[1:-1]))
        return val
    tot = 0.0
    for lo, hi in zip(pts[:-1], pts[1:]):
        v, _ = integrate.quad(inner, lo, hi, limit=200)
        tot += v
    return tot


for d in (2, 3):
    A, B = rand_pd(d), rand_pd(d)
    for n, m in [(1, 1), (2, 1), (2, 2), (3, 2)]:
        N = n + m
        p = word_avg(A, B, n, m)
        S = sum(a ** n * b ** m for a, b in singular_points(A, B))
        I = moment_c(A, B, n, m)
        print(f"d={d} (n,m)=({n},{m}) p={p:.10f} S={S:.10f} (p-S)/(N(N+1) I) = {(p - S) / (N * (N + 1) * I):.8f}  [1/2pi={1/(2*np.pi):.8f}, 1/4pi={1/(4*np.pi):.8f}]", flush=True)
