"""Exact TF tail for 2x2 pairs via the Bloch-sphere formula for the Weyl joint distribution:
  for A = a0 + a.sigma, B = b0 + b.sigma:  int F dPi_{A,B} = 2 E_n [ (1 + r d/dr) F(a0 + r a.n, b0 + r b.n) ]_{r=1},
  n uniform on S^2.  (Checked here against word averages.)
T(u) = int g_u(l) dPi - sum_i g_u(zeta_i), g_u(v) = [e^{N0 v} - (N0+1)e^{N0 u} + N0 e^{(N0+1)u - v}]_+ / (N0(N0+1))."""
import numpy as np
from scipy import integrate, optimize
from scipy.linalg import logm, expm, eigh

PAULI = [np.array([[0, 1], [1, 0]], complex), np.array([[0, -1j], [1j, 0]]), np.array([[1, 0], [0, -1]], complex)]

def bloch(M):
    return np.real(np.trace(M)) / 2, np.array([np.real(np.trace(M @ P)) / 2 for P in PAULI])

def plane_coords(av, bv):
    """Orthonormal basis e1, e2 of span(av, bv); returns 2-vectors (a.e1, a.e2), (b.e1, b.e2)."""
    e1 = av / np.linalg.norm(av)
    w = bv - (bv @ e1) * e1
    e2 = w / np.linalg.norm(w) if np.linalg.norm(w) > 1e-300 else np.cross(e1, [0.3, 0.5, 0.7])
    e2 = e2 / np.linalg.norm(e2)
    return np.array([av @ e1, av @ e2]), np.array([bv @ e1, bv @ e2])

def make_integrand(A, B, th, F, dF):
    a0, av = bloch(A); b0, bv = bloch(B)
    a2, b2 = plane_coords(av, bv)
    def val(x, y):  # (x, y) = projection of n on the plane
        da, db = a2[0] * x + a2[1] * y, b2[0] * x + b2[1] * y
        a, b = a0 + da, b0 + db
        l = th * np.log(a) + (1 - th) * np.log(b)
        dl = th * da / a + (1 - th) * db / b
        return F(l) + dF(l) * dl
    return val

def sphere_mean(f, splitter=None):
    """E_n f(n_x, n_y) for n uniform on S^2 = (1/2pi) int_0^{2pi} int_0^{pi/2} f(sin p cos c, sin p sin c) sin p dp dc."""
    def inner(c):
        g = lambda p: f(np.sin(p) * np.cos(c), np.sin(p) * np.sin(c)) * np.sin(p)
        pts = splitter(c) if splitter else []
        edges = [0.0] + sorted(p for p in pts if 0 < p < np.pi / 2) + [np.pi / 2]
        return sum(integrate.quad(g, lo, hi, epsabs=1e-15, epsrel=1e-12, limit=200)[0] for lo, hi in zip(edges[:-1], edges[1:]))
    return integrate.quad(inner, 0, 2 * np.pi, epsabs=1e-15, epsrel=1e-12, limit=400)[0] / (2 * np.pi)

def tf_tail(A, B, th, u):
    N0 = 1 / min(th, 1 - th)
    def g(v):
        v = np.asarray(v, float)
        t = np.exp(N0 * v) - (N0 + 1) * np.exp(N0 * u) + N0 * np.exp((N0 + 1) * u - v)
        return np.where(v > u, t, 0.0) / (N0 * (N0 + 1))
    def dg(v):
        v = np.asarray(v, float)
        return np.where(v > u, (np.exp(N0 * v) - np.exp((N0 + 1) * u - v)) / (N0 + 1), 0.0)
    a0, av = bloch(A); b0, bv = bloch(B)
    a2, b2 = plane_coords(av, bv)
    def lev(x, y):
        return th * np.log(a0 + a2 @ [x, y]) + (1 - th) * np.log(b0 + b2 @ [x, y])
    def splitter(c):  # p where the ray hits the level curve l = u (concave along the ray -> <= 2 roots)
        ps = np.linspace(0, np.pi / 2, 401)
        vals = np.array([lev(np.sin(p) * np.cos(c), np.sin(p) * np.sin(c)) - u for p in ps])
        out = []
        for i in range(len(ps) - 1):
            if vals[i] == 0: out.append(ps[i])
            elif vals[i] * vals[i + 1] < 0:
                out.append(optimize.brentq(lambda p: lev(np.sin(p) * np.cos(c), np.sin(p) * np.sin(c)) - u, ps[i], ps[i + 1], xtol=1e-15))
        return out
    f = make_integrand(A, B, th, g, dg)
    Pi_part = 2 * sphere_mean(f, splitter)
    Z = th * logm(A) + (1 - th) * logm(B)
    zeta = eigh((Z + Z.conj().T) / 2, eigvals_only=True)
    return Pi_part - float(np.sum(g(zeta))), zeta

def word_avg_check(A, B, n, m, th=None):
    """Compare int a^n b^m dPi (sphere formula) with the word average."""
    from itertools import combinations
    N = n + m
    tot = 0; cnt = 0
    for pos in combinations(range(N), n):
        W = np.eye(2, dtype=complex)
        for i in range(N):
            W = W @ (A if i in pos else B)
        tot += np.trace(W).real; cnt += 1
    a0, av = bloch(A); b0, bv = bloch(B)
    a2, b2 = plane_coords(av, bv)
    def f(x, y):
        da, db = a2 @ [x, y], b2 @ [x, y]
        a, b = a0 + da, b0 + db
        return a ** n * b ** m + (n * a ** (n - 1) * b ** m * da + m * a ** n * b ** (m - 1) * db)
    return tot / cnt, 2 * sphere_mean(f)

if __name__ == '__main__':
    rng = np.random.default_rng(1)
    X = rng.normal(size=(2, 2)) + 1j * rng.normal(size=(2, 2)); X = (X + X.conj().T) / 2
    Y = rng.normal(size=(2, 2)) + 1j * rng.normal(size=(2, 2)); Y = (Y + Y.conj().T) / 2
    A, B = expm(0.7 * X), expm(0.7 * Y)
    for (n, m) in [(1, 1), (2, 1), (2, 2), (3, 2), (4, 3)]:
        wa, sp = word_avg_check(A, B, n, m)
        print(f"({n},{m}) word avg {wa:.12f}  sphere {sp:.12f}  diff {wa - sp:.2e}")
