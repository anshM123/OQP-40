"""Adversarial search against BMV-P / PM:
  f(lam) = p_{n,m}(e^{Z+(1-th) lam T}, e^{Z - th lam T}),  th = n/(n+m).
Necessary conditions for 'f = Laplace transform of a positive measure':
  (a) log-convexity of f on R;  (b) Hankel PSD of Taylor moments (size 4: moments 0..6).
PM (monotone on [0, inf)) is tested too. Objective = most negative normalised violation."""
import sys, time
import numpy as np
from scipy.linalg import expm
from scipy.optimize import minimize
from math import comb, factorial

def word_avg(A, B, n, m):
    d = A.shape[0]
    S = {(0, 0): np.eye(d, dtype=complex)}
    for i in range(n + 1):
        for j in range(m + 1):
            if i == 0 and j == 0: continue
            T = np.zeros((d, d), complex)
            if i > 0: T += A @ S[(i - 1, j)]
            if j > 0: T += B @ S[(i, j - 1)]
            S[(i, j)] = T
    return np.trace(S[(n, m)]) / comb(n + m, n)

def unpack(x, d):
    k = 0
    def herm():
        nonlocal k
        M = np.zeros((d, d), complex)
        for i in range(d):
            M[i, i] = x[k]; k += 1
        for i in range(d):
            for j in range(i + 1, d):
                M[i, j] = x[k] + 1j * x[k + 1]; M[j, i] = np.conj(M[i, j]); k += 2
        return M
    return herm(), herm()

def f_factory(Z, T, n, m):
    th = n / (n + m)
    return lambda lam: word_avg(expm(Z + (1 - th) * lam * T), expm(Z - th * lam * T), n, m)

def violations(Z, T, n, m):
    f = f_factory(Z, T, n, m)
    lams = np.linspace(-3, 3, 61)
    v = np.array([f(l).real for l in lams])
    if np.any(v <= 0): return -1.0, -1.0, -1.0
    lv = np.log(v)
    h = lams[1] - lams[0]
    conv = (lv[2:] - 2 * lv[1:-1] + lv[:-2]) / h ** 2
    logconv = conv.min() / max(1e-12, np.abs(conv).max())
    pos = v[30:]  # lam >= 0
    pm = np.diff(pos).min() / max(1e-12, (pos - pos[0]).max())
    # Taylor moments via FFT on a circle
    R = 0.5 / max(1e-3, np.abs(np.linalg.eigvalsh(T)).max())
    M = 64
    zs = R * np.exp(2j * np.pi * np.arange(M) / M)
    fv = np.array([f(z) for z in zs])
    c = np.fft.fft(fv) / M / R ** np.arange(M)
    mom = [c[k].real * factorial(k) for k in range(7)]
    H = np.array([[mom[i + j] for j in range(4)] for i in range(4)])
    D = 1 / np.sqrt(np.abs(np.diag(H)))
    hk = np.linalg.eigvalsh(H * np.outer(D, D)).min()
    return logconv, pm, hk

def _main():
    seed = int(sys.argv[1]); budget = float(sys.argv[2])
    rng = np.random.default_rng(seed)
    t0 = time.time(); best = (np.inf, None)
    cases = [(1, 1), (2, 1), (1, 2), (2, 2), (3, 1), (3, 2)]
    while time.time() - t0 < budget:
        d = int(rng.choice([2, 3, 3, 4]))
        n, m = cases[rng.integers(len(cases))]
        npar = 2 * d * d
        x0 = rng.normal(size=npar) * rng.choice([0.3, 1.0, 2.0])
        def obj(x):
            Z, T = unpack(x, d)
            try:
                a, b, c = violations(Z, T, n, m)
            except Exception:
                return 1.0
            return min(a, b, c * 10)
        val0 = obj(x0)
        res = minimize(obj, x0, method='Nelder-Mead', options={'maxfev': 300, 'xatol': 1e-6, 'fatol': 1e-9})
        if res.fun < best[0]:
            best = (res.fun, (d, n, m, res.x.tolist()))
        print(f"{time.time()-t0:6.0f}s d={d} (n,m)=({n},{m}) start {val0:.3g} -> {res.fun:.4g}   best {best[0]:.4g}", flush=True)
    print('BEST', best[0], best[1][:3])
    np.save(f'bmvp_hunt_best_{seed}.npy', np.array(best[1][3]))


if __name__ == "__main__":
    _main()
