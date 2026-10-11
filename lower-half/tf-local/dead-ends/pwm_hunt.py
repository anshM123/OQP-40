"""Adversarial hunt against PWM: h -> R(h) = p_{n,m}(A^h,B^h)/L_{n,m}(A^h,B^h) nondecreasing on (0, 1].
Parametrise A = e^X, B = e^Y with X, Y Hermitian; work with log R to avoid overflow (rescale by e^{-h lambda_max}).
Score = min_k [log R(h_{k+1}) - log R(h_k)] / max_k log R(h_k); negatives saved for 50-digit re-check."""
import sys, time, json
import numpy as np
from scipy.linalg import expm, eigh
from scipy.optimize import minimize
from math import comb
from bmvp_hunt import unpack

def word_avg_scaled(A, B, n, m):
    d = A.shape[0]
    S = {(0, 0): np.eye(d, dtype=complex)}
    for i in range(n + 1):
        for j in range(m + 1):
            if i == 0 and j == 0: continue
            T = np.zeros((d, d), complex)
            if i > 0: T += A @ S[(i - 1, j)]
            if j > 0: T += B @ S[(i, j - 1)]
            S[(i, j)] = T
    return np.trace(S[(n, m)]).real / comb(n + m, n)

HS = np.linspace(0.05, 1.0, 39)
def logR(X, Y, n, m):
    out = []
    for h in HS:
        a = eigh(X, eigvals_only=True).max(); b = eigh(Y, eigvals_only=True).max()
        A, B = expm(h * (X - a * np.eye(len(X)))), expm(h * (Y - b * np.eye(len(Y))))  # shift: common factor e^{h(na+mb)}
        p = word_avg_scaled(A, B, n, m)
        L = np.trace(expm(h * (n * (X - a * np.eye(len(X))) + m * (Y - b * np.eye(len(Y)))))).real
        if not (p > 0 and L > 0): return None
        out.append(np.log(p) - np.log(L))
    return np.array(out)

def score(x, d, n, m):
    X, Y = unpack(x, d)
    r = logR(X, Y, n, m)
    if r is None: return 1.0
    if r.max() < 1e-10: return 1.0
    return np.diff(r).min() / r.max()

seed = int(sys.argv[1]); budget = float(sys.argv[2])
rng = np.random.default_rng(seed)
t0 = time.time(); best = (np.inf, None); found = []
cases = [(1, 1), (2, 1), (1, 2), (2, 2), (3, 1), (3, 2), (2, 3), (3, 3), (4, 2)]
while time.time() - t0 < budget:
    d = int(rng.choice([2, 3, 3, 4]))
    n, m = cases[rng.integers(len(cases))]
    x0 = rng.normal(size=2 * d * d) * rng.choice([0.5, 1.5, 3.0, 5.0])
    res = minimize(lambda x: score(x, d, n, m), x0, method='Nelder-Mead', options={'maxfev': 500, 'xatol': 1e-8, 'fatol': 1e-12})
    if res.fun < best[0]: best = (res.fun, (d, n, m))
    if res.fun < -1e-7:
        found.append({'d': d, 'n': n, 'm': m, 'x': res.x.tolist(), 'score': res.fun})
        json.dump(found, open(f'pwm_found_{seed}.json', 'w'))
    print(f"{time.time()-t0:6.0f}s d={d} ({n},{m}) -> {res.fun:.4g}   best {best[0]:.4g} {best[1]}", flush=True)
print('BEST', best)
