"""Adversarial search against PM (monotonicity) and BMV-P necessary conditions, with scale-safe normalisation.
f(lam) = p_{n,m}(e^{Z+(1-th) lam T}, e^{Z - th lam T}), th = n/(n+m). Saves every candidate with violation < -1e-6."""
import sys, time, json
import numpy as np
from scipy.linalg import expm
from scipy.optimize import minimize
from math import comb, factorial
from bmvp_hunt import word_avg, unpack

LAMS = np.linspace(-3, 3, 61)

def fvals(Z, T, n, m, lams=LAMS):
    th = n / (n + m)
    return np.array([word_avg(expm(Z + (1 - th) * l * T), expm(Z - th * l * T), n, m).real for l in lams])

def score(Z, T, n, m):
    v = fvals(Z, T, n, m)
    f0 = v[30]
    scale = max(v[-1], v[0]) - f0
    if not np.all(v > 0) or scale < 1e-6 * f0:
        return 1.0, {}
    pm_pos = np.diff(v[30:]).min() / scale
    pm_neg = -np.diff(v[:31]).max() / scale
    lv = np.log(v); h = LAMS[1] - LAMS[0]
    c2 = (lv[2:] - 2 * lv[1:-1] + lv[:-2]) / h ** 2
    lc = c2.min() / np.abs(c2).max()
    s = min(pm_pos, pm_neg, lc)
    return s, {'pm_pos': pm_pos, 'pm_neg': pm_neg, 'logconv': lc}

seed = int(sys.argv[1]); budget = float(sys.argv[2])
rng = np.random.default_rng(seed)
t0 = time.time(); best = (np.inf, None); found = []
cases = [(1, 1), (2, 1), (1, 2), (2, 2), (3, 1), (3, 2), (2, 3)]
while time.time() - t0 < budget:
    d = int(rng.choice([2, 3, 3, 4]))
    n, m = cases[rng.integers(len(cases))]
    x0 = rng.normal(size=2 * d * d) * rng.choice([0.5, 1.0, 2.0])
    def obj(x):
        Z, T = unpack(x, d)
        try:
            return score(Z, T, n, m)[0]
        except Exception:
            return 1.0
    res = minimize(obj, x0, method='Nelder-Mead', options={'maxfev': 400, 'xatol': 1e-7, 'fatol': 1e-10})
    Z, T = unpack(res.x, d)
    s, det = score(Z, T, n, m)
    if s < best[0]:
        best = (s, (d, n, m))
    if s < -1e-6:
        found.append({'d': d, 'n': n, 'm': m, 'x': res.x.tolist(), 'score': s, 'detail': det})
        json.dump(found, open(f'bmvp_found_{seed}.json', 'w'))
    print(f"{time.time()-t0:6.0f}s d={d} (n,m)=({n},{m}) -> {s:.4g} {det}   best {best[0]:.4g} {best[1]}", flush=True)
print('BEST', best)
