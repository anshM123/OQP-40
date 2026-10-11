"""Landscape of E(theta, X, Y) (X = log a, Y = log b, Delta = theta X + (1-theta) Y > 0), normalised by
X^2 Y^2 (1 - 2 theta + Delta) e^{N0 Delta}/(1 + Delta)^? ... we print min of E / (X^2 Y^2 * w) for a few w."""
import numpy as np
import mpmath as mp
mp.mp.dps = 50

def E(th, X, Y):
    th, X, Y = mp.mpf(th), mp.mpf(X), mp.mpf(Y)
    r = (1 - th) / th
    x, y = X, r * Y
    a, b = mp.e ** X, mp.e ** Y
    p, q = mp.expm1(X), mp.expm1(Y)
    s = x + y
    t1 = th * (x * y * mp.expm1(s) / s - mp.expm1(x) * mp.expm1(y))
    t2 = th * x * y * (-mp.expm1(-th * s)) / s
    t3 = p * q / (p - q) ** 2 * ((1 - th) * p * mp.expm1(th * (Y - X)) + th * q * mp.expm1((1 - th) * (X - Y)))
    return t1 + t2 + t3

rows = []
for th in ['0.5', '0.45', '0.35', '0.25', '0.15', '0.08', '0.03']:
    thf = float(th); N0 = 1 / thf
    worst = (np.inf, None)
    for X in np.concatenate([-np.exp(np.linspace(np.log(0.01), np.log(6), 18)), np.exp(np.linspace(np.log(0.01), np.log(6), 18))]):
        for Y in np.concatenate([-np.exp(np.linspace(np.log(0.01), np.log(6), 18)), np.exp(np.linspace(np.log(0.01), np.log(6), 18))]):
            D = thf * X + (1 - thf) * Y
            if D <= 1e-3 or abs(X - Y) < 1e-9:
                continue
            v = float(E(th, X, Y))
            w = X * X * Y * Y * ((1 - 2 * thf) + min(D, 1.0)) * np.exp(N0 * D) / (1 + abs(X) + abs(Y)) ** 2
            if v / w < worst[0]:
                worst = (v / w, (X, Y, D, v))
    rows.append((th, worst))
for th, (val, arg) in rows:
    print(f"theta={th}: min E/w = {val:.4e} at X={arg[0]:.3g}, Y={arg[1]:.3g}, Delta={arg[2]:.3g}, E={arg[3]:.3e}")
