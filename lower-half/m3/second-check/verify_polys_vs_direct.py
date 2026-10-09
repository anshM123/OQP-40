"""Check that the exact polynomials built by verify_n.py are what the proof says they are.

verify_n.py builds pairs C_k = (alpha, beta), meaning alpha + beta r with r = sqrt(q1 q2), and claims (Section 3 of
math/05-lower-half-m3.md)
    C0 = w w F,  C1 = 2 q2 Dw(X) w w F_X,  C2 = -2 q1 q2 Dw(Y) w w F_Y,  C3 = -4 q1 q2^2 Dw(X) Dw(Y) w w F_XY,
where F = E/(w(s) w(t)), E(s,t) = K_n(1,s,t) - sqrt(K_n(t,1,1) K_n(t,s,s)), w(s) = sqrt(K_n(1,s,s)), s = X^e, t = Y^e.
Here the right-hand sides are computed straight from these definitions (real powers, numerical differentiation at
80 digits), with no polynomial algebra, and compared with the exact polynomials of verify_n.py at random points.
Usage (from the m3/ folder): python second-check/verify_polys_vs_direct.py n [points]"""
import random
import runpy
import sys
from math import comb

import mpmath as mp

n = int(sys.argv[1])
NP = int(sys.argv[2]) if len(sys.argv) > 2 else 12
mp.mp.dps = 80
sys.argv = ["verify_n.py", str(n)]
g = runpy.run_path("verify_n.py")          # builds C, q1, q2, ptX, DXw, ... and prints its own result
C, q1, q2, e = g["C"], g["q1"], g["q2"], g["e"]
ptX = g["ptX"]
Cn = comb(n + 2, 2)


def K(x, y, z):
    tot = mp.mpf(0)
    for i in range(n + 1):
        for j in range(n + 1 - i):
            tot += x**i * y**j * z**(n - i - j)
    return tot / Cn - (x * y * z)**(mp.mpf(n) / 3)


def w(Xv):
    return mp.sqrt(K(1, Xv**e, Xv**e))


def F(Xv, Yv):
    s, t = Xv**e, Yv**e
    E = K(1, s, t) - mp.sqrt(K(t, 1, 1) * K(t, s, s))
    return E / (w(Xv) * w(Yv))


def ev(p, Xv, Yv):
    """evaluate an exact flint polynomial at mp reals via its terms"""
    tot = mp.mpf(0)
    for (i, j), c in zip(p.monoms(), p.coeffs()):
        tot += mp.mpf(int(c.p)) / mp.mpf(int(c.q)) * Xv**int(i) * Yv**int(j)
    return tot


def Dw_val(Zv):
    # Dw = 2 (Z - 1) pt(Z), with pt the polynomial of verify_n.py in its first variable
    return 2 * (Zv - 1) * ev(ptX, Zv, 0)


rng = random.Random(7)
worst = 0
for _ in range(NP):
    Xv = 1 + mp.mpf(10)**rng.uniform(-2, 0.7)
    Yv = Xv * (1 + mp.mpf(10)**rng.uniform(-2, 0.5))
    q1v, q2v = ev(q1, Xv, Yv), ev(q2, Xv, Yv)
    r = mp.sqrt(q1v * q2v)
    ww = w(Xv) * w(Yv)
    direct = {
        'C0': ww * F(Xv, Yv),
        'C1': 2 * q2v * Dw_val(Xv) * ww * mp.diff(lambda x: F(x, Yv), Xv),
        'C2': -2 * q1v * q2v * Dw_val(Yv) * ww * mp.diff(lambda y: F(Xv, y), Yv),
        'C3': -4 * q1v * q2v**2 * Dw_val(Xv) * Dw_val(Yv) * ww * mp.diff(lambda x, y: F(x, y), (Xv, Yv), (1, 1)),
    }
    for k in ('C0', 'C1', 'C2', 'C3'):
        a, b = C[k]
        val = ev(a, Xv, Yv) + ev(b, Xv, Yv) * r
        rel = abs(val - direct[k]) / max(abs(direct[k]), mp.mpf(10)**-70)
        worst = max(worst, rel)
print(f"n = {n}: {NP} random points, largest relative difference between verify_n.py's exact conditions and the "
      f"direct computation: {mp.nstr(worst, 3)}", flush=True)
