"""Independent numerical cross-check of the symbolic conditions.

From first principles (mpmath, 60 digits): K_n(x,y,z) = h_n(x,y,z)/C(n+2,2) - (xyz)^{n/3} with real powers,
E(s,t) = K(1,s,t) - sqrt(K(t,1,1) K(t,s,s)) (1 < s < t), weight w(b) = sqrt(K(1,b,b)) ("diag") or
(b-1)^{3/2} b^{(n-3)/2} ("std"), F = E/(w(s) w(t)); derivatives F_s, F_t, F_st by mp.diff in the variables s, t.
Compares with the polynomial expressions C1, C2, C3 (unreduced alpha + beta*rho from m3flint2) divided by
their claimed positive multipliers:
  C1 = 2 q2 Dw(X) w w F_X,   C2 = -2 q1 q2 Dw(Y) w w F_Y,   C3 = -4 q1 q2^2 Dw(X) Dw(Y) w w F_XY,
where X = s^{1/e}, F_X = F_s e X^{e-1}, F_XY = F_st e^2 X^{e-1} Y^{e-1}.  Also C0 = E.
Usage: python crosscheck_conditions.py n weight"""
import sys, random
from fractions import Fraction
from math import comb
import mpmath as mp
from m3flint2 import *

mp.mp.dps = 60
n = int(sys.argv[1]); wname = sys.argv[2] if len(sys.argv) > 2 else 'diag'
if wname == 'std':
    spec_fn = lambda n, d: std_weight(n, d['e'])
else:
    spec_fn = lambda n, d: diag_weight(n, d)
d, conds, _ = conditions(n, spec_fn)
e = d['e']
NXw, DXw = weight_poly(spec_fn(n, d), X)
NYw, DYw = weight_poly(spec_fn(n, d), Y)

def tofun(p):
    terms = [((int(m[0]), int(m[1])), mp.mpf(int(c.p)) / int(c.q)) for m, c in zip(p.monoms(), p.coeffs())]
    return lambda x, y: mp.fsum(c * x**m[0] * y**m[1] for m, c in terms)

Cn = comb(n + 2, 2)
def hn(x, y, z):
    return mp.fsum(x**i * y**j * z**(n - i - j) for i in range(n + 1) for j in range(n + 1 - i))
def Kd(x, y, z):
    return hn(x, y, z) / Cn - (x * y * z) ** (mp.mpf(n) / 3)
def Ed(s, t):
    return Kd(1, s, t) - mp.sqrt(Kd(t, 1, 1) * Kd(t, s, s))
def wd(b):
    if wname == 'std':
        return (b - 1) ** mp.mpf(1.5) * b ** (mp.mpf(n - 3) / 2)
    return mp.sqrt(Kd(1, b, b))
def Fd(s, t):
    return Ed(s, t) / (wd(s) * wd(t))

fq1, fq2 = tofun(d['q1']), tofun(d['q2'])
fun = {k: (tofun(a), tofun(b)) for k, (a, b) in conds.items()}
fDX, fDY = tofun(DXw), tofun(DYw)
random.seed(7)
worst = {k: mp.mpf(0) for k in conds}
for trial in range(40):
    s = 1 + mp.mpf(10) ** random.uniform(-2, 2)
    t = s + mp.mpf(10) ** random.uniform(-2, 2)
    Xv, Yv = s ** (mp.mpf(1) / e), t ** (mp.mpf(1) / e)
    rho = mp.sqrt(fq1(Xv, Yv) * fq2(Xv, Yv))
    val = {k: fa(Xv, Yv) + fb(Xv, Yv) * rho for k, (fa, fb) in fun.items()}
    ww = wd(s) * wd(t)
    Fs = mp.diff(lambda x: Fd(x, t), s); Ft = mp.diff(lambda y: Fd(s, y), t)
    Fst = mp.diff(lambda x: mp.diff(lambda y: Fd(x, y), t), s)
    FX = Fs * e * Xv**(e - 1); FY = Ft * e * Yv**(e - 1); FXY = Fst * e * e * Xv**(e - 1) * Yv**(e - 1)
    q1v, q2v = fq1(Xv, Yv), fq2(Xv, Yv)
    pred = {'C0': Ed(s, t), 'C1': 2 * q2v * fDX(Xv, Yv) * ww * FX, 'C2': -2 * q1v * q2v * fDY(Xv, Yv) * ww * FY,
            'C3': -4 * q1v * q2v**2 * fDX(Xv, Yv) * fDY(Xv, Yv) * ww * FXY}
    for k in conds:
        rel = abs(val[k] - pred[k]) / max(abs(pred[k]), mp.mpf(10) ** -40)
        worst[k] = max(worst[k], rel)
        if pred[k] < 0:
            print("NEGATIVE condition value", k, s, t, pred[k])
print(f"n = {n}, weight {wname}: max relative mismatch symbolic vs direct differentiation:",
      {k: mp.nstr(v, 3) for k, v in worst.items()})
