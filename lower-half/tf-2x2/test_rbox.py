"""Soundness test of the box bounds (rbox.py) against independent 50-digit mpmath values (hyp.py).
Ansh Mishra, Aryan Senthilkumar.

For random boxes (various sizes, touching the faces w = +-1, a = 0, c = 0, theta = 1/2 or not) and random points in
them, check
    Rlo <= R(point),  epsP_lo <= eps_P(point),  Flo <= F(point),  a c * D_lo <= dR/dw(point)  (D on the same box).
Any violation is reported.  Usage: python test_rbox.py seed nboxes [amax [digits]]
"""
import sys, random
import mpmath as mp
from flint import ctx
from rbox import box_bounds, dw_lower
from hyp import parts, F as F_mp

mp.mp.dps = int(sys.argv[4]) if len(sys.argv) > 4 else 50
ctx.prec = 100
random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
nb = int(sys.argv[2]) if len(sys.argv) > 2 else 200
AMAX = float(sys.argv[3]) if len(sys.argv) > 3 else 3.5


def Fc(th, a, c, w):
    th = mp.mpf(th); b = th * c / (1 - th)
    return F_mp(th, a, b, w)


def Rc(th, a, c, w):
    th = mp.mpf(th); w = mp.mpf(w)
    return Fc(th, a, c, w) / (th * (1 - w * w) * mp.mpf(a) ** 2 * mp.mpf(c) ** 2)


def dyad(x, k=20):
    return round(x * 2 ** k) / 2 ** k


viol = 0
nchk = 0
for i in range(nb):
    th0 = dyad(random.choice([0.0, random.uniform(0, 0.45), 0.4375]))
    th1 = dyad(min(0.5, th0 + random.choice([1 / 64, 1 / 16, 0.0625, 0.5 - th0])))
    if th1 <= th0:
        continue
    a0 = dyad(random.choice([0.0, random.uniform(0, AMAX)]))
    a1 = dyad(a0 + random.choice([1 / 64, 1 / 8, 0.5]))
    c0 = dyad(random.choice([0.0, random.uniform(0, AMAX)]))
    c1 = dyad(c0 + random.choice([1 / 64, 1 / 8, 0.5]))
    w0 = dyad(random.choice([-1.0, random.uniform(-1, 0.9), 1 - 2.0 ** -random.randint(3, 20)]))
    w1 = dyad(min(1.0, w0 + random.choice([2.0 ** -12, 1 / 64, 1 / 4, 1.0])))
    if w1 <= w0:
        continue
    o = box_bounds(th0, th1, a0, a1, c0, c1, w0, w1)
    d = dw_lower(th0, th1, a0, a1, c0, c1, w0, w1)
    for j in range(4):
        th = random.uniform(max(th0, 1e-3), th1); a = random.uniform(max(a0, 1e-3), a1)
        c = random.uniform(max(c0, 1e-3), c1); w = random.uniform(w0, w1)
        w = min(max(w, -1 + 1e-12), 1 - 1e-12)
        nchk += 1
        R = Rc(th, a, c, w)
        Fv = Fc(th, a, c, w)
        thm = mp.mpf(th); q = parts(thm, a, thm * c / (1 - thm), w)
        eP = q['epsP']
        bad = []
        if float(o['Rlo'].upper()) > float(R) + 1e-30 * abs(float(R)):
            bad.append(('R', float(o['Rlo'].upper()), float(R)))
        if float(o['epsP_lo'].upper()) > float(eP) * (1 + 1e-20) + 1e-40:
            bad.append(('epsP', float(o['epsP_lo'].upper()), float(eP)))
        if float(o['Flo'].upper()) > float(Fv) + 1e-30:
            bad.append(('F', float(o['Flo'].upper()), float(Fv)))
        if d.is_finite() and float(d.mid()) > -1e200:
            h = mp.mpf(10) ** -12
            wl, wh = max(w - float(h), w0), min(w + float(h), w1)
            if wh > wl and -1 < wl and wh < 1:
                dR = (Rc(th, a, c, wh) - Rc(th, a, c, wl)) / (mp.mpf(wh) - mp.mpf(wl))
                if float(d.upper()) * a * c > float(dR) + 1e-6 * abs(float(dR)) + 1e-12:
                    bad.append(('dRdw', float(d.upper()) * a * c, float(dR)))
        if bad:
            viol += 1
            print('VIOLATION box', (th0, th1, a0, a1, c0, c1, w0, w1), 'point', (th, a, c, w), bad, flush=True)
print(f'checked {nchk} points in {nb} boxes; violations: {viol}')
