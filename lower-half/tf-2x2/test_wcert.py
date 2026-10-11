"""Soundness test of the whole-column certificate W (rbox.wcert) against 50-digit mpmath values of F.
Ansh Mishra, Aryan Senthilkumar.
For random (theta, a, c)-boxes with a, c >= 2 that W certifies, sample points (theta, a, c, w) with w in the bulk and
in the thin layers near +-1 and check F >= 0 (F from hyp.py, independent closed forms).  Also reports the face
parameters (k+, k-, y+, y-) of W.  Usage: python test_wcert.py seed nboxes [amin amax [digits]]"""
import sys, random
import mpmath as mp
from flint import ctx
from rbox import wcert
from hyp import F as F_mp

mp.mp.dps = int(sys.argv[5]) if len(sys.argv) > 5 else 120
ctx.prec = 100
random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
nb = int(sys.argv[2]) if len(sys.argv) > 2 else 40
AMIN = float(sys.argv[3]) if len(sys.argv) > 3 else 2.0
AMAX = float(sys.argv[4]) if len(sys.argv) > 4 else 7.5
ncert = 0; npts = 0; bad = 0
for i in range(nb):
    th0 = random.choice([0.0625, 0.125, 0.25, 0.375, 0.4375, 0.46875])
    th1 = min(0.5, th0 + random.choice([1 / 64, 1 / 32]))
    a0 = round(random.uniform(AMIN, AMAX) * 64) / 64; c0 = round(random.uniform(AMIN, AMAX) * 64) / 64
    a1 = a0 + random.choice([1 / 64, 1 / 16]); c1 = c0 + random.choice([1 / 64, 1 / 16])
    ok, info = wcert(th0, th1, a0, a1, c0, c1)
    if not ok:
        continue
    ncert += 1
    kp, km = info[0], info[1]
    for j in range(12):
        th = random.uniform(th0, th1); a = random.uniform(a0, a1); c = random.uniform(c0, c1)
        mode = j % 4
        if mode == 0:
            w = mp.mpf(random.uniform(-1, 1))
        elif mode == 1:
            w = 1 - mp.mpf(2) ** (-kp) * mp.mpf(random.random())        # inside the + layer
        elif mode == 2:
            w = -1 + mp.mpf(2) ** (-km) * mp.mpf(random.random())       # inside the - layer
        else:
            w = 1 - mp.mpf(10) ** (-random.uniform(5, 30))
        thm = mp.mpf(th)
        Fv = F_mp(thm, a, thm * c / (1 - thm), w)
        npts += 1
        if Fv < 0:
            bad += 1
            print('VIOLATION', (th0, th1, a0, a1, c0, c1), (th, a, c, mp.nstr(w, 20)), mp.nstr(Fv, 10), flush=True)
print(f'W-certified boxes {ncert} of {nb}; points checked {npts}; F < 0 at {bad} points')
