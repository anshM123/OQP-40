"""Test of the rigorous core rcore.py against independent mpmath code (hyp.py, 60 digits) and against the
E-proof function H on the commuting faces (R(theta,a,c,+1) = 4H(theta,2a,2c), R(theta,a,c,-1) = 4H(theta,x,y),
(x,y) = (2a,-2c) if a >= c else (-2a,2c)).
Ansh Mishra, Aryan Senthilkumar."""
import sys, os, random, time
import mpmath as mp
mp.mp.dps = 60
from flint import arb
import rcore
from rcore import R_box, iv
from hyp import F as F_mp

sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'tf-local', 'E-proof'))
import ecore  # noqa: E402

random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
n = int(sys.argv[2]) if len(sys.argv) > 2 else 40
bad = 0
t0 = time.time()
for k in range(n):
    th = random.choice([0.5, random.uniform(0.0, 0.5), random.uniform(0.4, 0.5), 0.01])
    a = random.choice([random.uniform(0, 0.3), random.uniform(0, 3), random.uniform(0, 6)])
    c = random.choice([random.uniform(0, 0.3), random.uniform(0, 3), random.uniform(0, 6)])
    w = random.choice([random.uniform(-1, 1), -1 + 10 ** random.uniform(-8, -1), 1 - 10 ** random.uniform(-8, -1)])
    if th == 0 or a == 0 or c == 0:
        continue
    R, eP = R_box(arb(th), arb(a), arb(c), arb(w))
    b = mp.mpf(th) * c / (1 - mp.mpf(th))
    Fm = F_mp(th, a, b, w)
    Rm = Fm / (mp.mpf(th) * (1 - mp.mpf(w) ** 2) * mp.mpf(a) ** 2 * mp.mpf(c) ** 2)
    ok = R.contains(arb(mp.nstr(Rm, 40))) or abs(float(R.mid()) - float(Rm)) <= 4 * float(R.rad()) + 1e-25 * abs(float(Rm))
    if not ok:
        bad += 1
    print(f"th={th:.4f} a={a:.4f} c={c:.4f} w={w:.10f}: R ball = {R.str(10)}  mp = {mp.nstr(Rm, 14)}  {'OK' if ok else 'MISMATCH'}")
print('mismatches vs mpmath:', bad, ' time', round(time.time() - t0, 1), 's')

# commuting faces vs E-proof H
bad2 = 0
for k in range(20):
    th = random.uniform(0.02, 0.5); a = random.uniform(0.01, 3); c = random.uniform(0.01, 3)
    for wv in (1, -1):
        R, _ = R_box(arb(th), arb(a), arb(c), arb(wv))
        if wv == 1:
            x, y = 2 * a, 2 * c
        else:
            x, y = (2 * a, -2 * c) if a >= c else (-2 * a, 2 * c)
        H = ecore.H_point(arb(th), arb(x), arb(y))
        ok = R.overlaps(4 * H)
        bad2 += (not ok)
        print(f"face w={wv:+d} th={th:.3f} a={a:.3f} c={c:.3f}: R = {R.str(12)}  4H = {(4 * H).str(12)}  {'OK' if ok else 'MISMATCH'}")
print('face mismatches:', bad2)
