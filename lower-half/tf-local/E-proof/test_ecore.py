"""Tests of ecore against the mpmath closed form (verify_closed_form.E_closed) and internal consistency:
  - H_point = E/(theta x^2 y^2) at random points;
  - tm_point_I == tm_point_II;
  - g_series == g_point;
  - box enclosures contain sampled point values;
  - complex evaluation runs (for the Cauchy bounds)."""
import random
import mpmath as mp
from flint import arb, acb
import ecore as C
from verify_closed_form import E_closed

mp.mp.dps = 60
rng = random.Random(11)
worst = 0
for i in range(200):
    th = rng.choice([rng.uniform(0.001, 0.5), 0.5, rng.uniform(0.4, 0.5)])
    x = rng.uniform(-8, 8)
    y = rng.uniform(-8, 8)
    if x + y <= 0:
        x, y = -x, -y
    if rng.random() < 0.2:
        y = rng.uniform(-1e-3, 1e-3)
        x = abs(x)
    if rng.random() < 0.1:
        x = rng.uniform(-1e-3, 1e-3)
        y = abs(y)
    thA, xA, yA = arb(repr(th)), arb(repr(x)), arb(repr(y))
    H = C.H_point(thA, xA, yA)
    X, Y = mp.mpf(repr(x)), mp.mpf(repr(th)) / (1 - mp.mpf(repr(th))) * mp.mpf(repr(y))
    Ec = E_closed(mp.mpf(repr(th)), X, Y)
    Hc = Ec / (mp.mpf(repr(th)) * mp.mpf(repr(x)) ** 2 * mp.mpf(repr(y)) ** 2)
    rel = abs(mp.mpf(H.mid().str(60, radius=False)) - Hc) / abs(Hc)
    worst = max(worst, rel)
    t1 = C.tm_point_I(thA, xA, yA)
    t2 = C.tm_point_II(thA, xA, yA)
    assert t1.overlaps(t2), (th, x, y, t1, t2)
    if abs(x) <= 1 and abs(y) <= 1:
        assert C.g_series(xA, yA).overlaps(C.g_point(xA, yA))
print("H_point vs mpmath closed form: max rel diff", mp.nstr(worst, 3), "(mpmath at 60 digits)")

# box enclosure tests
bad = 0
for i in range(300):
    th0 = rng.uniform(0.01, 0.5); hth = rng.choice([0.001, 0.01])
    x0 = rng.uniform(-6, 6); y0 = rng.uniform(-6, 6); h = rng.choice([0.01, 0.05, 0.2])
    if x0 + y0 - 2 * h <= 0.05 or abs(x0) < 2 * h or abs(y0) < 2 * h:
        continue
    thB = arb(th0, hth); xB = arb(x0, h); yB = arb(y0, h)
    encI = C.tm_box_I(thB, xB, yB)
    encII = C.tm_box_II(thB, xB, yB)
    for t in range(5):
        th = th0 + rng.uniform(-hth, hth); x = x0 + rng.uniform(-h, h); y = y0 + rng.uniform(-h, h)
        v = C.tm_point_I(arb(th), arb(x), arb(y))
        if not (encI.contains(v) and encII.contains(v)):
            bad += 1
            print("NOT CONTAINED", th, x, y, v, encI, encII)
print("box containment failures:", bad)
# widths
thB = arb(0.5, 0.005); xB = arb(1.2, 0.02); yB = arb(-1.1, 0.02)
print("example tm_box_I at th=.5+-.005, x=1.2+-.02, y=-1.1+-.02:", C.tm_box_I(thB, xB, yB))
print("example tm_box_II same box:", C.tm_box_II(thB, xB, yB))
print("point:", C.tm_point_I(arb(0.5), arb(1.2), arb(-1.1)), " g:", C.g_point(arb(1.2), arb(-1.1)))
# complex
z = C.H_point(arb(0.5), acb(2.0, 1.0), acb(-1.0, 2.0))
print("complex H sample:", z)
