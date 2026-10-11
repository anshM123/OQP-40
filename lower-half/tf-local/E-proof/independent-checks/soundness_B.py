"""Randomised soundness test of region-B box certificates: for random boxes, the certified margin
glo - tm_upper (a claimed lower bound for H on the box) must not exceed min over samples of H (mpmath, 50 digits,
from the closed form, written independently of ecore)."""
import sys, random
sys.path.insert(0, '..')
import mpmath as mp
import regionB as RB
mp.mp.dps = 50

def H_mp(th, x, y):
    th, x, y = mp.mpf(th), mp.mpf(x), mp.mpf(y)
    r = (1 - th) / th; X, Y = x, y / r; s = x + y
    p, q = mp.expm1(X), mp.expm1(Y)
    EGT = th * (x * y * mp.expm1(s) / s - mp.expm1(x) * mp.expm1(y))
    Em1 = th * x * y * (-mp.expm1(-th * s)) / s + p * q / (p - q) ** 2 * ((1 - th) * p * mp.expm1(th * (Y - X)) + th * q * mp.expm1((1 - th) * (X - Y)))
    return (EGT + Em1) / (th * x * x * y * y)

rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 0)
bad = 0; tested = 0; worst_gap = None
for _ in range(400):
    th_lo = rng.uniform(0.01, 0.48); th_w = rng.choice([0.002, 0.01, 0.03])
    x_lo = rng.uniform(-6, 8); y_lo = rng.uniform(-6, 8)
    w = rng.choice([1 / 64, 1 / 16, 1 / 4])
    x_hi, y_hi = x_lo + w, y_lo + w
    if x_lo + y_lo <= 0.05:
        continue
    ok, margin = RB.verify(th_lo, th_lo + th_w, x_lo, x_hi, y_lo, y_hi)
    if margin is None:
        continue
    tested += 1
    hmin = None
    for i in range(5):
        for j in range(5):
            for k in range(3):
                th = th_lo + th_w * k / 2; x = x_lo + w * i / 4; y = y_lo + w * j / 4
                if abs(x) < 1e-12 or abs(y) < 1e-12 or x + y <= 0: continue
                h = H_mp(th, x, y)
                hmin = h if hmin is None or h < hmin else hmin
    m = mp.mpf(margin.mid().str(30, radius=False)) if hasattr(margin, 'mid') else mp.mpf(str(margin))
    gap = hmin - m
    if worst_gap is None or gap < worst_gap: worst_gap = gap
    if gap < -mp.mpf('1e-20'):
        bad += 1
        print('UNSOUND?', th_lo, x_lo, y_lo, w, 'certified', m, 'sampled min', hmin)
print(f'boxes tested {tested}, certified-margin above sampled min (unsound): {bad}; min(sampled min - certified) = {mp.nstr(worst_gap, 5)}')
