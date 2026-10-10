"""Thin-point check of iv_as (both forms) against the definitions (ref_defs.margins)."""
import random
from fractions import Fraction as Fr
import mpmath as mp
mp.mp.dps = 60
from flint import arb, fmpq
import iv_as as AS
from ref_defs import margins
rnd = random.Random(4)
worst = {}
for it in range(24):
    n = rnd.choice([37, 50, 100, 1000, None])
    form = rnd.choice(['direct', 'direct', 'nu'])
    a = Fr(rnd.randrange(1, 3 * 64), 64) if rnd.random() < 0.8 else Fr(1, 1000)
    if form == 'direct':
        b = a + Fr(rnd.randrange(1, 4 * 64), 64)
        if b > 7:
            b = Fr(7)
    else:
        b = a + Fr(rnd.randrange(5 * 8, 300 * 8), 8)
    e = Fr(0) if n is None else Fr(1, n)
    r = AS.evaluate(form, a, a, b, b, e, e)
    ga, gb, gab = AS.coef_on_box(r, 1, 0), AS.coef_on_box(r, 0, 1), AS.coef_on_box(r, 1, 1)
    F0, L1, L2, L3 = margins(n, float(a), float(b - a), dps=int(170 + 0.3 * float(b)), h=mp.mpf(10) ** -35 * min(1, float(a)))
    ref = (L1 - 1 / mp.mpf(a.numerator) * a.denominator, 1 / (mp.mpf(b.numerator) / b.denominator) - L2, L1 * L2 - L3)
    got = [mp.mpf(x.mid().str(50, radius=False)) for x in (ga, gb, gab)]
    dev = max(abs(g - r_) / max(abs(r_), mp.mpf('1e-3')) for g, r_ in zip(got, ref))
    worst[form] = max(worst.get(form, 0), dev)
    print(f"{form:6s} n={n} a={float(a):.5f} b={float(b):.4f}: Ghat_a {mp.nstr(got[0], 10)} ({mp.nstr(ref[0], 10)}), "
          f"Ghat_b {mp.nstr(got[1], 10)}, Ghat_ab {mp.nstr(got[2], 10)} ({mp.nstr(ref[2], 10)}); radii "
          f"{float(ga.rad()):.1e}; rel.dev {mp.nstr(dev, 3)}", flush=True)
print("worst:", {k: mp.nstr(v, 3) for k, v in worst.items()})
