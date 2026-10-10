"""End-to-end soundness test of the strip code for the forms not covered by iv_selftest2 (which tested the direct form):
the corner box of run S0 and random boxes of the nu form (as in runs S2 with the 'box' option, and S3).  The certified
lower bounds that the driver uses for acceptance (iv_as.conditions_c: a L1, L2 or b L2, a L3 or a b L3) must not exceed
the true values from the definitions (ref_defs.margins) at points of the box with eps = 1/n, and at eps = 0."""
import random
from fractions import Fraction as Fr
import mpmath as mp
import iv_as as AS
from ref_defs import margins

rnd = random.Random(4049)
E = Fr(1, 37)
viol = chk = 0


def true_vals(n, a, b):
    F0, L1, L2, L3 = margins(n, float(a), float(b - a), dps=int(120 + 0.3 * float(b)),
                             h=mp.mpf(10) ** -30 * min(1, float(a), float(b - a)))
    a_, b_ = mp.mpf(float(a)), mp.mpf(float(b))
    return {'aL1': a_ * L1, 'L2': L2, 'bL2': b_ * L2, 'aL3': a_ * L3, 'abL3': a_ * b_ * L3}


def ns_in(e0, e1):
    out = [n for n in range(37, 100000) if e0 <= Fr(1, n) <= e1][:2]
    if e0 == 0:
        out.append(None)
    return out


def test_box(form, a0, a1, b0, b1, e0, e1, corner=False, box=False, npts=3):
    global viol, chk
    AS.Ctl.BOX = box
    r = AS.evaluate(form, a0, a1, b0, b1, e0, e1, corner=corner)
    ok, out, contrib = AS.conditions_c(r)
    lows = {k: v for k, v in out.items() if k in ('aL1', 'L2', 'bL2', 'aL3', 'abL3')}
    for n in ns_in(e0, e1):
        for _ in range(npts):
            a = a0 + (a1 - a0) * Fr(rnd.randrange(1, 100), 100)
            b = b0 + (b1 - b0) * Fr(rnd.randrange(1, 100), 100)
            if b <= a:
                continue
            tv = true_vals(n, a, b)
            for k, lo in lows.items():
                chk += 1
                if tv[k] < mp.mpf(lo.lower().str(40, radius=False)) - mp.mpf('1e-25'):
                    viol += 1
                    print('STRIP VIOLATION', form, [float(x) for x in (a0, a1, b0, b1, e0, e1)], n, float(a), float(b), k, tv[k], lo)
    print(f'{form}{" corner" if corner else ""}{" box" if box else ""} box a=[{float(a0):.4g},{float(a1):.4g}] '
          f'b=[{float(b0):.5g},{float(b1):.5g}] eps=[{float(e0):.4f},{float(e1):.4f}] accepted={ok} '
          f'lows={ {k: round(float(v.lower()), 5) for k, v in lows.items()} }', flush=True)


# the corner box of run S0 (accepted there as one box)
test_box('direct', Fr(0), Fr(1, 4), Fr(0), Fr(1, 4), Fr(0), E, corner=True, npts=6)
# nu form, S2-type boxes (b in [x1 + 15/4, 8], 'box' option) and S3-type boxes (b in [15/2, 515])
for it in range(8):
    x0 = Fr(rnd.randrange(0, 24), 8)
    x1 = x0 + Fr(1, 8)
    if rnd.random() < 0.5:
        b0 = x1 + Fr(15, 4) + Fr(rnd.randrange(0, 30), 16)
        b1 = b0 + Fr(1, 32)
        box = True
    else:
        b0 = Fr(rnd.choice([8, 12, 20, 37, 60, 150, 300, 500]))
        b1 = b0 + b0 / 64
        box = False
    k = rnd.randrange(16)
    test_box('nu', x0, x1, b0, b1, E * k / 16, E * (k + 1) / 16, box=box)
print(f'strip nu/corner soundness test: {chk} comparisons, {viol} violations')
