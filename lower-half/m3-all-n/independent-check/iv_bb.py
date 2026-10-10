"""Independent verifier, part 3: branch and bound over boxes [a0,a1] x [d0,d1] x [e0,e1] (eps = 1/n).

For each box: L_k at the thin centre (jets with thin a, d, eps), gradients of L_k over the box (jets with ball
a, d, eps; naive ball arithmetic, no tightening), and the mean-value bound
    L_k(box) >= L_k(c) - |dL_k/da| r_a - |dL_k/dd| r_d - |dL_k/deps| r_e
(mean value theorem on the convex box; the gradient enclosures hold at every point of the box).  F > 0 on the box
follows from the box evaluation (log of D, Om_a, Om_b and sqrt of Gam_b Gam_d need positive enclosures).
Boxes failing are bisected in the direction with the largest contribution of the worst condition.
Usage: python iv_bb.py FORM a0 a1 d0 d1 NA ND NE [min_w] > log      (eps in [0, 1/37]; FORM = nu)
"""
import sys
import time
from fractions import Fraction as Fr
from flint import arb, fmpq
import iv_jet as JJ
from iv_jet import Jet, SP3, NotPos
import iv_forms as FF

FORMS = {'nu': FF.logF_nu}
E37 = Fr(1, 37)


def q(x):
    return arb(fmpq(x.numerator, x.denominator))


def check(form, a0, a1, d0, d1, e0, e1):
    ac, dc, ec = (a0 + a1) / 2, (d0 + d1) / 2, (e0 + e1) / 2
    Gc = form(Jet.var(q(ac), 0, SP3), Jet.var(q(dc), 1, SP3), Jet.var(q(ec), 2, SP3))
    Lc = FF.conditions(Gc)
    Ab = arb.union(q(a0), q(a1))
    Db = arb.union(q(d0), q(d1))
    Eb = arb.union(q(e0), q(e1))
    Gb = form(Jet.var(Ab, 0, SP3), Jet.var(Db, 1, SP3), Jet.var(Eb, 2, SP3))
    grads = FF.gradients(Gb)
    r = (q((a1 - a0) / 2), q((d1 - d0) / 2), q((e1 - e0) / 2))
    lows, contrib = [], []
    for k in range(3):
        cs = [abs(grads[k][v]) * r[v] for v in range(3)]
        lows.append(Lc[k] - cs[0] - cs[1] - cs[2])
        contrib.append([float(x.upper()) for x in cs])
    return lows, contrib, Lc


def run(formname, a0, a1, d0, d1, e0, e1, na, nd, ne, min_w=Fr(1, 2 ** 12), log=print):
    form = FORMS[formname]
    t0 = time.time()
    stack = []
    for i in range(na):
        for j in range(nd):
            for k in range(ne):
                stack.append((a0 + (a1 - a0) * i / na, a0 + (a1 - a0) * (i + 1) / na,
                              d0 + (d1 - d0) * j / nd, d0 + (d1 - d0) * (j + 1) / nd,
                              e0 + (e1 - e0) * k / ne, e0 + (e1 - e0) * (k + 1) / ne))
    nbox, nfail, nsplit = 0, 0, 0
    worst = [None, None, None]
    last = t0
    while stack:
        box = stack.pop()
        try:
            lows, contrib, Lc = check(form, *box)
            ok = all(l > 0 for l in lows)
        except (NotPos, ZeroDivisionError, ValueError):
            ok, lows, contrib = False, None, None
        if ok:
            nbox += 1
            for k in range(3):
                v = float(lows[k].lower())
                if worst[k] is None or v < worst[k][0]:
                    worst[k] = (v, tuple(float(x) for x in box))
            if time.time() - last > 120:
                last = time.time()
                log(f"  progress: {nbox} boxes, {nsplit} splits, stack {len(stack)}, {time.time() - t0:.0f} s")
            continue
        ba0, ba1, bd0, bd1, be0, be1 = box
        widths = (ba1 - ba0, bd1 - bd0, be1 - be0)
        if contrib is None:
            order = sorted(range(3), key=lambda v: -[float(widths[0]) / 4, float(widths[1]) / 4, float(widths[2]) * 37][v])
        else:
            k = min(range(3), key=lambda i: float(lows[i].lower()))
            order = sorted(range(3), key=lambda v: -contrib[k][v])
        done = False
        for v in order:
            if (v < 2 and widths[v] >= 2 * min_w) or (v == 2 and widths[2] >= 2 * E37 / 2 ** 12):
                lo, hi = box[2 * v], box[2 * v + 1]
                m = (lo + hi) / 2
                b1, b2 = list(box), list(box)
                b1[2 * v + 1] = m
                b2[2 * v] = m
                stack += [tuple(b1), tuple(b2)]
                nsplit += 1
                done = True
                break
        if not done:
            nfail += 1
            log(f"FAIL box {tuple(float(x) for x in box)} lows={lows}")
            if nfail > 20:
                break
    return nbox, nfail, nsplit, worst, time.time() - t0


if __name__ == '__main__':
    formname = sys.argv[1]
    a0, a1, d0, d1 = (Fr(x) for x in sys.argv[2:6])
    na, nd, ne = (int(x) for x in sys.argv[6:9])
    log = lambda s: print(s, flush=True)
    log(f"independent verifier: form={formname} a=[{a0},{a1}] d=[{d0},{d1}] eps=[0,1/37], initial grid {na}x{nd}x{ne}")
    nbox, nfail, nsplit, worst, dt = run(formname, a0, a1, d0, d1, Fr(0), E37, na, nd, ne, log=log)
    log(f"boxes accepted: {nbox}, splits: {nsplit}, failures: {nfail}, time {dt:.1f} s")
    for k in range(3):
        if worst[k]:
            log(f"  smallest certified lower bound of L{k + 1}: {worst[k][0]:.6g} on box {worst[k][1]}")
    log("RESULT: REGION VERIFIED" if nfail == 0 else "RESULT: FAILED")
