"""Independent verifier, part 5: branch and bound with centre/box jet pairs (iv_dual.TJ) in (a, d, eps).
Same acceptance test as iv_bb.py:  L_k(box) >= L_k(c) - sum_v |dL_k/dv (box)| r_v > 0 for k = 1, 2, 3.
Usage: python iv_bb2.py FORM a0 a1 d0 d1 NA ND NE [e0num e0den e1num e1den] > log
"""
import sys
import time
from fractions import Fraction as Fr
from flint import arb, fmpq
import iv_jet as JJ
from iv_jet import Jet, NotPos
import iv_dual as DU
from iv_dual import TJ, SP4
import iv_forms as FF

FORMS = {'nu': FF.logF_nu, 'nus': FF.logF_nus, 'mix': FF.logF_mix, 'nus2': FF.logF_nus2}
E37 = Fr(1, 37)


def q(x):
    return arb(fmpq(x.numerator, x.denominator))


def check(form, a0, a1, d0, d1, e0, e1):
    ac, dc, ec = (a0 + a1) / 2, (d0 + d1) / 2, (e0 + e1) / 2
    r = (q((a1 - a0) / 2), q((d1 - d0) / 2), q((e1 - e0) / 2))
    DU.RADII[:] = [arb(0, rv) for rv in r]
    V = []
    for t, (lo, hi, cc) in enumerate(((a0, a1, ac), (d0, d1, dc), (e0, e1, ec))):
        V.append(TJ(Jet.var(q(cc), t, SP4), Jet.var(arb.union(q(lo), q(hi)), t, SP4)))
    G = form(V[0], V[1], V[2])
    Lc = FF.conditions(G.c)
    grads = FF.gradients(G.final())
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
    nbox, nfail, nsplit, nerr = 0, 0, 0, 0
    worst = [None, None, None]
    last = t0
    while stack:
        box = stack.pop()
        try:
            lows, contrib, Lc = check(form, *box)
            ok = all(l > 0 for l in lows)
        except (NotPos, ZeroDivisionError) as ex:
            ok, lows, contrib = False, None, None
            if 'disjoint' in str(ex):
                nerr += 1
                log(f"TIGHTEN-DISJOINT on box {tuple(float(x) for x in box)}")
        if ok:
            nbox += 1
            for k in range(3):
                v = float(lows[k].lower())
                if worst[k] is None or v < worst[k][0]:
                    worst[k] = (v, tuple(float(x) for x in box))
            if time.time() - last > 120:
                last = time.time()
                log(f"  progress: {nbox} boxes, {nsplit} splits, stack {len(stack)}, {time.time() - t0:.0f} s, box {tuple(round(float(x), 4) for x in box)}")
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
    return nbox, nfail, nsplit, nerr, worst, time.time() - t0


if __name__ == '__main__':
    formname = sys.argv[1]
    a0, a1, d0, d1 = (Fr(x) for x in sys.argv[2:6])
    na, nd, ne = (int(x) for x in sys.argv[6:9])
    e0, e1 = Fr(0), E37
    if len(sys.argv) > 9:
        e0 = Fr(int(sys.argv[9]), int(sys.argv[10]))
        e1 = Fr(int(sys.argv[11]), int(sys.argv[12]))
    log = lambda s: print(s, flush=True)
    log(f"independent verifier (centre/box jets): form={formname} a=[{a0},{a1}] d=[{d0},{d1}] eps=[{e0},{e1}], initial grid {na}x{nd}x{ne}")
    nbox, nfail, nsplit, nerr, worst, dt = run(formname, a0, a1, d0, d1, e0, e1, na, nd, ne, log=log)
    log(f"boxes accepted: {nbox}, splits: {nsplit}, failures: {nfail}, tightening errors: {nerr}, time {dt:.1f} s")
    for k in range(3):
        if worst[k]:
            log(f"  smallest certified lower bound of L{k + 1}: {worst[k][0]:.6g} on box {worst[k][1]}")
    log("RESULT: REGION VERIFIED" if nfail == 0 and nerr == 0 else "RESULT: FAILED")
