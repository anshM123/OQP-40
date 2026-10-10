"""Theorem B: verified branch and bound for the Lemma 4 conditions of the Gaussian-design certificate on a region
[a_lo, a_hi] x [d_lo, d_hi] (scaled variables) for all eps = 1/n in [eps_lo, eps_hi] (eps an interval variable).

On a box with centre c and half-widths (r_a, r_d, r_e) each condition L_k (k = 1, 2, 3) is enclosed by the centred
form  L_k(box) in L_k(c) + (d_a + d_b) L_k(box) [-r_a, r_a] + d_b L_k(box) [-r_d, r_d] + d_eps L_k(box) [-r_e, r_e]
(the directions of the box edges are d/da at fixed d, = d_a + d_b, and d/dd at fixed a, = d_b).  L_k(c) is computed
with thin balls; the gradients with jets over the whole box (eps a jet variable).  F > 0 on the box follows from the
box evaluation itself (it takes logarithms and square roots of quantities whose enclosures must be positive).
A box is accepted if all three lower bounds are > 0; otherwise it is bisected.
Usage: python tb_bb.py FORM a_lo a_hi d_lo d_hi eps_lo_num eps_lo_den eps_hi_num eps_hi_den [init_na init_nd] > log
"""
import sys
import time
from fractions import Fraction as Fr
from flint import arb, fmpq
import tb_arb as T

FORMS = {'nu2': T.logF_nu2, 'mixed2': T.logF_mixed2, 'mixed3': T.logF_mixed3, 'nu4': T.logF_nu4, 'nu5': T.logF_nu5, 'mixed5': T.logF_mixed5}


def A(x):
    return arb(fmpq(x.numerator, x.denominator))


def check_box(form, a0, a1, d0, d1, e0, e1):
    if DUAL:
        Lc, grads = T.dual_box(form, a0, a1, d0, d1, e0, e1)
        ra, rd, re = (a1 - a0) / 2, (d1 - d0) / 2, (e1 - e0) / 2
        lows, contrib = [], []
        for k in range(3):
            ga, gb, ge = grads[k]
            ca, cd, ce = abs(ga + gb) * A(ra), abs(gb) * A(rd), abs(ge) * A(re)
            lows.append(Lc[k] - ca - cd - ce)
            contrib.append((float(ca.upper()) if ra else 0.0, float(cd.upper()) if rd else 0.0, float(ce.upper()) if re else 0.0))
        return lows, contrib, Lc
    return check_box_plain(form, a0, a1, d0, d1, e0, e1)


DUAL = False


def check_box_plain(form, a0, a1, d0, d1, e0, e1):
    ac, dc, ec = (a0 + a1) / 2, (d0 + d1) / 2, (e0 + e1) / 2
    ra, rd, re = (a1 - a0) / 2, (d1 - d0) / 2, (e1 - e0) / 2
    cx = T.Ctx(A(ec))
    Ga = T.J.var(A(ac), 0, T.MP)
    Gb = T.J.var(A(ac) + A(dc), 1, T.MP)
    Lc, _ = T.margins_from_logF(form(Ga, Gb, cx))
    ab = arb.union(A(a0), A(a1))
    db = arb.union(A(d0), A(d1))
    eb = arb.union(A(e0), A(e1))
    E = T.J.var(eb, 2, T.MBE)
    cxb = T.Ctx(E)
    Ga = T.J.var(ab, 0, T.MBE)
    Gd = T.dvar(db, T.MBE)
    Gb = Ga + Gd
    _, grads = T.margins_from_logF(form(Ga, Gb, cxb, Gd))
    lows, contrib = [], []
    for k in range(3):
        ga, gb, ge = grads[k]
        ca = abs(ga + gb) * A(ra)
        cd = abs(gb) * A(rd)
        ce = abs(ge) * A(re)
        lo = Lc[k] - ca - cd - ce
        lows.append(lo)
        contrib.append((float(ca.upper()) if ra else 0.0, float(cd.upper()) if rd else 0.0, float(ce.upper()) if re else 0.0))
    return lows, contrib, Lc


def run(formname, a0, a1, d0, d1, e0, e1, na=8, nd=8, min_width=Fr(1, 2 ** 12), log=print):
    form = FORMS[formname]
    t0 = time.time()
    stack = []
    for i in range(na):
        for j in range(nd):
            stack.append((a0 + (a1 - a0) * i / na, a0 + (a1 - a0) * (i + 1) / na,
                          d0 + (d1 - d0) * j / nd, d0 + (d1 - d0) * (j + 1) / nd, e0, e1))
    nbox, nfail = 0, 0
    worst = [None, None, None]
    while stack:
        box = stack.pop()
        b_a0, b_a1, b_d0, b_d1, b_e0, b_e1 = box
        try:
            lows, contrib, Lc = check_box(form, *box)
            ok = all(l > 0 for l in lows)
        except (T.NotPositive, ValueError, ZeroDivisionError) as ex:
            ok, lows, contrib = False, None, None
        if ok:
            nbox += 1
            if nbox % 5000 == 0:
                log(f"  progress: {nbox} boxes accepted, stack {len(stack)}, {time.time() - t0:.0f} s, last box a=[{float(b_a0):.4g},{float(b_a1):.4g}] d=[{float(b_d0):.4g},{float(b_d1):.4g}]")
            for k in range(3):
                v = float(lows[k].lower())
                if worst[k] is None or v < worst[k][0]:
                    worst[k] = (v, tuple(float(x) for x in box))
            continue
        # split
        wa, wd, we = b_a1 - b_a0, b_d1 - b_d0, b_e1 - b_e0
        if contrib is None:
            # choose the widest (relative to scale) direction
            dims = [(float(wa) / max(1.0, float(b_a0)), 0), (float(wd) / max(1.0, float(b_d0)), 1), (float(we) * 37, 2)]
            dim = max(dims)[1]
        else:
            # the failing condition with the smallest lower bound; split the largest contribution
            k = min(range(3), key=lambda i: float(lows[i].lower()))
            dim = max(range(3), key=lambda i: contrib[k][i])
        if max(wa, wd) < min_width and we < Fr(1, 2 ** 20):
            nfail += 1
            log(f"FAIL box a=[{float(b_a0)},{float(b_a1)}] d=[{float(b_d0)},{float(b_d1)}] eps=[{float(b_e0)},{float(b_e1)}] lows={lows}")
            if nfail > 20:
                break
            continue
        if dim == 0:
            m = (b_a0 + b_a1) / 2
            stack += [(b_a0, m, b_d0, b_d1, b_e0, b_e1), (m, b_a1, b_d0, b_d1, b_e0, b_e1)]
        elif dim == 1:
            m = (b_d0 + b_d1) / 2
            stack += [(b_a0, b_a1, b_d0, m, b_e0, b_e1), (b_a0, b_a1, m, b_d1, b_e0, b_e1)]
        else:
            m = (b_e0 + b_e1) / 2
            stack += [(b_a0, b_a1, b_d0, b_d1, b_e0, m), (b_a0, b_a1, b_d0, b_d1, m, b_e1)]
    dt = time.time() - t0
    return nbox, nfail, worst, dt


if __name__ == '__main__':
    if sys.argv[1] == '--dual':
        DUAL = True
        sys.argv.pop(1)
    formname = sys.argv[1]
    a0, a1, d0, d1 = (Fr(x) for x in sys.argv[2:6])
    e0 = Fr(int(sys.argv[6]), int(sys.argv[7]))
    e1 = Fr(int(sys.argv[8]), int(sys.argv[9]))
    na = int(sys.argv[10]) if len(sys.argv) > 10 else 8
    nd = int(sys.argv[11]) if len(sys.argv) > 11 else 8
    print(f"region form={formname} a=[{a0},{a1}] d=[{d0},{d1}] eps=[{e0},{e1}]", flush=True)
    nbox, nfail, worst, dt = run(formname, a0, a1, d0, d1, e0, e1, na, nd, log=lambda s: print(s, flush=True))
    print(f"boxes accepted: {nbox}, failures: {nfail}, time {dt:.1f} s")
    for k in range(3):
        if worst[k]:
            print(f"  certified min lower bound of L{k + 1}: {worst[k][0]:.6g} on box {worst[k][1]}")
    print("RESULT: REGION VERIFIED" if nfail == 0 else "RESULT: FAILED")
