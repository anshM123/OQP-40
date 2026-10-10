"""Theorem B: the strip 0 < a <= a_max (s -> 1), for d >= d_min > 0, all eps in [0, 1/37].

F = a H with H = sqrt(nu_b phi1(-a eps)) Xt / sqrt(omt_a om_b), Xt = X/a^2, X = E e^{-(a+b)/2}/(c nu_b),
omt_a = S(-a) phi1(-a eps)/c, i.e. log H = log Xt + bpart(b) + (log c - log S(-a))/2 with
bpart = (log nu_b - log om_b)/2 (tb_arb.bpart).  With G = log H the Lemma 4 conditions are equivalent (a > 0) to
    H > 0,  N1 = 1 + a G_a >= 0,  N2 = -G_b >= 0,  N3 = -G_b - a (G_ab + G_a G_b) >= 0.
Centred form in (a, d, eps) for N1, N2, N3: the centre values come from thin balls (Xt = X/a_c^2 computed directly,
a_c > 0); the gradients over the box come from a dual jet of G whose box part for Xt is obtained from the integral
form of Taylor's theorem (X(0,b) = d_a X(0,b) = 0 for every eps = 1/n and for the limit):
    d_a^i d_b^j d_eps^k Xt (a, b, eps) = int_0^1 (1-u) u^i (d_a^{i+2} d_b^j d_eps^k X)(u a, b, eps) du,
so each Taylor coefficient of Xt on the box lies in the hull of the corresponding order-(i+2) coefficient of X over
[0, a1] x (b-range) x (eps-range) (naive enclosure), and is then tightened by the mean-value form around the centre
(tb_arb.tighten).  X is evaluated with the forms of tb_astrip.py (d >= 3) or with the mixed form with
c2 gam_b = b^4 phi1(-b eps)^2 S(b) e^{-b} (d < 3, no cancellation for small b).
Usage: python tb_astrip5.py a_max d_min d_max na nd > log
"""
import sys
import time
from fractions import Fraction as Fr
from flint import arb, fmpq
import tb_arb as T
import tb_astrip as AS
from tb_arb import J, DJ, MT, ZERO, ONE, MU, LAM


def _closure(monos):
    s = set()
    for (i, j, k) in monos:
        for a in range(i + 1):
            for b in range(j + 1):
                for c in range(k + 1):
                    s.add((a, b, c))
    return sorted(s, key=lambda m: (m[2], m[0] + m[1], m))


MH2 = T.Mode(_closure([(i + 2, j, k) for (i, j, k) in MT.monos]))


def X_mixed5(A, B, cx):
    eps, e1, e2 = cx.eps, cx.e1, cx.e2
    Dd = B - A
    nb = T.nu_of(B, cx)
    Pd = (Dd * e2).phi1() / (Dd * eps).phi1()
    q = (-(A * e2)).phi1() / (-(A * eps)).phi1()
    x = T.Phihat_of(B) * (-MU * B).exp() - T.Phihat_of(Dd) * (-MU * Dd).exp()
    R = (-(x * x)).exp()
    Sd = T.S_of(Dd, cx)
    return ((-(Dd * (arb(1) / 2 + eps))).exp() * (Pd - q)
            - (-(A / 3)).exp() * (-(Dd / 6)).exp() / (cx.c * nb)
            - T.cpgam(B, cx).sqrt() / cx.c * Dd * Sd.sqrt() * R)


def q_(x):
    return arb(fmpq(x.numerator, x.denominator))


def shift2(Xh):
    c = [ZERO] * MT.n
    for idx, (i, j, k) in enumerate(MT.monos):
        c[idx] = Xh.c[MH2.idx[(i + 2, j, k)]]
    return J(c, MT)


def check_box(a0, a1, d0, d1, e0, e1):
    if d0 < 3 < d1:
        raise T.NotPositive('box straddles d = 3')
    Xf = AS.X_nu2 if d0 >= 3 else X_mixed5
    ac, dc, ec = (a0 + a1) / 2, (d0 + d1) / 2, (e0 + e1) / 2
    ra, rd, re = (a1 - a0) / 2, (d1 - d0) / 2, (e1 - e0) / 2
    T.TIGHT['r'] = (arb(0, q_(ra)), arb(0, q_(rd)), arb(0, q_(re)))
    # centre: thin
    Ac = J.var(q_(ac), 0, MT)
    Dc = T.dvar(q_(dc), MT)
    Ec = J.var(q_(ec), 2, MT)
    cxc = T.Ctx(Ec)
    Xc = Xf(Ac, Ac + Dc, cxc)
    Xtc = Xc / (Ac * Ac)
    # box: hull of the order-(i+2) coefficients of X over [0, a1] x b-range x eps-range
    eb = arb.union(q_(e0), q_(e1))
    Eh = J.var(eb, 2, MH2)
    cxh = T.Ctx(Eh)
    ah = arb.union(arb(0), q_(a1))
    bh = arb.union(q_(a0) + q_(d0), q_(a1) + q_(d1))
    Xh = Xf(J.var(ah, 0, MH2), J.var(bh, 1, MH2), cxh)
    Xtb = T.tighten(shift2(Xh), Xtc)
    if not (Xtb.c[0] > 0):
        raise T.NotPositive('Xt not positive on the box')
    # rest = bpart(b) + (log c - log S(-a))/2 as dual jets
    Ab = J.var(arb.union(q_(a0), q_(a1)), 0, MT)
    Db = T.dvar(arb.union(q_(d0), q_(d1)), MT)
    Eb = J.var(eb, 2, MT)
    A = DJ(Ac, Ab)
    D = DJ(Dc, Db)
    B = A + D
    cx = T.DCtx(Ec, Eb)
    rest = T.bpart(B, cx) + (cx.c.log() - T.S_of(-A, cx).log()) / 2
    G = DJ(Xtc, Xtb).log() + rest
    Nc = AS.norm_conditions(G.cj, q_(ac))
    grads = AS.norm_gradients(T.tighten(G.bj, G.cj), Ab.c[0])
    lows, contrib = [], []
    for k in range(3):
        ga, gb, ge = grads[k]
        ca, cd, ce = (ga + gb) * arb(0, q_(ra)), gb * arb(0, q_(rd)), ge * arb(0, q_(re))
        lows.append(Nc[k] + ca + cd + ce)
        contrib.append((float(ca.rad()), float(cd.rad()), float(ce.rad())))
    return lows, contrib, Nc


def run(a_max, d_min, d_max, na, nd, log=print):
    t0 = time.time()
    stack = []
    for i in range(na):
        for j in range(nd):
            stack.append((a_max * i / na, a_max * (i + 1) / na, d_min + (d_max - d_min) * j / nd,
                          d_min + (d_max - d_min) * (j + 1) / nd, Fr(0), Fr(1, 37)))
    nbox, nfail = 0, 0
    worst = [None] * 3
    while stack:
        box = stack.pop()
        a0, a1, d0, d1, e0, e1 = box
        if d0 < 3 < d1:
            stack += [(a0, a1, d0, Fr(3), e0, e1), (a0, a1, Fr(3), d1, e0, e1)]
            continue
        if a1 - a0 > d0:                       # the hull region needs d = b - a' >= 0 for a' in [0, a1]
            m = (a0 + a1) / 2
            stack += [(a0, m, d0, d1, e0, e1), (m, a1, d0, d1, e0, e1)]
            continue
        try:
            lows, contrib, Nc = check_box(*box)
            ok = all(l > 0 for l in lows)
        except (T.NotPositive, ValueError, ZeroDivisionError):
            ok, lows, contrib = False, None, None
        if ok:
            nbox += 1
            if nbox % 2000 == 0:
                log(f"  progress: {nbox} boxes, stack {len(stack)}, {time.time() - t0:.0f} s, last a=[{float(a0):.4g},{float(a1):.4g}] d=[{float(d0):.4g},{float(d1):.4g}]")
            for k in range(3):
                v = float(lows[k].lower())
                if worst[k] is None or v < worst[k][0]:
                    worst[k] = (v, tuple(float(x) for x in box))
            continue
        wa, wd, we = a1 - a0, d1 - d0, e1 - e0
        if contrib is None:
            dim = 0 if float(wa) >= float(wd) / max(1.0, float(d0)) else 1
        else:
            k = min(range(3), key=lambda i: float(lows[i].lower()))
            dim = max(range(3), key=lambda i: contrib[k][i])
        if (dim == 0 and wa < Fr(1, 2 ** 14)) or (dim == 1 and wd < Fr(1, 2 ** 14)) or (dim == 2 and we < Fr(1, 2 ** 22)):
            nfail += 1
            log(f"FAIL box {tuple(float(x) for x in box)} lows={lows}")
            if nfail > 10:
                break
            continue
        if dim == 0:
            m = (a0 + a1) / 2
            stack += [(a0, m, d0, d1, e0, e1), (m, a1, d0, d1, e0, e1)]
        elif dim == 1:
            m = (d0 + d1) / 2
            stack += [(a0, a1, d0, m, e0, e1), (a0, a1, m, d1, e0, e1)]
        else:
            m = (e0 + e1) / 2
            stack += [(a0, a1, d0, d1, e0, m), (a0, a1, d0, d1, m, e1)]
    return nbox, nfail, worst, time.time() - t0


if __name__ == '__main__':
    a_max, d_min, d_max = Fr(sys.argv[1]), Fr(sys.argv[2]), Fr(sys.argv[3])
    na, nd = int(sys.argv[4]), int(sys.argv[5])
    print(f"strip: 0 < a <= {a_max}, d in [{d_min}, {d_max}], eps in [0, 1/37]", flush=True)
    nbox, nfail, worst, dt = run(a_max, d_min, d_max, na, nd, log=lambda s: print(s, flush=True))
    print(f"boxes accepted: {nbox}, failures: {nfail}, time {dt:.1f} s")
    for k in range(3):
        if worst[k]:
            print(f"  certified min lower bound of N{k + 1}: {worst[k][0]:.6g} on box {worst[k][1]}")
    print("RESULT: REGION VERIFIED" if nfail == 0 else "RESULT: FAILED")
