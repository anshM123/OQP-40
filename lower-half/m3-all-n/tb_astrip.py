"""Theorem B: the strip a -> 0 (s -> 1), for d in [d_lo, d_hi] with d_lo > 0.

Write F = sqrt(nu_b/nu_a) X / sqrt(om_a om_b) with X = E e^{-(a+b)/2}/(c nu_b) (X = O(a^2): E(1,t) = 0 and d_s E(1,t) = 0),
and use 1/nu_a = a phi1(-a eps), om_a = a^3 S(-a; eps) phi1(-a eps)/c (W(a) = e^a a^2 S(-a)).  Then F = a H with
    H = sqrt(nu_b phi1(-a eps)) Xt / sqrt(omt_a om_b),   Xt = X/a^2,   omt_a = S(-a) phi1(-a eps)/c,
and, with G = log H, the Lemma 4 conditions are equivalent (a > 0) to
    H > 0,  N1 = a L1 = 1 + a G_a >= 0,  N2 = L2 = -G_b >= 0,  N3 = a L3 = -G_b - a (G_ab + G_a G_b) >= 0.
Xt and its jets on a box with a in [a_lo, a_hi] are enclosed by the integral form of Taylor's theorem:
    d_a^i d_b^j d_eps^k Xt (a, b, eps) = int_0^1 (1-u) u^i (d_a^{i+2} d_b^j d_eps^k X)(u a, b, eps) du,
so the Taylor coefficient of a^i b^j eps^k of Xt lies in the hull of the coefficient of a^{i+2} b^j eps^k of X over
[0, a_hi] x (b-range) x (eps-range).  At the (thin) centre Xt = X/a^2 is computed directly.
X: for d >= 3 the scaled nu-form X = e^{-lam d} nu_d Dhat/(1+2eps) (as in tb_arb.logF_nu2), for d <= 3 the mixed
form X = Bm (as in tb_arb.logF_mixed3), both with nu_a (1 - e^{-a(1+2eps)}) = (1+2eps) phi1(-a(1+2eps))/phi1(-a eps).
Usage: python tb_astrip.py a_hi d_lo d_hi [na nd] > log
"""
import sys
import time
from fractions import Fraction as Fr
from flint import arb, fmpq
import tb_arb as T
from tb_arb import J, ZERO, ONE, MU, LAM

_AB_H = [(i, j) for i in range(5) for j in range(3) if (i, j) != (4, 2)]
MH = T.Mode([(i, j, 0) for (i, j) in _AB_H] + [(i, j, 1) for i in range(4) for j in range(2)])


def X_nu2(A, B, cx):
    eps, e1, e2 = cx.eps, cx.e1, cx.e2
    Dd = B - A
    nb, nd = T.nu_of(B, cx), T.nu_of(Dd, cx)
    ema, emb, emd = (-A).exp(), (-B).exp(), (-Dd).exp()
    ema3, emd3 = (-(A / 3)).exp(), (-(Dd / 3)).exp()
    yhb, yhd = 1 / (nb * cx.sqcp), 1 / (nd * cx.sqcp)
    phb = (-(2 * eps) * B).exp() + e2 * (-eps * B).exp() / nb
    phd = (-(2 * eps) * Dd).exp() + e2 * (-eps * Dd).exp() / nd
    uh1 = (-(2 * eps) * Dd).exp()
    nua_1m = e2 * (-(A * e2)).phi1() / (-(A * eps)).phi1()        # nu_a (1 - e^{-a(1+2eps)})
    uh2 = nua_1m * (-eps * Dd).exp() / nd
    uh = uh1 + uh2
    emd43 = emd * emd3
    Nt = ((yhb * ema3 - yhd) * (yhb * ema3 - yhd) + emd3 * (phb * ema + phd - 2 * uh) + emd43 * uh * uh
          + 2 * emd * ema3 * uh * yhb * yhd - phb * phd * ema * emd43 - phb * yhd * yhd * ema * emd
          - phd * yhb * yhb * ema3 * ema3 * emd)
    gb = 1 - phb * emb - yhb * yhb * (-(2 * B / 3)).exp()
    gd = 1 - phd * emd - yhd * yhd * emd3 * emd3
    kh = 1 - emd * uh - yhb * yhd * ema3 * emd3 * emd3
    sg = gb.sqrt() * gd.sqrt()
    dif = T.Phihat_of(B) * (-MU * A).exp() - T.Phihat_of(Dd)
    dif2 = dif * dif
    xx = dif2 * (-((2 * MU) * Dd)).exp()
    psi = (-xx).phi1()
    Dh = (-((arb(1) / 6 - LAM) * Dd)).exp() * Nt / (kh + sg) + sg * dif2 * psi
    return (-LAM * Dd).exp() * nd * Dh / e2


def X_mixed3(A, B, cx):
    eps, e1, e2 = cx.eps, cx.e1, cx.e2
    Dd = B - A
    nb = T.nu_of(B, cx)
    pb = (-(B * e2)).exp() + e2 * (-(B * e1)).exp() / nb
    yb = (-(B / 3)).exp() / (nb * cx.sqcp)
    gb = 1 - pb - yb * yb
    Pd = (Dd * e2).phi1() / (Dd * eps).phi1()
    q = (-(A * e2)).phi1() / (-(A * eps)).phi1()                    # nu_a (1 - e^{-a(1+2eps)})/(1+2eps)
    x = T.Phihat_of(B) * (-MU * B).exp() - T.Phihat_of(Dd) * (-MU * Dd).exp()
    R = (-(x * x)).exp()
    Sd = T.S_of(Dd, cx)
    return ((-(Dd * (arb(1) / 2 + eps))).exp() * (Pd - q)
            - (-(A / 3)).exp() * (-(Dd / 6)).exp() / (cx.c * nb)
            - (cx.cp * gb).sqrt() / cx.c * Dd * Sd.sqrt() * R)


def logH_rest(A, B, cx):
    """log H - log Xt = (log nu_b + log phi1(-a eps))/2 - (log omt_a + log om_b)/2."""
    eps, e2 = cx.eps, cx.e2
    nb = T.nu_of(B, cx)
    p1 = (-(A * eps)).phi1()
    omt_a = T.S_of(-A, cx) * p1 / cx.c
    omb = 1 - nb * (1 - (-(B * e2)).exp()) / e2 - (-(B / 3)).exp() / (cx.c * nb)
    return (nb.log() + p1.log()) / 2 - (omt_a.log() + omb.log()) / 2


def shift2(Xh, mode):
    """jet (mode) whose coefficient (i,j,k) is the coefficient (i+2,j,k) of the MH jet Xh."""
    c = [ZERO] * mode.n
    for idx, (i, j, k) in enumerate(mode.monos):
        c[idx] = Xh.c[MH.idx[(i + 2, j, k)]]
    return J(c, mode)


def A_(x):
    return arb(fmpq(x.numerator, x.denominator))


def norm_conditions(G, a):
    Ga, Gb, Gab = G.coef(1, 0), G.coef(0, 1), G.coef(1, 1)
    return [1 + a * Ga, -Gb, -Gb - a * (Gab + Ga * Gb)]


def norm_gradients(G, a):
    c100, c010, c110 = G.coef(1, 0), G.coef(0, 1), G.coef(1, 1)
    c200, c020, c210, c120 = G.coef(2, 0), G.coef(0, 2), G.coef(2, 1), G.coef(1, 2)
    c101, c011, c111 = G.coef(1, 0, 1), G.coef(0, 1, 1), G.coef(1, 1, 1)
    g1 = (c100 + 2 * a * c200, a * c110, a * c101)
    g2 = (-c110, -2 * c020, -c011)
    g3 = (-2 * c110 - 2 * a * c210 - c100 * c010 - 2 * a * c200 * c010 - a * c100 * c110,
          -2 * c020 - 2 * a * c120 - a * c110 * c010 - 2 * a * c100 * c020,
          -c011 - a * c111 - a * c101 * c010 - a * c100 * c011)
    return g1, g2, g3


def check_box(a0, a1, d0, d1, e0, e1):
    if d0 < 3 < d1:
        raise T.NotPositive('box straddles the form switch')
    Xf = X_nu2 if d0 >= 3 else X_mixed3
    ac, dc, ec = (a0 + a1) / 2, (d0 + d1) / 2, (e0 + e1) / 2
    ra, rd, re = (a1 - a0) / 2, (d1 - d0) / 2, (e1 - e0) / 2
    # centre (thin)
    cx = T.Ctx(A_(ec))
    Ga = J.var(A_(ac), 0, T.MP)
    Gb = J.var(A_(ac) + A_(dc), 1, T.MP)
    Xc = Xf(Ga, Gb, cx)
    G = (Xc / (Ga * Ga)).log() + logH_rest(Ga, Gb, cx)
    Nc = norm_conditions(G, A_(ac))
    # box: Xt from the hull of the order-(i+2) coefficients of X over [0, a1] x b-range x eps-range
    eb = arb.union(A_(e0), A_(e1))
    E = J.var(eb, 2, MH)
    cxh = T.Ctx(E)
    ah = arb.union(arb(0), A_(a1))
    bh = arb.union(A_(a0) + A_(d0), A_(a1) + A_(d1))
    Xh = Xf(J.var(ah, 0, MH), J.var(bh, 1, MH), cxh)
    Xt = shift2(Xh, T.MBE)
    if not (Xt.c[0] > 0):
        raise T.NotPositive('Xt not positive on the box')
    Eb = J.var(eb, 2, T.MBE)
    cxb = T.Ctx(Eb)
    ab = arb.union(A_(a0), A_(a1))
    db = arb.union(A_(d0), A_(d1))
    Ga = J.var(ab, 0, T.MBE)
    Gb = J.var(ab + db, 1, T.MBE)
    Gbox = Xt.log() + logH_rest(Ga, Gb, cxb)
    grads = norm_gradients(Gbox, ab)
    lows = []
    for k in range(3):
        ga, gb, ge = grads[k]
        lows.append(Nc[k] + (ga + gb) * arb(0, A_(ra)) + gb * arb(0, A_(rd)) + ge * arb(0, A_(re)))
    return lows


def run(a_hi, d_lo, d_hi, na=4, nd=16, log=print):
    t0 = time.time()
    e_lo, e_hi = Fr(0), Fr(1, 37)
    stack = []
    for i in range(na):
        for j in range(nd):
            stack.append((a_hi * i / na, a_hi * (i + 1) / na, d_lo + (d_hi - d_lo) * j / nd,
                          d_lo + (d_hi - d_lo) * (j + 1) / nd, e_lo, e_hi))
    nbox, nfail = 0, 0
    worst = [None] * 3
    while stack:
        box = stack.pop()
        a0, a1, d0, d1, e0, e1 = box
        if d0 < 3 < d1:
            stack += [(a0, a1, d0, Fr(3), e0, e1), (a0, a1, Fr(3), d1, e0, e1)]
            continue
        try:
            lows = check_box(*box)
            ok = all(l > 0 for l in lows)
        except (T.NotPositive, ValueError, ZeroDivisionError):
            ok, lows = False, None
        if ok:
            nbox += 1
            if nbox % 2000 == 0:
                log(f"  progress: {nbox} boxes, stack {len(stack)}, {time.time() - t0:.0f} s")
            for k in range(3):
                v = float(lows[k].lower())
                if worst[k] is None or v < worst[k][0]:
                    worst[k] = (v, tuple(float(x) for x in box))
            continue
        wa, wd, we = a1 - a0, d1 - d0, e1 - e0
        if wa < Fr(1, 2 ** 16) and wd < Fr(1, 2 ** 16):
            nfail += 1
            log(f"FAIL box {tuple(float(x) for x in box)} lows={lows}")
            if nfail > 10:
                break
            continue
        # split the a-width first while the hull region [0, a1] x b-range reaches d < 0 or d across 3,
        # otherwise the largest relative width
        if a0 + d0 - a1 < 0 or (d0 < 3 and a1 + d1 > 3 and d0 + a0 - a1 < 3 and d0 >= 3):
            dim = 0
        else:
            sc = [float(wa) / max(float(d0), 1e-9), float(wd) / max(1.0, float(d0)), float(we) * 37 * 0.5]
            dim = max(range(3), key=lambda i: sc[i])
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
    a_hi, d_lo, d_hi = Fr(sys.argv[1]), Fr(sys.argv[2]), Fr(sys.argv[3])
    na = int(sys.argv[4]) if len(sys.argv) > 4 else 4
    nd = int(sys.argv[5]) if len(sys.argv) > 5 else 16
    print(f"a-strip: a in (0, {a_hi}], d in [{d_lo}, {d_hi}], eps in [0, 1/37]", flush=True)
    nbox, nfail, worst, dt = run(a_hi, d_lo, d_hi, na, nd, log=lambda s: print(s, flush=True))
    print(f"boxes accepted: {nbox}, failures: {nfail}, time {dt:.1f} s")
    for k in range(3):
        if worst[k]:
            print(f"  certified min lower bound of N{k + 1}: {worst[k][0]:.6g} on box {worst[k][1]}")
    print("RESULT: REGION VERIFIED" if nfail == 0 else "RESULT: FAILED")
