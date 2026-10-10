"""Theorem B, strip: the far tail d >= 512 for 0 <= a <= 3 (all eps in [0, 1/37]).

As in tb_dtail.py (chart C4, RESULTS.md 8.3), with w = 1/d, m_d = nu_d - eps in [0, w] and d-jets from (w, eps) cells,
but for G = log(F/a) (F = a H; no division by a anywhere):
  G = -lam d + log(d nu_d) + (log nu_b - log om_b)/2 - log S(-a)/2 + log(c)/2 - log(1+2eps) + log(Dhat/(a^2 d)),
  Dhat/(a^2 d) = sg (M/a)^2 psi + tau (Ntil nu_d^2/a^2)/(khat + sg),
  M/a = phit_d g(a, w) + sqrt(1 + a w) e^{-mu a} (phit_d - phit_b)/a,
  g(a, w) = (1 - sqrt(1 + a w) e^{-mu a})/a = -v phi1(a v),  v = -mu + (w/2) L1(a w),  L1(x) = log(1+x)/x,
(from Phihat(z) = -sqrt(z) phit(z): Phihat_b e^{-mu a} - Phihat_d = sqrt(d) [phit_d - sqrt(1 + a w) phit_b e^{-mu a}] and
-log a - log S(-a)/2 + log(c)/2 = -(log nu_a + log om_a)/2, nu_a om_a = a^2 S(-a)/c).  Bounds (b = a + d >= 512):
  (phit_d - phit_b)/a = -int_0^1 phit'(b - (1-u) a) du: its (a, b)-Taylor coefficients of order i + j <= 3 are at most
    (1+i+j)!/(i! j! (i+1)) max |phit^{(m)}/m!| <= 24 * 3.6e-19 < 1e-17 (Lemma T': |phit^{(m)}(z)/m!| <= 2(z+1)
    e^{-(1/6-lam)(z-1)} <= 3.6e-19 for z >= 512, Cauchy on unit discs); enclosed in [-1e-15, 1e-15];
  phit_d - sqrt(eta), sg - 1, psi - 1, om_b - 1 + nu_b/(1+2eps): as in Lemma T'' (all <= 1e-12 with coefficients);
  the tau-term: Ntil nu_d^2 = T1 + T2, T1/a^2 = ((nu_d/nu_b) e^{-a/3} - 1)^2/(a^2 c') with
    ((nu_d/nu_b) e^{-a/3} - 1)/a = -(1/3+eps) phi1(-a(1/3+eps)) + nu_d phi1(-a eps) e^{-a/3}, |.| <= 2 on complex unit discs
    around real a in [0, 3], so T1/a^2 <= 4/c' <= 2.2; T2 (the remaining terms of the perfect square N, times
    e^{2d/3} nu_d^2) is <= 20 (2 + b)^2 e^{-(d-1)/3} on the same discs and vanishes to second order at a = 0, so
    |T2/a^2| <= 1e-60 with all coefficients; tau <= d e^{-(1/6-lam) d}, khat + sg >= 1: the tau-term with its coefficients
    of order <= 3 is <= 512 e^{-49} * 2.3 * e < 1e-15 for d >= 512; enclosed in [-1e-12, 1e-12].
Conditions (F = a H, G = log H): N1 = 1 + a G_a, N2 = -G_b, N3 = -G_b - a (G_ab + G_a G_b) (= a L1, L2, a L3), centre values
plus the a-gradient (d/da at fixed d = d_a + d_b) on the box times the a-radius; the (w, eps) cells enclose everything.
Usage: python tb_sx_dtail.py D a_lo a_hi n_w n_eps n_a > log
"""
import sys
import time
from fractions import Fraction as Fr
from math import factorial
from flint import arb, fmpq
import tb_arb as T
from tb_arb import J, ZERO, ONE, MU, LAM, ETA
from tb_dtail import q, djet_from, atom_jet, m_range

XA = arb('1e-12')
XP = arb('1e-15')
N_L1 = 30


def g_L1(x0, K):
    """Taylor coefficients at x0 (|x0| <= 1/100) of L1(x) = log(1+x)/x = sum_k (-1)^k x^k/(k+1);
    tail sum_{k>N} C(k,m) h^{k-m} <= 2 (N+1)^m h^{N+1-m} for h <= 1/100."""
    h = abs(x0).upper()
    if not (h <= arb(1) / 100):
        raise T.NotPositive('L1 beyond 1/100')
    coefs = [arb(fmpq((-1) ** k, k + 1)) for k in range(N_L1 + 1)]
    tail = lambda m: (2 * arb(N_L1 + 1) ** m * arb(h) ** (N_L1 + 1 - m)).upper()
    return T.taylor_from_series(coefs, x0, K, tail)


def logG_dtail_strip(A, w0, w1, e0, e1, mode):
    eps = arb.union(q(e0), q(e1)) if e1 > e0 else q(e0)
    cx = T.Ctx(eps)
    e2 = cx.e2
    w = arb.union(q(w0), q(w1)) if w1 > w0 else q(w0)
    md = m_range(w0, w1, e0, e1)
    nd = md + eps
    W = djet_from([w, -w * w, w * w * w, -w * w * w * w], mode)
    LDN = djet_from([ZERO, w - md, (-w * w + nd * md) / 2, (2 * w * w * w - nd * md * (nd + md)) / 6], mode)
    LND = djet_from([ZERO, -md, nd * md / 2, -nd * md * (nd + md) / 6], mode)
    ND = djet_from([nd, -nd * md, nd * md * (nd + md) / 2, -nd * md * (nd * nd + 4 * nd * md + md * md) / 6], mode)
    LIN = djet_from([ZERO, ONE], mode)
    den = (-(A * eps)).exp() + ND * A * (-(A * eps)).phi1()          # nu_d / nu_b
    NB = ND / den
    omb = 1 - NB / e2 + atom_jet(mode)
    phit_d = ETA.sqrt() + atom_jet(mode)
    AW = A * W
    L1 = AW.compose(g_L1(AW.c[0], mode.maxdeg))
    v = -MU + (W / 2) * L1
    g = -v * (A * v).phi1()
    Ma = phit_d * g + (1 + AW).sqrt() * (-MU * A).exp() * atom_jet(mode, XP)
    DHa = Ma * Ma * (1 + atom_jet(mode)) + atom_jet(mode)
    Sma = T.S_of(-A, cx)
    return (-LAM * LIN + LDN + (LND - den.log()) / 2 - omb.log() / 2 - Sma.log() / 2 + cx.c.log() / 2 - e2.log()
            + DHa.log())


def norm_from_G(G, a):
    """N1, N2, N3 at the centre, and (with mode MB) their d/da at fixed d (= d_a + d_b) on the box."""
    Ga, Gb, Gab = G.coef(1, 0), G.coef(0, 1), G.coef(1, 1)
    N1 = 1 + a * Ga
    N2 = -Gb
    N3 = -Gb - a * (Gab + Ga * Gb)
    if G.m is T.MP:
        return (N1, N2, N3), None
    Gaa, Gbb, Gaab, Gabb = 2 * G.coef(2, 0), 2 * G.coef(0, 2), 2 * G.coef(2, 1), 2 * G.coef(1, 2)
    dN1 = (Ga + a * Gaa) + a * Gab
    dN2 = -Gab - Gbb
    dN3a = -2 * Gab - a * Gaab - Ga * Gb - a * Gaa * Gb - a * Ga * Gab
    dN3b = -Gbb - a * Gabb - a * Gab * Gb - a * Ga * Gbb
    return (N1, N2, N3), (dN1, dN2, dN3a + dN3b)


def check_a(a0, a1, w0, w1, e0, e1):
    ac, ra = (a0 + a1) / 2, (a1 - a0) / 2
    Gc = logG_dtail_strip(J.var(q(ac), 0, T.MP), w0, w1, e0, e1, T.MP)
    Nc, _ = norm_from_G(Gc, q(ac))
    Ab = arb.union(q(a0), q(a1))
    Gb = logG_dtail_strip(J.var(Ab, 0, T.MB), w0, w1, e0, e1, T.MB)
    _, gr = norm_from_G(Gb, Ab)
    R = arb(0, q(ra))
    contrib = [gr[k] * R for k in range(3)]
    return [Nc[k] + contrib[k] for k in range(3)], Nc, contrib


def run(D, a_lo, a_hi, n_w, n_eps, n_a, log=print):
    t0 = time.time()
    stack = []
    for i in range(n_w):
        for j in range(n_eps):
            for k in range(n_a):
                stack.append((a_lo + (a_hi - a_lo) * k / n_a, a_lo + (a_hi - a_lo) * (k + 1) / n_a,
                              Fr(i, n_w * D), Fr(i + 1, n_w * D), Fr(j, 37 * n_eps), Fr(j + 1, 37 * n_eps)))
    nbox, nfail = 0, 0
    worst = [None] * 3
    while stack:
        a0, a1, w0, w1, e0, e1 = stack.pop()
        try:
            lows, Nc, contrib = check_a(a0, a1, w0, w1, e0, e1)
            ok = all(l > 0 for l in lows)
        except (T.NotPositive, ValueError, ZeroDivisionError):
            ok, lows, Nc, contrib = False, None, None, None
        if ok:
            nbox += 1
            for k in range(3):
                v = float(lows[k].lower())
                if worst[k] is None or v < worst[k][0]:
                    worst[k] = (v, tuple(float(x) for x in (a0, a1, w0, w1, e0, e1)))
            continue
        if Nc is None:
            split = 'a'
        else:
            k = min(range(3), key=lambda i: float(lows[i].lower()))
            split = 'a' if float(contrib[k].rad()) >= float(Nc[k].rad()) else ('e' if 7 * float(e1 - e0) >= float(w1 - w0) * 100 else 'w')
        if (split == 'a' and a1 - a0 < Fr(1, 2 ** 14)) or (split != 'a' and e1 - e0 < Fr(1, 2 ** 26) and w1 - w0 < Fr(1, 2 ** 30)):
            nfail += 1
            log(f"FAIL a=[{float(a0)},{float(a1)}] w=[{float(w0)},{float(w1)}] eps=[{float(e0)},{float(e1)}] lows={lows}")
            if nfail > 10:
                break
            continue
        if split == 'a':
            m = (a0 + a1) / 2
            stack += [(a0, m, w0, w1, e0, e1), (m, a1, w0, w1, e0, e1)]
        elif split == 'e':
            m = (e0 + e1) / 2
            stack += [(a0, a1, w0, w1, e0, m), (a0, a1, w0, w1, m, e1)]
        else:
            m = (w0 + w1) / 2
            stack += [(a0, a1, w0, m, e0, e1), (a0, a1, m, w1, e0, e1)]
    return nbox, nfail, worst, time.time() - t0


if __name__ == '__main__':
    D = int(sys.argv[1])
    a_lo, a_hi = Fr(sys.argv[2]), Fr(sys.argv[3])
    n_w, n_eps, n_a = int(sys.argv[4]), int(sys.argv[5]), int(sys.argv[6])
    print(f"strip far tail: d >= {D}, a in [{a_lo}, {a_hi}], w = 1/d in [0, 1/{D}] ({n_w} slices), eps in [0, 1/37] "
          f"({n_eps} slabs); conditions N1 = a L1, N2 = L2, N3 = a L3", flush=True)
    nbox, nfail, worst, dt = run(D, a_lo, a_hi, n_w, n_eps, n_a, log=lambda s: print(s, flush=True))
    print(f"boxes accepted: {nbox}, failures: {nfail}, time {dt:.1f} s")
    names = ('a L1', 'L2', 'a L3')
    for k in range(3):
        if worst[k]:
            print(f"  certified min lower bound of {names[k]}: {worst[k][0]:.6g} on (a0, a1, w0, w1, e0, e1) = {worst[k][1]}")
    print("RESULT: REGION VERIFIED" if nfail == 0 else "RESULT: FAILED")
