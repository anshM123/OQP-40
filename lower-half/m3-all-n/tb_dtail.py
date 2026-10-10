"""Theorem B: the far tail d >= D (D = 512), for a in [a_lo, a_hi] (a-direction: jets + centred form) and for a >= A
(double tail, a-atoms as in tb_tail.py), all eps in [0, 1/37].

For d >= D write w = 1/d, m_d = nu_d - eps = 1/(d phi1(d eps)) in [0, w], and (scaled nu-form, tb_arb.logF_nu2)
  log F = -lam d + log(d nu_d) + (log nu_b - log nu_a)/2 - log(1+2eps) - (log om_a + log om_b)/2 + log(Dhat/d),
  Dhat/d = sg [phit_d - sqrt(1 + a w) phit_b e^{-mu a}]^2 psi + tau Ntil nu_d^2/(khat + sg),
with Phihat(z) = -sqrt(z) phit(z), tau = e^{-(1/6-lam) d}/(d nu_d^2) <= d e^{-(1/6-lam) d}, and
  nu_b = nu_d/(e^{-a eps} + nu_d a phi1(-a eps)),   log(d nu_d)' = w - m_d, '' = -w^2 + nu_d m_d, ''' = 2w^3 - nu_d m_d (nu_d + m_d),
  (log nu_d)' = -m_d, '' = nu_d m_d, ''' = -nu_d m_d (nu_d + m_d),   w' = -w^2, w'' = 2 w^3, w''' = -6 w^4.
Lemma T' (RESULTS.md): for z >= 400, |phit(z) - sqrt(eta)| and |phit^(k)(z)/k!| (k <= 3) are <= 2(z+1) e^{-(1/6-lam)(z-1)}.
All remaining terms (sg - 1, psi - 1, khat - 1, om_b - 1 + nu_b(...)/(1+2eps), tau Ntil nu_d^2/(khat + sg)) are
exponentially small for d >= 512 and are enclosed, with all their Taylor coefficients of order <= 3, in [-XA, XA],
XA = 1e-12 (Lemma T'' in RESULTS.md lists the individual bounds; each is <= (a + d)^2 d^2 e^{-(1/6-lam) d} <= 1e-12 for
a <= 512 <= d, resp. smaller).
Usage: python tb_dtail.py D a_lo a_hi n_w n_eps > log     (a_hi = 0 means the double tail a >= a_lo with atoms)
"""
import sys
import time
from fractions import Fraction as Fr
from flint import arb, fmpq
import tb_arb as T
from tb_arb import J, ZERO, ONE, MU, LAM, ETA

XA = arb('1e-12')


def q(x):
    return arb(fmpq(x.numerator, x.denominator))


def djet_from(vals, mode):
    """(a,b)-jet of a function of d = b - a with univariate Taylor coefficients vals (order 0..3)."""
    Dd = T.dvar(arb(0), mode)
    return Dd.compose(list(vals) + [ZERO] * (mode.maxdeg + 1 - len(vals)))


def atom_jet(mode, X=XA):
    c = [arb(0, X)] * mode.n
    return J(c, mode)


def m_range(w0, w1, e0, e1):
    """enclosure of m_d = 1/(d phi1(d eps)) for d in [1/w1, 1/w0] (w0 = 0: d -> inf, m_d -> 0) and eps in [e0, e1]."""
    def m(d, e):
        return 1 / (d * T.g_phi1(d * e, 0)[0])
    hi = m(1 / q(w1), q(e0))
    lo = arb(0) if w0 == 0 else m(1 / q(w0), q(e1))
    return arb.union(lo, hi)


def logF_dtail(A, w0, w1, e0, e1, mode):
    """A: the a-jet (mode); the d-dependent quantities from the (w, eps) cell."""
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
    LIN = djet_from([ZERO, ONE], mode)                      # d - d_0
    na = T.nu_of(A, cx)
    den = (-(A * eps)).exp() + ND * A * (-(A * eps)).phi1()
    NB = ND / den
    oma = 1 - na * (1 - (-(A * e2)).exp()) / e2 - (-(A / 3)).exp() / (cx.c * na)
    omb = 1 - NB / e2 + atom_jet(mode)
    sq = ETA.sqrt()
    delta = atom_jet(mode)
    phit_d = sq + delta
    phit_b = sq + delta
    M = phit_d - (1 + A * W).sqrt() * phit_b * (-MU * A).exp()
    DH = M * M * (1 + atom_jet(mode)) + atom_jet(mode)
    return (-LAM * LIN + LDN + (LND - den.log() - na.log()) / 2 - e2.log() - (oma.log() + omb.log()) / 2 + DH.log())


def check_a(a0, a1, w0, w1, e0, e1):
    ac, ra = (a0 + a1) / 2, (a1 - a0) / 2
    Gc = logF_dtail(J.var(q(ac), 0, T.MP), w0, w1, e0, e1, T.MP)
    Lc, _ = T.margins_from_logF(Gc)
    Gb = logF_dtail(J.var(arb.union(q(a0), q(a1)), 0, T.MB), w0, w1, e0, e1, T.MB)
    _, gr = T.margins_from_logF(Gb)
    R = arb(0, q(ra))
    contrib = [(gr[k][0] + gr[k][1]) * R for k in range(3)]       # d/da at fixed d
    return [Lc[k] + contrib[k] for k in range(3)], Lc, contrib


def run(D, a_lo, a_hi, n_w, n_eps, log=print):
    t0 = time.time()
    stack = []
    for i in range(n_w):
        for j in range(n_eps):
            for k in range(8):
                stack.append((a_lo + (a_hi - a_lo) * k / 8, a_lo + (a_hi - a_lo) * (k + 1) / 8,
                              Fr(i, n_w * D), Fr(i + 1, n_w * D), Fr(j, 37 * n_eps), Fr(j + 1, 37 * n_eps)))
    nbox, nfail = 0, 0
    worst = [None] * 3
    while stack:
        a0, a1, w0, w1, e0, e1 = stack.pop()
        try:
            lows, Lc, contrib = check_a(a0, a1, w0, w1, e0, e1)
            ok = all(l > 0 for l in lows)
        except (T.NotPositive, ValueError, ZeroDivisionError):
            ok, lows, Lc, contrib = False, None, None, None
        if ok:
            nbox += 1
            if nbox % 2000 == 0:
                log(f"  progress: {nbox} boxes, stack {len(stack)}, {time.time() - t0:.0f} s")
            for k in range(3):
                v = float(lows[k].lower())
                if worst[k] is None or v < worst[k][0]:
                    worst[k] = (v, tuple(float(x) for x in (a0, a1, w0, w1, e0, e1)))
            continue
        if Lc is None:
            split = 'a'
        else:
            k = min(range(3), key=lambda i: float(lows[i].lower()))
            split = 'a' if float(contrib[k].rad()) >= float(Lc[k].rad()) else ('e' if 7 * float(e1 - e0) >= float(w1 - w0) * 100 else 'w')
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
    n_w, n_eps = int(sys.argv[4]), int(sys.argv[5])
    print(f"far tail: d >= {D}, a in [{a_lo}, {a_hi}], w = 1/d in [0, 1/{D}] ({n_w} slices), eps in [0, 1/37] ({n_eps} slabs)", flush=True)
    nbox, nfail, worst, dt = run(D, a_lo, a_hi, n_w, n_eps, log=lambda s: print(s, flush=True))
    print(f"boxes accepted: {nbox}, failures: {nfail}, time {dt:.1f} s")
    for k in range(3):
        if worst[k]:
            print(f"  certified min lower bound of L{k + 1}: {worst[k][0]:.6g} on (a0, a1, w0, w1, e0, e1) = {worst[k][1]}")
    print("RESULT: REGION VERIFIED" if nfail == 0 else "RESULT: FAILED")
