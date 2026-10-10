"""Theorem B: the stationary tail a >= A (all eps = 1/n in [0, 1/37], d in [d_lo, d_hi]).

For a >= A every a-dependent quantity of the nu-forms is a function of m_a = nu_a - eps = 1/(a phi1(a eps)) in [0, 1/A]
and of exponentially small atoms:
  nu_a = m_a + eps,  e^{-a eps} = m_a/nu_a,  nu_b = nu_a/(e^{-d eps} + nu_a d phi1(-d eps)),  m_b = nu_b (m_a/nu_a) e^{-d eps},
  e^{-b eps} = (m_a/nu_a) e^{-d eps};  d/da nu_a = -nu_a m_a, d^2/da^2 nu_a = nu_a m_a (nu_a + m_a) (same for b);
  atoms: e^{-a} in [0, e^{-A}], e^{-a/3} in [0, e^{-A/3}], e^{-a(1+2eps)} in [0, e^{-A}], with their exact a-jets;
  Phi(b) and its b-derivatives up to order 2 bounded by e^{-0.27 b} <= e^{-0.27 A} (Lemma T in RESULTS.md, A >= 400).
The jets in (a, b) are assembled from these values; m_a and eps are ball parameters (sliced), and the centred form is
used in d only:  L_k(box) in L_k(d_c) + d_b L_k(box) [-r_d, r_d]  (d/dd at fixed a is d_b).
Usage: python tb_tail.py A d_lo d_hi n_m n_eps > log
"""
import sys
import time
from fractions import Fraction as Fr
from flint import arb, fmpq
import tb_arb as T
from tb_arb import J, ZERO, ONE, MU, LAM


def ajet(vals, mode):
    """jet with only a-direction coefficients vals = [c0, c1, c2]."""
    c = [ZERO] * mode.n
    c[0] = vals[0]
    c[mode.idx[(1, 0, 0)]] = vals[1]
    if (2, 0, 0) in mode.idx:
        c[mode.idx[(2, 0, 0)]] = vals[2]
    return J(c, mode)


def bjet(vals, mode):
    c = [ZERO] * mode.n
    c[0] = vals[0]
    c[mode.idx[(0, 1, 0)]] = vals[1]
    if (0, 2, 0) in mode.idx:
        c[mode.idx[(0, 2, 0)]] = vals[2]
    return J(c, mode)


def atom(X):
    """the ball [0, X]."""
    return arb(X / 2, X / 2)


def pieces(mA, Dd, cx, A, d_hi):
    """jets of the a- and b-dependent quantities for a >= A (see the module docstring).  Atoms (all Taylor
    coefficients of order <= 2 bounded as stated; derivative factors are <= 1 because m_b, nu_b <= 1):
      Q1 = e^{-a/3}/(nu_b sqrt(c')) in [0, (A + d_hi) e^{-A/3}],        (nu_b >= 1/b, b <= a + d_hi, decreasing in a)
      Q2 = e^{-a} (e^{-2 eps b} + (1+2eps) e^{-eps b}/nu_b) in [0, 2 e^{-A} (1 + 3(A + d_hi))],
      e^{-a} in [0, e^{-A}],  e^{-a(1+2eps)} in [0, e^{-A}],  Phi(b): Lemma T."""
    mode = Dd.m
    eps, e2 = cx.eps, cx.e2
    if isinstance(d_hi, Fr):
        d_hi = arb(fmpq(d_hi.numerator, d_hi.denominator))
    nu = mA + eps
    NuA = ajet([nu, -nu * mA, nu * mA * (nu + mA) / 2], mode)
    LNA = ajet([ZERO, -mA, nu * mA / 2], mode)                      # log nu_a without its constant term
    d0 = Dd.c[0]
    emde = (-(d0 * eps)).exp()
    rho = mA / nu if mA.lower() > 0 or eps.lower() > 0 else arb(0, 1)  # e^{-a eps} in [0, 1]
    if not (rho.upper() <= 1):
        rho = arb(0, 1)
    nub = nu / (emde + nu * d0 * T.g_phi1(-(d0 * eps), 0)[0])
    mb = nub * rho * emde
    NuB = bjet([nub, -nub * mb, nub * mb * (nub + mb) / 2], mode)
    LNB = bjet([ZERO, -mb, nub * mb / 2], mode)                     # log nu_b without its constant term
    X1 = ((A + d_hi) * arb(-A / 3).exp()).upper()
    X2 = (2 * arb(-A).exp() * (1 + 3 * (A + d_hi))).upper()
    q1 = arb(0, X1)
    Q1 = J([arb(X1 / 2, X1 / 2)] + [q1] * (mode.n - 1), mode)
    q2 = arb(0, X2)
    Q2 = J([arb(X2 / 2, X2 / 2)] + [q2] * (mode.n - 1), mode)
    XA = arb(-A).exp()
    v1 = atom(XA)
    EMA = ajet([v1, -v1, v1 / 2], mode)
    v2 = atom(XA)
    EA2 = ajet([v2, -e2 * v2, e2 * e2 * v2 / 2], mode)
    # Lemma T: PH = Phihat(b) e^{-mu a}; for b >= 64, |Phihat^(k)(b)/k!| <= sqrt(b+1) (Cauchy on |z - b| <= 1), so every
    # Taylor coefficient (order <= 3) of PH is <= 2 sqrt(a + d_hi + 1) e^{-mu a} <= 2 sqrt(A + d_hi + 1) e^{-mu A}.
    XP = (2 * arb(A + d_hi + 1).sqrt() * (-MU * A).exp()).upper()
    pb = arb(0, XP)
    PHIB = J([arb(-XP / 2, XP / 2)] + [pb] * (mode.n - 1), mode)
    return NuA, LNA, NuB, LNB, Q1, Q2, EMA, EA2, PHIB


def logF_tail_nu2(mA, Dd, cx, A, d_hi):
    eps, e1, e2 = cx.eps, cx.e1, cx.e2
    na, lna, nb, lnb, Q1, Q2, ema, ea2, phib = pieces(mA, Dd, cx, A, d_hi)
    nd = T.nu_of(Dd, cx)
    emd, emd3 = (-Dd).exp(), (-(Dd / 3)).exp()
    yhd = 1 / (nd * cx.sqcp)
    phd = (-(2 * eps) * Dd).exp() + e2 * (-eps * Dd).exp() / nd
    uh1 = (-(2 * eps) * Dd).exp()
    uh2 = (1 - ea2) * (na / nd) * (-eps * Dd).exp()
    uh = uh1 + uh2
    emd43 = emd * emd3
    Nt = ((Q1 - yhd) * (Q1 - yhd) + emd3 * (Q2 + phd - 2 * uh) + emd43 * uh * uh + 2 * emd * uh * Q1 * yhd
          - Q2 * phd * emd43 - Q2 * yhd * yhd * emd - phd * Q1 * Q1 * emd)
    gb = 1 - Q2 * emd - Q1 * Q1 * emd3 * emd3
    gd = 1 - phd * emd - yhd * yhd * emd3 * emd3
    kh = 1 - emd * uh - Q1 * yhd * emd3 * emd3
    sg = gb.sqrt() * gd.sqrt()
    dif = phib - T.Phihat_of(Dd)
    dif2 = dif * dif
    xx = dif2 * (-((2 * MU) * Dd)).exp()
    psi = (-xx).phi1()
    Dh = (-((arb(1) / 6 - LAM) * Dd)).exp() * Nt / (kh + sg) + sg * dif2 * psi
    # om_a = 1 - nu_a (1 - e^{-a(1+2eps)})/(1+2eps) - e^{-a/3}/(c nu_a); e^{-a/3}/nu_a <= a e^{-a/3}... as an atom:
    X3 = (arb(A) * arb(-A / 3).exp() * 2).upper()
    q3 = arb(0, X3)
    W3 = J([arb(X3 / 2, X3 / 2)] + [q3] * (Dd.m.n - 1), Dd.m)          # e^{-a/3}/(c nu_a) (Lemma: <= a e^{-a/3} <= 2 A e^{-A/3}, coefficients likewise)
    oma = 1 - na * (1 - ea2) / e2 - W3
    omb = 1 - nb * (1 - ea2 * (-(Dd * e2)).exp()) / e2 - Q1 * cx.sqcp * emd3 / cx.c
    return (-LAM * Dd + nd.log() + (lnb - lna) / 2 - e2.log() - (oma.log() + omb.log()) / 2 + Dh.log())


def logF_tail_mixed3(mA, Dd, cx, A, d_hi):
    eps, e1, e2 = cx.eps, cx.e1, cx.e2
    na, lna, nb, lnb, Q1, Q2, ema, ea2, phib = pieces(mA, Dd, cx, A, d_hi)
    emd, emd3 = (-Dd).exp(), (-(Dd / 3)).exp()
    gb = 1 - Q2 * emd - Q1 * Q1 * emd3 * emd3
    X3 = (arb(A) * arb(-A / 3).exp() * 2).upper()
    q3 = arb(0, X3)
    W3 = J([arb(X3 / 2, X3 / 2)] + [q3] * (Dd.m.n - 1), Dd.m)
    oma = 1 - na * (1 - ea2) / e2 - W3
    omb = 1 - nb * (1 - ea2 * (-(Dd * e2)).exp()) / e2 - Q1 * cx.sqcp * emd3 / cx.c
    Pd = (Dd * e2).phi1() / (Dd * eps).phi1()
    x = (phib - T.Phihat_of(Dd)) * (-MU * Dd).exp()
    R = (-(x * x)).exp()
    Sd = T.S_of(Dd, cx)
    Bm = ((-(Dd * (arb(1) / 2 + eps))).exp() * (Pd - na * (1 - ea2) / e2)
          - Q1 * cx.sqcp * (-(Dd / 6)).exp() / cx.c
          - (cx.cp * gb).sqrt() / cx.c * Dd * Sd.sqrt() * R)
    return (lnb - lna) / 2 + Bm.log() - (oma.log() + omb.log()) / 2


def dj(d, mode):
    c = [ZERO] * mode.n
    c[0] = d
    c[mode.idx[(1, 0, 0)]] = -ONE
    c[mode.idx[(0, 1, 0)]] = ONE
    return J(c, mode)


def check(form, mA, eps, d0, d1, A, d_hi):
    cx = T.Ctx(eps)
    dc = (d0 + d1) / 2
    rd = (d1 - d0) / 2
    Lc, _ = T.margins_from_logF(form(mA, dj(arb(fmpq(dc.numerator, dc.denominator)), T.MP), cx, A, d_hi))
    db = arb.union(arb(fmpq(d0.numerator, d0.denominator)), arb(fmpq(d1.numerator, d1.denominator)))
    _, gr = T.margins_from_logF(form(mA, dj(db, T.MB), cx, A, d_hi))
    R = arb(0, arb(fmpq(rd.numerator, rd.denominator)))
    return [Lc[k] + gr[k][1] * R for k in range(3)]


def run(A, d_lo, d_hi, n_m, n_eps, log=print, d_switch=Fr(3)):
    t0 = time.time()
    nbox, nfail = 0, 0
    worst = [None] * 3
    for i in range(n_m):
        m0, m1 = Fr(i, n_m * A), Fr(i + 1, n_m * A)
        mA = arb.union(arb(fmpq(m0.numerator, m0.denominator)), arb(fmpq(m1.numerator, m1.denominator)))
        for j in range(n_eps):
            e0, e1 = Fr(j, 37 * n_eps), Fr(j + 1, 37 * n_eps)
            eps = arb.union(arb(fmpq(e0.numerator, e0.denominator)), arb(fmpq(e1.numerator, e1.denominator)))
            stack = []
            nd0 = 16
            for k in range(nd0):
                stack.append((d_lo + (d_hi - d_lo) * k / nd0, d_lo + (d_hi - d_lo) * (k + 1) / nd0))
            while stack:
                d0, d1 = stack.pop()
                if d0 < d_switch < d1:
                    stack += [(d0, d_switch), (d_switch, d1)]
                    continue
                form = logF_tail_mixed3 if d1 <= d_switch else logF_tail_nu2
                try:
                    lows = check(form, mA, eps, d0, d1, A, d_hi)
                    ok = all(l > 0 for l in lows)
                except (T.NotPositive, ValueError, ZeroDivisionError):
                    ok, lows = False, None
                if ok:
                    nbox += 1
                    for k in range(3):
                        v = float(lows[k].lower())
                        if worst[k] is None or v < worst[k][0]:
                            worst[k] = (v, (float(m0), float(m1), float(e0), float(e1), float(d0), float(d1)))
                    continue
                if d1 - d0 < Fr(1, 2 ** 14):
                    nfail += 1
                    log(f"FAIL m=[{float(m0)},{float(m1)}] eps=[{float(e0)},{float(e1)}] d=[{float(d0)},{float(d1)}] lows={lows}")
                    if nfail > 10:
                        return nbox, nfail, worst, time.time() - t0
                    continue
                m = (d0 + d1) / 2
                stack += [(d0, m), (m, d1)]
        log(f"  m-slice {i + 1}/{n_m} done: boxes {nbox}, failures {nfail}, {time.time() - t0:.0f} s")
    return nbox, nfail, worst, time.time() - t0


def check2(form, mA, eps, d0, d1, A, d_hi):
    """as check(), also returning the centre enclosures and the d-contributions."""
    cx = T.Ctx(eps)
    dc = (d0 + d1) / 2
    rd = (d1 - d0) / 2
    Lc, _ = T.margins_from_logF(form(mA, dj(arb(fmpq(dc.numerator, dc.denominator)), T.MP), cx, A, d_hi))
    db = arb.union(arb(fmpq(d0.numerator, d0.denominator)), arb(fmpq(d1.numerator, d1.denominator)))
    _, gr = T.margins_from_logF(form(mA, dj(db, T.MB), cx, A, d_hi))
    R = arb(0, arb(fmpq(rd.numerator, rd.denominator)))
    contrib = [gr[k][1] * R for k in range(3)]
    return [Lc[k] + contrib[k] for k in range(3)], Lc, contrib


def run_adaptive(A, d_lo, d_hi, n_m, n_eps, log=print, d_switch=Fr(3), w_eps=7.0, w_m=1.0):
    """adaptive branch and bound over (m_a, eps, d): m_a and eps plain balls (split when the centre enclosure is too
    wide), d by the centred form (split when the d-contribution dominates)."""
    t0 = time.time()
    stack = []
    for i in range(n_m):
        for j in range(n_eps):
            for k in range(16):
                stack.append((Fr(i, n_m * A), Fr(i + 1, n_m * A), Fr(j, 37 * n_eps), Fr(j + 1, 37 * n_eps),
                              d_lo + (d_hi - d_lo) * k / 16, d_lo + (d_hi - d_lo) * (k + 1) / 16))
    nbox, nfail = 0, 0
    worst = [None] * 3
    q = lambda x: arb(fmpq(x.numerator, x.denominator))
    while stack:
        m0, m1, e0, e1, d0, d1 = stack.pop()
        if d0 < d_switch < d1:
            stack += [(m0, m1, e0, e1, d0, d_switch), (m0, m1, e0, e1, d_switch, d1)]
            continue
        form = logF_tail_mixed3 if d1 <= d_switch else logF_tail_nu2
        mA = arb.union(q(m0), q(m1)) if m1 > m0 else q(m0)
        eps = arb.union(q(e0), q(e1)) if e1 > e0 else q(e0)
        try:
            lows, Lc, contrib = check2(form, mA, eps, d0, d1, A, d_hi)
            ok = all(l > 0 for l in lows)
        except (T.NotPositive, ValueError, ZeroDivisionError):
            ok, lows, Lc, contrib = False, None, None, None
        if ok:
            nbox += 1
            if nbox % 5000 == 0:
                log(f"  progress: {nbox} boxes, stack {len(stack)}, {time.time() - t0:.0f} s, at m=[{float(m0):.3g},{float(m1):.3g}] eps=[{float(e0):.4g},{float(e1):.4g}] d=[{float(d0):.4g},{float(d1):.4g}]")
            for k in range(3):
                v = float(lows[k].lower())
                if worst[k] is None or v < worst[k][0]:
                    worst[k] = (v, tuple(float(x) for x in (m0, m1, e0, e1, d0, d1)))
            continue
        wd, we, wm = d1 - d0, e1 - e0, m1 - m0
        if Lc is None:
            split = 'd' if wd > Fr(1, 64) else ('e' if w_eps * float(we) >= w_m * float(wm) else 'm')
        else:
            k = min(range(3), key=lambda i: float(lows[i].lower()))
            dpart = float(contrib[k].rad())
            cpart = float(Lc[k].rad())
            if dpart >= cpart:
                split = 'd'
            else:
                split = 'e' if w_eps * float(we) >= w_m * float(wm) else 'm'
        if (split == 'd' and wd < Fr(1, 2 ** 16)) or (split != 'd' and we < Fr(1, 2 ** 24) and wm < Fr(1, 2 ** 24)):
            nfail += 1
            log(f"FAIL m=[{float(m0)},{float(m1)}] eps=[{float(e0)},{float(e1)}] d=[{float(d0)},{float(d1)}] lows={lows}")
            if nfail > 10:
                break
            continue
        if split == 'd':
            mid = (d0 + d1) / 2
            stack += [(m0, m1, e0, e1, d0, mid), (m0, m1, e0, e1, mid, d1)]
        elif split == 'e':
            mid = (e0 + e1) / 2
            stack += [(m0, m1, e0, mid, d0, d1), (m0, m1, mid, e1, d0, d1)]
        else:
            mid = (m0 + m1) / 2
            stack += [(m0, mid, e0, e1, d0, d1), (mid, m1, e0, e1, d0, d1)]
    return nbox, nfail, worst, time.time() - t0


if __name__ == '__main__':
    A = int(sys.argv[1])
    d_lo, d_hi = Fr(sys.argv[2]), Fr(sys.argv[3])
    n_m, n_eps = int(sys.argv[4]), int(sys.argv[5])
    print(f"stationary tail: a >= {A}, d in [{d_lo}, {d_hi}], m_a in [0, 1/{A}] ({n_m} slices), eps in [0, 1/37] ({n_eps} slabs)", flush=True)
    nbox, nfail, worst, dt = run_adaptive(A, d_lo, d_hi, n_m, n_eps, log=lambda s: print(s, flush=True))
    print(f"boxes accepted: {nbox}, failures: {nfail}, time {dt:.1f} s")
    for k in range(3):
        if worst[k]:
            print(f"  certified min lower bound of L{k + 1}: {worst[k][0]:.6g} on (m0, m1, e0, e1, d0, d1) = {worst[k][1]}")
    print("RESULT: REGION VERIFIED" if nfail == 0 else "RESULT: FAILED")


