"""Theorem B: the stationary tail a >= A, version with eps as a jet variable (centred form in eps at fixed m_a).

Base variables (m_a, eps, d), m_a = nu_a - eps = 1/(a phi1(a eps)) in [0, 1/A].  Same formulas as tb_tail.py, but every
quantity is a jet in (a, b, eps), where the eps-direction is d/d eps at fixed (m_a, d) (the a- and b-directions are
the partial derivatives at fixed eps that define L1, L2, L3).  Exact quantities are built from nu_a = m_a + eps
(jet), rho = e^{-a eps} = m_a/nu_a, nu_b = nu_a/(e^{-d eps} + nu_a d phi1(-d eps)), m_b = nu_b rho e^{-d eps}, with
  nu_a(a + h) = nu_a - nu_a m_a h + nu_a m_a (nu_a + m_a) h^2/2 + ...,  log nu_a: -m_a h + nu_a m_a h^2/2,  same for b.
Atoms (exponentially small in a >= A): every Taylor coefficient of order <= 3 is enclosed in [-X, X]; for the
eps-coefficients we use |d a/d eps| (fixed m_a) = a^2 phi2 <= a^2/2 (phi2(x) = (x - 1 + e^{-x})/x^2 <= 1/2), so they
are bounded by the a- and b-bounds times (a + d)^2 + a + d + 1, maximised at a = A (the bounds decrease in a).
Usage: python tb_tail2.py A d_lo d_hi n_m n_eps > log
"""
import sys
import time
from fractions import Fraction as Fr
from flint import arb, fmpq
import tb_arb as T
import tb_tail as TT
from tb_arb import J, ZERO, ONE, MU, LAM


def q(x):
    return arb(fmpq(x.numerator, x.denominator))


def unit(mode, mono):
    c = [ZERO] * mode.n
    c[mode.idx[mono]] = ONE
    return J(c, mode)


def atomj(mode, X, Xe):
    c = []
    for (i, j, k) in mode.monos:
        if (i, j, k) == (0, 0, 0):
            c.append(arb(X / 2, X / 2))
        elif k == 0:
            c.append(arb(0, X))
        else:
            c.append(arb(0, Xe))
    return J(c, mode)


def pieces2(mA, Dd, cx, A, d_hi):
    mode = Dd.m
    E = cx.eps                       # arb (thin, centre) or J (box)
    ah, bh = unit(mode, (1, 0, 0)), unit(mode, (0, 1, 0))
    if isinstance(d_hi, Fr):
        d_hi = q(d_hi)
    Nu = mA + E
    if not isinstance(Nu, J):
        Nu = J.const(Nu, mode)
    NuA = Nu - Nu * mA * ah + Nu * mA * (Nu + mA) / 2 * ah * ah
    LNA = -mA * ah + Nu * mA / 2 * ah * ah
    d0 = Dd.c[0]
    dE = E * d0
    emde = (-dE).exp() if isinstance(dE, J) else J.const((-dE).exp(), mode)
    ph = (-dE).phi1() if isinstance(dE, J) else J.const(T.g_phi1(-dE, 0)[0], mode)
    ratio = 1 / (emde + Nu * d0 * ph)                    # nu_b/nu_a
    nub = Nu * ratio
    mb = mA * ratio * emde                                # m_b = nu_b e^{-b eps} = nu_b (m_a/nu_a) e^{-d eps}
    NuB = nub - nub * mb * bh + nub * mb * (nub + mb) / 2 * bh * bh
    LNB = -mb * bh + nub * mb / 2 * bh * bh
    eb = None
    # A here is a lower bound for a on the whole box (a_min = log(1 + eps1/m1)/eps1, see check3), so that every
    # atom bound below holds at every point of the box (also at points with a < 64, which the core chart covers too).
    A = arb(A)
    # eps-coefficients of the atoms: |d a/d eps| <= a^2/2, |d log nu_b/d eps| <= b + a^2/2 m_b, |d log nu_a/d eps| <= a,
    # so every atom Z here satisfies |d Z/d eps| <= Z (a^2 + a + d + 2), and Z (a^2 + a + d + 2) is decreasing in a
    # for a >= 30, d <= 512 (for the atom bounds below); hence the factor at a = A, d = d_hi.
    fac = (A * A + A + d_hi + 2)
    X1 = ((A + d_hi) * (-A / 3).exp()).upper()
    X2 = (2 * (-A).exp() * (1 + 3 * (A + d_hi))).upper()
    X3 = (A * (-A / 3).exp() * 2).upper()
    XP = (arb('2.4') * (A + d_hi + 1).sqrt() * (-MU * A).exp()).upper()    # Lemma T (|phit| <= 1.2 for Re z >= 30)
    XA = (-A).exp().upper()
    Q1 = atomj(mode, X1, (X1 * fac * 2).upper())
    Q2 = atomj(mode, X2, (X2 * fac * 2).upper())
    W3 = atomj(mode, X3, (X3 * fac * 2).upper())
    PH = atomj(mode, XP, (XP * fac * 2).upper())
    PH = PH - J.const(arb(XP / 2), mode)                  # value in [-XP/2... symmetric enough: [-XP/2, XP/2]
    EA2 = atomj(mode, XA, (XA * fac * 2).upper())
    return NuA, LNA, NuB, LNB, Q1, Q2, W3, PH, EA2, eb


def logF_t2_nu2(mA, Dd, cx, A, d_hi):
    eps, e1, e2 = cx.eps, cx.e1, cx.e2
    na, lna, nb, lnb, Q1, Q2, W3, phib, ea2, eb = pieces2(mA, Dd, cx, A, d_hi)
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
    oma = 1 - na * (1 - ea2) / e2 - W3
    omb = 1 - nb * (1 - ea2 * (-(Dd * e2)).exp()) / e2 - Q1 * cx.sqcp * emd3 / cx.c
    return (-LAM * Dd + nd.log() + (lnb - lna) / 2 - e2.log() - (oma.log() + omb.log()) / 2 + Dh.log())


def logF_t2_mixed3(mA, Dd, cx, A, d_hi):
    eps, e1, e2 = cx.eps, cx.e1, cx.e2
    na, lna, nb, lnb, Q1, Q2, W3, phib, ea2, eb = pieces2(mA, Dd, cx, A, d_hi)
    emd, emd3 = (-Dd).exp(), (-(Dd / 3)).exp()
    gb = 1 - Q2 * emd - Q1 * Q1 * emd3 * emd3
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


def a_min_of(m1, e1, A):
    """lower bound for a = log(1 + eps/m)/eps over m <= m1, eps <= e1 (a is decreasing in m and in eps)."""
    if m1 == 0:
        return arb(10 ** 6)
    if e1 == 0:
        return (1 / q(m1)).lower()
    x = q(e1) / q(m1)
    return ((1 + x).log() / q(e1)).lower()


def check3(form, m0, m1, e0, e1, d0, d1, A, d_hi):
    A = a_min_of(m1, e1, A)
    if not (A >= 30):
        raise T.NotPositive('a_min below 30')
    mA = arb.union(q(m0), q(m1)) if m1 > m0 else q(m0)
    dc, ec = (d0 + d1) / 2, (e0 + e1) / 2
    rd, re = (d1 - d0) / 2, (e1 - e0) / 2
    cx = T.Ctx(q(ec))
    Lc, _ = T.margins_from_logF(form(mA, TT.dj(q(dc), T.MP), cx, A, d_hi))
    db = arb.union(q(d0), q(d1))
    eb = arb.union(q(e0), q(e1))
    E = J.var(eb, 2, T.MBE)
    cxb = T.Ctx(E)
    _, gr = T.margins_from_logF(form(mA, T.dvar(db, T.MBE), cxb, A, d_hi))
    Rd, Re = arb(0, q(rd)), arb(0, q(re))
    cd = [gr[k][1] * Rd for k in range(3)]
    ce = [gr[k][2] * Re for k in range(3)]
    return [Lc[k] + cd[k] + ce[k] for k in range(3)], Lc, cd, ce


def run(A, d_lo, d_hi, n_m, n_eps, log=print, d_switch=Fr(3)):
    t0 = time.time()
    stack = []
    for i in range(n_m):
        for j in range(n_eps):
            for k in range(16):
                stack.append((Fr(i, n_m * A), Fr(i + 1, n_m * A), Fr(j, 37 * n_eps), Fr(j + 1, 37 * n_eps),
                              d_lo + (d_hi - d_lo) * k / 16, d_lo + (d_hi - d_lo) * (k + 1) / 16))
    nbox, nfail = 0, 0
    worst = [None] * 3
    while stack:
        m0, m1, e0, e1, d0, d1 = stack.pop()
        if d0 < d_switch < d1:
            stack += [(m0, m1, e0, e1, d0, d_switch), (m0, m1, e0, e1, d_switch, d1)]
            continue
        form = logF_t2_mixed3 if d1 <= d_switch else logF_t2_nu2
        try:
            lows, Lc, cd, ce = check3(form, m0, m1, e0, e1, d0, d1, A, d_hi)
            ok = all(l > 0 for l in lows)
        except (T.NotPositive, ValueError, ZeroDivisionError):
            ok, lows, Lc, cd, ce = False, None, None, None, None
        if ok:
            nbox += 1
            if nbox % 5000 == 0:
                log(f"  progress: {nbox} boxes, stack {len(stack)}, {time.time() - t0:.0f} s")
            for k in range(3):
                v = float(lows[k].lower())
                if worst[k] is None or v < worst[k][0]:
                    worst[k] = (v, tuple(float(x) for x in (m0, m1, e0, e1, d0, d1)))
            continue
        if Lc is None:
            split = 'd' if (d1 - d0) > Fr(1, 64) else 'e'
        else:
            k = min(range(3), key=lambda i: float(lows[i].lower()))
            parts = {'d': float(cd[k].rad()), 'e': float(ce[k].rad()), 'm': float(Lc[k].rad())}
            split = max(parts, key=parts.get)
        if (split == 'd' and d1 - d0 < Fr(1, 2 ** 16)) or (split == 'e' and e1 - e0 < Fr(1, 2 ** 24)) or \
                (split == 'm' and m1 - m0 < Fr(1, 2 ** 24)):
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
    print(f"stationary tail (eps-jets): a >= {A}, d in [{d_lo}, {d_hi}], m_a in [0, 1/{A}] ({n_m} slices), eps in [0, 1/37] ({n_eps} slabs)", flush=True)
    nbox, nfail, worst, dt = run(A, d_lo, d_hi, n_m, n_eps, log=lambda s: print(s, flush=True))
    print(f"boxes accepted: {nbox}, failures: {nfail}, time {dt:.1f} s")
    for k in range(3):
        if worst[k]:
            print(f"  certified min lower bound of L{k + 1}: {worst[k][0]:.6g} on (m0, m1, e0, e1, d0, d1) = {worst[k][1]}")
    print("RESULT: REGION VERIFIED" if nfail == 0 else "RESULT: FAILED")
