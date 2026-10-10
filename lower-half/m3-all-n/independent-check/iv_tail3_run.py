"""a-tail chart with a mean-value form in (d, eps) at fixed m_a (m_a a ball): a >= 250, d in [D0, D1].
Uses iv_far.logF_atail2 with the third jet variable = eps (the eps-derivative is taken at fixed m_a; the identity
nu(a + h) = (m + eps)/(1 + m h phi(-h eps)) makes the non-atom parts exact jets in (h_a, h_d, eps)).
Atom coefficients (Z any atom, coefficient of h_a^i h_d^j h_eps^k, k <= 1, i + j + k <= 3):
  k = 0: |.| <= X(a) (Cauchy, radius 1 in a and d; iv_atoms.a_tail_atom_bound);
  k = 1: d/deps [coef_ij Z(a(m, eps), d; eps)] = (i+1) coef_{i+1,j} * da/deps|_m + d/deps coef_ij |_{a,d}, where
    |da/deps|_m| = a^2 psi(-a eps) <= a^2/2 (a = log(1 + eps/m)/eps, psi(y) = (e^y - 1 - y)/y^2), i <= 2, and the
    second term is bounded by Cauchy on the polydisc x the complex disc |eps' - eps| <= 1/(4 (a + d1 + 2)):
    <= 4 (a + d1 + 2) Xc(a) (iv_atoms.a_tail_atom_bound_ceps).  So |.| <= 1.5 a^2 X(a) + 4 (a + d1 + 2) Xc(a);
  both bounds are decreasing in a for a >= 100 and are evaluated at a lower bound of a_min of the box; factor 10.
L_k(box) >= L_k(m-ball, d_c, eps_c) - |d_d L_k| r_d - |d_eps L_k| r_e  (mean value in (d, eps) for every m of the cell).
Usage: python iv_tail3_run.py D0 D1 ND NM NE K0 K1
"""
import sys
import time
from fractions import Fraction as Fr
from flint import arb
import iv_far as T
import iv_forms as FF
import iv_atoms as AT
import iv_tail_run as R
from iv_jet import Jet, SP3, NotPos

q = T.q


def check(m0, m1, d0, d1, e0, e1, form):
    amin = R.amin_of(m1, e1)
    if not (amin >= 100):
        raise NotPos('amin')
    Xr = AT.a_tail_atom_bound(amin, q(d1))[0]
    Xc = AT.a_tail_atom_bound_ceps(amin, q(d1))[0]
    am = arb(amin)
    X = 10 * Xr
    Xe = float((10 * (arb('1.5') * am ** 2 * arb(Xr) + 4 * (am + q(d1) + 2) * arb(Xc))).upper()) * (1 + 2.0 ** -50)
    ma = arb.union(q(m0), q(m1)) if m1 > m0 else q(m0)
    Mj = Jet.const(ma, SP3)
    ec, dc = (e0 + e1) / 2, (d0 + d1) / 2
    Gc = T.logF_atail2(Mj, Jet.var(q(ec), 2, SP3), Jet.var(q(dc), 1, SP3), X, Xe, form)
    Lc = FF.conditions(Gc)
    Gb = T.logF_atail2(Mj, Jet.var(arb.union(q(e0), q(e1)), 2, SP3), Jet.var(arb.union(q(d0), q(d1)), 1, SP3), X, Xe, form)
    gr = FF.gradients(Gb)
    rd, re = q((d1 - d0) / 2), q((e1 - e0) / 2)
    lows = [Lc[k] - abs(gr[k][1]) * rd - abs(gr[k][2]) * re for k in range(3)]
    cd = max(float((abs(gr[k][1]) * rd).upper()) for k in range(3))
    ce = max(float((abs(gr[k][2]) * re).upper()) for k in range(3))
    cm = max(float(Lc[k].rad()) for k in range(3))
    return lows, (cd, ce, cm)


def run(D0, D1, ND, NM, NE, K0, K1, log):
    t0 = time.time()
    stack = []
    for k in range(K0, K1):
        e0, e1 = Fr(k, 37 * NE), Fr(k + 1, 37 * NE)
        mtop = R.m250(e0)
        for i in range(NM):
            for j in range(ND):
                stack.append((mtop * i / NM, mtop * (i + 1) / NM, D0 + (D1 - D0) * j / ND, D0 + (D1 - D0) * (j + 1) / ND,
                              e0, e1))
    nbox = nfail = 0
    worst = [None] * 3
    last = t0
    while stack:
        m0, m1, d0, d1, e0, e1 = stack.pop()
        if d0 < Fr(15, 4) < d1:
            stack += [(m0, m1, d0, Fr(15, 4), e0, e1), (m0, m1, Fr(15, 4), d1, e0, e1)]
            continue
        form = 'mix' if d1 <= Fr(15, 4) else 'nu'
        try:
            lows, (cd, ce, cm) = check(m0, m1, d0, d1, e0, e1, form)
            ok = all(l > 0 for l in lows)
        except (NotPos, ZeroDivisionError, ValueError):
            ok, lows, cd, ce, cm = False, None, None, None, None
        if ok:
            nbox += 1
            for kk in range(3):
                v = float(lows[kk].lower())
                if worst[kk] is None or v < worst[kk][0]:
                    worst[kk] = (v, tuple(float(x) for x in (m0, m1, d0, d1, e0, e1)))
            if time.time() - last > 120:
                last = time.time()
                log(f"  progress: {nbox} boxes, stack {len(stack)}, {time.time() - t0:.0f} s, box m=[{float(m0):.3g},{float(m1):.3g}] "
                    f"d=[{float(d0):.4g},{float(d1):.4g}] e=[{float(e0):.4g},{float(e1):.4g}]")
            continue
        if cd is None:
            dim = 'd' if d1 - d0 > Fr(1, 64) else 'e'
        else:
            dim = max((('d', cd), ('e', ce), ('m', cm)), key=lambda t: t[1])[0]
        if dim == 'd' and d1 - d0 >= Fr(1, 2 ** 14):
            m = (d0 + d1) / 2
            stack += [(m0, m1, d0, m, e0, e1), (m0, m1, m, d1, e0, e1)]
        elif dim == 'm' and m1 - m0 >= Fr(1, 2 ** 40):
            m = (m0 + m1) / 2
            stack += [(m0, m, d0, d1, e0, e1), (m, m1, d0, d1, e0, e1)]
        elif e1 - e0 >= Fr(1, 2 ** 24):
            m = (e0 + e1) / 2
            stack.append((m0, m1, d0, d1, e0, m))
            mtop = min(m1, R.m250(m))                     # upper half: only m <= m(250, m) can have a >= 250
            if mtop > m0:
                stack.append((m0, mtop, d0, d1, m, e1))
        elif m1 - m0 >= Fr(1, 2 ** 40):
            m = (m0 + m1) / 2
            stack += [(m0, m, d0, d1, e0, e1), (m, m1, d0, d1, e0, e1)]
        else:
            nfail += 1
            log(f"FAIL m=[{float(m0)},{float(m1)}] d=[{float(d0)},{float(d1)}] eps=[{float(e0)},{float(e1)}] lows={lows}")
            if nfail > 10:
                break
    return nbox, nfail, worst, time.time() - t0


if __name__ == '__main__':
    log = lambda s: print(s, flush=True)
    D0, D1 = Fr(sys.argv[1]), Fr(sys.argv[2])
    ND, NM, NE, K0, K1 = (int(x) for x in sys.argv[3:8])
    log(f"a-tail chart, mean value in (d, eps) at fixed m_a: a >= 250, d in [{D0},{D1}], eps cells {K0}..{K1 - 1} of {NE}; grid {ND} x {NM}")
    nbox, nfail, worst, dt = run(D0, D1, ND, NM, NE, K0, K1, log)
    log(f"boxes accepted: {nbox}, failures: {nfail}, time {dt:.1f} s")
    for k in range(3):
        if worst[k]:
            log(f"  smallest certified lower bound of L{k + 1}: {worst[k][0]:.6g} on {worst[k][1]}")
    log("RESULT: REGION VERIFIED" if nfail == 0 else "RESULT: FAILED")
