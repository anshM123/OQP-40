"""Independent verifier, tail drivers (iv_far.py; atoms bounded rigorously by iv_atoms.py), all eps in [0, 1/37].
  farreg   A0 A1 NA NW NE : 3 <= a <= 250 (A0..A1), d >= 512 (w = 1/d in [0, 1/512]); centre a + a-gradient, (w, eps) cells.
  farstrip A0 A1 NA NW NE : 0 <= a <= 3, d >= 512; normalised conditions a L1, L2, a L3 (G = log(F/a)).
  double   NM NW NE       : a >= 250 (m_a cells) and d >= 512 (w cells), every quantity naive on the cell.
  atail    D0 D1 ND NM NE : a >= 250 (m_a in [0, m(250, e0)] for the eps cell [e0, e1]), D0 <= d <= D1; centre d + d-gradient.
The m_a range [0, m(250, e0)] contains m_a(a, eps) for every a >= 250 and eps >= e0 (m decreasing in a and eps), so the
cells cover {a >= 250}; points with a < 250 that they also contain are covered elsewhere and only enlarge the check.
Atom bounds are evaluated at the smallest a (resp. d) of each cell: a_min = log(1 + e1/m1)/e1.
"""
import sys
import time
from fractions import Fraction as Fr
from flint import arb, fmpq
import iv_far as T
import iv_atoms as AT
from iv_jet import Jet, NotPos

q = T.q


def m250(e0):
    """an upper bound (Fraction) of m(250, e0) = 1/(250 phi(250 e0))."""
    v = T.m_of(arb(250), q(e0))
    return Fr(v.upper().str(30, radius=False)) * (1 + Fr(1, 10 ** 9))


def amin_of(m1, e1):
    """lower bound of a on the cell m <= m1, eps <= e1 (a = log(1 + eps/m)/eps is decreasing in m and in eps)."""
    if e1 == 0:
        return (1 / q(m1)).lower()
    return ((1 + q(e1) / q(m1)).log() / q(e1)).lower()


def run_far(mode, A0, A1, NA, NW, NE, log):
    X, parts = AT.far_d_atom_bound(512, 3 if mode == 'farstrip' else 250, strip=(mode == 'farstrip'))
    X = 10 * X
    log(f"atom bound used: X = {X:.3e} (10 x the bound {parts})")
    t0 = time.time()
    stack = [(A0 + (A1 - A0) * i / NA, A0 + (A1 - A0) * (i + 1) / NA, Fr(j, 512 * NW), Fr(j + 1, 512 * NW),
              Fr(k, 37 * NE), Fr(k + 1, 37 * NE)) for i in range(NA) for j in range(NW) for k in range(NE)]
    nbox = nfail = 0
    worst = [None] * 3
    while stack:
        a0, a1, w0, w1, e0, e1 = stack.pop()
        ac, ra = (a0 + a1) / 2, (a1 - a0) / 2
        try:
            if mode == 'farreg':
                Gc = T.logF_far_reg(Jet.var(q(ac), 0, T.SPT), w0, w1, e0, e1, X)
                Lc, _, _ = T.conds_ad(Gc)
                Gb = T.logF_far_reg(Jet.var(arb.union(q(a0), q(a1)), 0, T.SPT), w0, w1, e0, e1, X)
                _, La, _ = T.conds_ad(Gb)
            else:
                Gc = T.logG_far_strip(Jet.var(q(ac), 0, T.SPT), w0, w1, e0, e1, X)
                Lc, _ = T.conds_strip(Gc, q(ac))
                Ab = arb.union(q(a0), q(a1))
                Gb = T.logG_far_strip(Jet.var(Ab, 0, T.SPT), w0, w1, e0, e1, X)
                _, La = T.conds_strip(Gb, Ab)
            lows = [Lc[k] - abs(La[k]) * q(ra) for k in range(3)]
            ok = all(l > 0 for l in lows)
            ca = max(float((abs(La[k]) * q(ra)).upper()) for k in range(3))
            cc = max(float(Lc[k].rad()) for k in range(3))
        except (NotPos, ZeroDivisionError, ValueError):
            ok, lows, ca, cc = False, None, 1.0, 0.0
        if ok:
            nbox += 1
            for k in range(3):
                v = float(lows[k].lower())
                if worst[k] is None or v < worst[k][0]:
                    worst[k] = (v, tuple(float(x) for x in (a0, a1, w0, w1, e0, e1)))
            continue
        if ca >= cc and a1 - a0 >= Fr(1, 2 ** 14):
            m = (a0 + a1) / 2
            stack += [(a0, m, w0, w1, e0, e1), (m, a1, w0, w1, e0, e1)]
        elif e1 - e0 >= Fr(1, 2 ** 26) and 30 * float(e1 - e0) >= 512 * float(w1 - w0):
            m = (e0 + e1) / 2
            stack += [(a0, a1, w0, w1, e0, m), (a0, a1, w0, w1, m, e1)]
        elif w1 - w0 >= Fr(1, 2 ** 30):
            m = (w0 + w1) / 2
            stack += [(a0, a1, w0, m, e0, e1), (a0, a1, m, w1, e0, e1)]
        else:
            nfail += 1
            log(f"FAIL a=[{float(a0)},{float(a1)}] w=[{float(w0)},{float(w1)}] eps=[{float(e0)},{float(e1)}] lows={lows}")
            if nfail > 10:
                break
    return nbox, nfail, worst, time.time() - t0


def run_double(NM, NW, NE, log):
    t0 = time.time()
    nbox = nfail = 0
    worst = [None] * 3
    stack = []
    for k in range(NE):
        e0, e1 = Fr(k, 37 * NE), Fr(k + 1, 37 * NE)
        mtop = m250(e0)
        for i in range(NM):
            for j in range(NW):
                stack.append((mtop * i / NM, mtop * (i + 1) / NM, Fr(j, 512 * NW), Fr(j + 1, 512 * NW), e0, e1))
    while stack:
        m0, m1, w0, w1, e0, e1 = stack.pop()
        try:
            amin = amin_of(m1, e1)
            if not (amin >= 100):
                raise NotPos('amin')
            X = 10 * AT.double_tail_bound(float(amin), 512)
            G = T.logF_double(m0, m1, w0, w1, e0, e1, X)
            L, _, _ = T.conds_ad(G)
            ok = all(l > 0 for l in L)
        except (NotPos, ZeroDivisionError, ValueError):
            ok, L = False, None
        if ok:
            nbox += 1
            for kk in range(3):
                v = float(L[kk].lower())
                if worst[kk] is None or v < worst[kk][0]:
                    worst[kk] = (v, tuple(float(x) for x in (m0, m1, w0, w1, e0, e1)))
            continue
        if e1 - e0 >= Fr(1, 2 ** 24) and (L is None or float(e1 - e0) * 37 * 4 >= float(m1 - m0) * 250):
            me = (e0 + e1) / 2
            stack.append((m0, m1, w0, w1, e0, me))
            mtop = min(m1, m250(me))                 # upper half: only m <= m(250, me) can have a >= 250
            if mtop > m0:
                stack.append((m0, mtop, w0, w1, me, e1))
        elif m1 - m0 >= Fr(1, 2 ** 40):
            mm = (m0 + m1) / 2
            stack += [(m0, mm, w0, w1, e0, e1), (mm, m1, w0, w1, e0, e1)]
        elif w1 - w0 >= Fr(1, 2 ** 30):
            wm = (w0 + w1) / 2
            stack += [(m0, m1, w0, wm, e0, e1), (m0, m1, wm, w1, e0, e1)]
        else:
            nfail += 1
            log(f"FAIL m=[{float(m0)},{float(m1)}] w=[{float(w0)},{float(w1)}] eps=[{float(e0)},{float(e1)}] L={L}")
            if nfail > 10:
                break
    return nbox, nfail, worst, time.time() - t0


def run_atail(D0, D1, ND, NM, NE, log):
    t0 = time.time()
    nbox = nfail = 0
    worst = [None] * 3
    stack = []
    for k in range(NE):
        e0, e1 = Fr(k, 37 * NE), Fr(k + 1, 37 * NE)
        mtop = m250(e0)
        for i in range(NM):
            for j in range(ND):
                stack.append((mtop * i / NM, mtop * (i + 1) / NM, D0 + (D1 - D0) * j / ND, D0 + (D1 - D0) * (j + 1) / ND,
                              e0, e1))
    last = t0
    while stack:
        m0, m1, d0, d1, e0, e1 = stack.pop()
        if d0 < Fr(15, 4) < d1:
            stack += [(m0, m1, d0, Fr(15, 4), e0, e1), (m0, m1, Fr(15, 4), d1, e0, e1)]
            continue
        form = 'mix' if d1 <= Fr(15, 4) else 'nu'
        dc, rd = (d0 + d1) / 2, (d1 - d0) / 2
        try:
            amin = amin_of(m1, e1)
            if not (amin >= 100):
                raise NotPos('amin')
            X = 10 * AT.a_tail_atom_bound(float(amin), float(d1))[0]
            ma = arb.union(q(m0), q(m1))
            eps = arb.union(q(e0), q(e1)) if e1 > e0 else q(e0)
            Gc = T.logF_atail(ma, eps, Jet.var(q(dc), 1, T.SPT), X, form)
            Lc, _, _ = T.conds_ad(Gc)
            Gb = T.logF_atail(ma, eps, Jet.var(arb.union(q(d0), q(d1)), 1, T.SPT), X, form)
            _, _, Ld = T.conds_ad(Gb)
            lows = [Lc[kk] - abs(Ld[kk]) * q(rd) for kk in range(3)]
            ok = all(l > 0 for l in lows)
            cd = max(float((abs(Ld[kk]) * q(rd)).upper()) for kk in range(3))
            cc = max(float(Lc[kk].rad()) for kk in range(3))
        except (NotPos, ZeroDivisionError, ValueError):
            ok, lows, cd, cc = False, None, 1.0, 0.0
        if ok:
            nbox += 1
            for kk in range(3):
                v = float(lows[kk].lower())
                if worst[kk] is None or v < worst[kk][0]:
                    worst[kk] = (v, tuple(float(x) for x in (m0, m1, d0, d1, e0, e1)))
            if time.time() - last > 120:
                last = time.time()
                log(f"  progress: {nbox} boxes, stack {len(stack)}, {time.time() - t0:.0f} s")
            continue
        if cd >= cc and d1 - d0 >= Fr(1, 2 ** 14):
            m = (d0 + d1) / 2
            stack += [(m0, m1, d0, m, e0, e1), (m0, m1, m, d1, e0, e1)]
        elif e1 - e0 >= Fr(1, 2 ** 24) and (lows is None or float(e1 - e0) * 37 >= float(m1 - m0) * 250):
            m = (e0 + e1) / 2
            stack.append((m0, m1, d0, d1, e0, m))
            mtop = min(m1, m250(m))                  # upper half: only m <= m(250, m) can have a >= 250
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
    mode = sys.argv[1]
    if mode in ('farreg', 'farstrip'):
        A0, A1 = Fr(sys.argv[2]), Fr(sys.argv[3])
        NA, NW, NE = (int(x) for x in sys.argv[4:7])
        log(f"tail verifier {mode}: a in [{A0},{A1}], d >= 512 (w = 1/d in [0,1/512]), all eps in [0,1/37]; grid {NA}x{NW}x{NE}")
        nbox, nfail, worst, dt = run_far(mode, A0, A1, NA, NW, NE, log)
    elif mode == 'double':
        NM, NW, NE = (int(x) for x in sys.argv[2:5])
        log(f"tail verifier double: a >= 250 (m_a cells), d >= 512 (w cells), all eps in [0,1/37]; grid {NM}x{NW}x{NE}")
        nbox, nfail, worst, dt = run_double(NM, NW, NE, log)
    elif mode == 'atail':
        D0, D1 = Fr(sys.argv[2]), Fr(sys.argv[3])
        ND, NM, NE = (int(x) for x in sys.argv[4:7])
        log(f"tail verifier atail: a >= 250 (m_a in [0, m(250, e0)]), d in [{D0},{D1}], all eps in [0,1/37]; grid {ND}x{NM}x{NE}")
        nbox, nfail, worst, dt = run_atail(D0, D1, ND, NM, NE, log)
    else:
        raise SystemExit('mode?')
    log(f"boxes accepted: {nbox}, failures: {nfail}, time {dt:.1f} s")
    names = ('aL1', 'L2', 'aL3') if mode == 'farstrip' else ('L1', 'L2', 'L3')
    for k in range(3):
        if worst[k]:
            log(f"  smallest certified lower bound of {names[k]}: {worst[k][0]:.6g} on {worst[k][1]}")
    log("RESULT: REGION VERIFIED" if nfail == 0 else "RESULT: FAILED")
