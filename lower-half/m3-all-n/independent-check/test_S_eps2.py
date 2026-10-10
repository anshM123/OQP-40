"""Test of tb_arb.S_of with dual jets in mode MT2 (used by tb_bb.py --dual mixed3 after 00:20).

S_of(X, cx) with eps a jet returns X.compose(S) + dE * X.compose(S_eps): the eps-expansion stops at first order, so
every (i, j, 2) slot of the S jet is exactly 0, while MT2 carries (i, j, 2) slots and tighten() uses them to enclose
the (i, j, 1) slots over the box:  Q_(i,j,1)(box) <- Q_(i,j,1)(centre) + ... + 2 Q_(i,j,2)(box) [-r_e, r_e].
Here we compare the tightened enclosure of d_eps S(d; eps) on a box with its TRUE values (mpmath, from the
definition kappa_n(x) = K_n(e^{x eps}, 1, 1), S = kappa_n/x^2, interpolated in eps by the closed form of (F1)).
"""
import sys
import os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
import mpmath as mp
from flint import arb, fmpq
import tb_arb as T

mp.mp.dps = 60


def S_true(x, eps):
    """S(x; eps) = kappa_n(x)/x^2 with kappa_n(x) = c (P(x) - 1)/Q(x) - e^{x/3} (exact at eps = 1/n, smooth in eps)."""
    x = mp.mpf(x)
    eps = mp.mpf(eps)
    if eps == 0:
        kap = 2 * (mp.exp(x) - 1 - x) / x ** 2 - mp.exp(x / 3)
    else:
        phi1 = lambda u: mp.expm1(u) / u
        c = 2 / (1 + eps)
        P = phi1(x * (1 + 2 * eps)) / phi1(x * eps)
        Q = x * phi1(x * eps)
        kap = c * (P - 1) / Q - mp.exp(x / 3)
    return kap / x ** 2


def dS_deps(x, eps, h=mp.mpf('1e-15')):
    return (S_true(x, eps + h) - S_true(x, eps - h)) / (2 * h)


def d2S_deps2(x, eps, h=mp.mpf('1e-10')):
    return (S_true(x, eps + h) - 2 * S_true(x, eps) + S_true(x, eps - h)) / h ** 2


def check_box(a0, a1, d0, d1, e0, e1):
    q = lambda x: arb(fmpq(x.numerator, x.denominator))
    from fractions import Fraction as Fr
    a0, a1, d0, d1, e0, e1 = (Fr(x) for x in (a0, a1, d0, d1, e0, e1))
    ac, dc, ec = (a0 + a1) / 2, (d0 + d1) / 2, (e0 + e1) / 2
    T.TIGHT['r'] = (arb(0, q((a1 - a0) / 2)), arb(0, q((d1 - d0) / 2)), arb(0, q((e1 - e0) / 2)))
    M = T.DUAL_MODE
    Ac = T.J.var(q(ac), 0, M)
    Dc = T.dvar(q(dc), M)
    Ec = T.J.var(q(ec), 2, M)
    Ab = T.J.var(arb.union(q(a0), q(a1)), 0, M)
    Db = T.dvar(arb.union(q(d0), q(d1)), M)
    Eb = T.J.var(arb.union(q(e0), q(e1)), 2, M)
    D = T.DJ(Dc, Db)
    cx = T.DCtx(Ec, Eb)
    S = T.S_of(D, cx)
    St = T.tighten(S.bj, S.cj)                      # what DJ._u('sqrt') feeds into sqrt
    i001 = M.idx[(0, 0, 1)]
    i002 = M.idx[(0, 0, 2)]
    enc_t = St.c[i001]
    enc_naive = S.bj.c[i001]
    print(f"box a=[{float(a0)},{float(a1)}] d=[{float(d0)},{float(d1)}] eps=[{float(e0)},{float(e1)}]")
    print(f"  (0,0,2) slot of the S box jet (should enclose S_eps,eps/2): {S.bj.c[i002]}   centre jet: {S.cj.c[i002]}")
    print(f"  naive enclosure of d_eps S on the box:     {enc_naive.mid().str(12)} +- {enc_naive.rad().str(3)}")
    print(f"  tightened enclosure of d_eps S on the box: {enc_t.mid().str(12)} +- {enc_t.rad().str(3)}")
    worst = 0
    viol = 0
    for d in (d0, dc, d1):
        for e in (e0, ec, e1):
            v = dS_deps(mp.mpf(d.numerator) / d.denominator, mp.mpf(e.numerator) / e.denominator)
            vv = arb(mp.nstr(v, 40))
            inside = enc_t.contains(vv) or vv.overlaps(enc_t)
            lo, hi = float(enc_t.lower()), float(enc_t.upper())
            out = max(lo - float(v), float(v) - hi, 0.0)
            worst = max(worst, out)
            if out > 0:
                viol += 1
            print(f"   d={float(d):.6f} eps={float(e):.6f}: true d_eps S = {mp.nstr(v, 15)}  in tightened enclosure: {out == 0}  (outside by {out:.3e})")
    x = mp.mpf(dc.numerator) / dc.denominator
    print(f"  true S_eps,eps at the centre: {mp.nstr(d2S_deps2(x, mp.mpf(ec.numerator) / ec.denominator), 10)}")
    return viol, worst


if __name__ == '__main__':
    tot = 0
    # boxes of the size accepted in the logs (C2 d-strip and C1 lo2 regions) and a larger one
    for box in [(24.46875, 24.5, 2.0625, 2.125, 0, 1 / 74), (38.6875, 38.75, 1.3125, 1.375, 1 / 74, 1 / 37),
                (52, 52.0625, 2.5625, 2.625, 0, 1 / 148), (46.34375, 46.375, 3.1875, 3.25, 1 / 74, 3 / 148),
                (10, 10.0625, 0.5, 0.5625, 0, 1 / 37), (3, 3.0625, 2.9375, 3.0, 0, 1 / 37)]:
        from fractions import Fraction as Fr
        bx = [Fr(x).limit_denominator(10 ** 6) for x in box]
        v, w = check_box(*bx)
        tot += v
    print("total violations:", tot)
