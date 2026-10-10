"""Numerical check (not a proof): the chart formulas of tb_tail2.py (a >= 64), tb_dtail.py (d >= 512) and the core
forms of tb_arb.py, evaluated at thin points, against mpmath numerical differentiation of the definitions
(tb_formulas_mp.ref_F), at random points for n = 37, 50, 100, 1000 and near the chart boundaries a = 64, d = 3,
d = 64, d = 512.  The chart forms enclose some exponentially small terms by balls, so their values are balls that
must contain the reference values (up to the ~1e-15 accuracy of the numerical differentiation).
Usage: python tb_check_charts.py > tb_check_charts.log"""
import random
from fractions import Fraction as Fr
import mpmath as mp
from flint import arb
import tb_arb as T
import tb_tail as TT
import tb_tail2 as T2
import tb_dtail as DT
from tb_check_arb import ref_margins

random.seed(31)
pts = []
for n in (37, 50, 100, 1000):
    for _ in range(3):
        pts.append(('tail', n, random.uniform(64, 400), random.uniform(0.01, 3)))
        pts.append(('tail', n, random.uniform(64, 400), random.uniform(3, 500)))
        pts.append(('dtail', n, random.uniform(3, 64), random.uniform(512, 1500)))
        pts.append(('core', n, random.uniform(3, 64), random.uniform(3, 512)))
        pts.append(('dstrip', n, random.uniform(3, 64), random.uniform(0.001, 3)))
    pts += [('tail', n, 64.0, 3.0), ('tail', n, 64.0, 64.0), ('tail', n, 64.0, 0.01), ('tail', n, 64.0, 511.0),
            ('dtail', n, 3.0, 512.0), ('dtail', n, 64.0, 512.0), ('core', n, 3.0, 3.0), ('core', n, 64.0, 512.0),
            ('dstrip', n, 3.0, 0.001), ('dstrip', n, 64.0, 3.0)]
worst = {}
for (chart, n, a, d) in pts:
    a, d = round(a, 6), round(d, 6)
    mp.mp.dps = int(60 + (a + d) / 2.3 + 3 * n / 10)
    ref = ref_margins(n, mp.mpf(str(a)), mp.mpf(str(a)) + mp.mpf(str(d)))
    eps = arb(1) / n
    cx = T.Ctx(eps)
    if chart == 'tail':
        m = 1 / (arb(str(a)) * T.g_phi1(arb(str(a)) * eps, 0)[0])
        form = T2.logF_t2_nu2 if d >= 3 else T2.logF_t2_mixed3
        L, _ = T.margins_from_logF(form(m, TT.dj(arb(str(d)), T.MP), cx, 64, Fr(512)))
    elif chart == 'dtail':
        w = Fr(1) / Fr(str(d))
        L, _ = T.margins_from_logF(DT.logF_dtail(T.J.var(arb(str(a)), 0, T.MP), w, w, Fr(1, n), Fr(1, n), T.MP))
    else:
        A = T.J.var(arb(str(a)), 0, T.MP)
        D = T.dvar(arb(str(d)), T.MP)
        form = T.logF_nu2 if chart == 'core' else T.logF_mixed3
        L, _ = T.margins_from_logF(form(A, A + D, cx, D))
    for k in range(3):
        x, y = L[k], ref[k]
        err = abs(mp.mpf(x.mid().str(40, radius=False)) - y)
        excess = max(mp.mpf(0), err - mp.mpf(x.rad().str(40, radius=False)))     # deviation outside the ball
        rel = excess / abs(y)
        key = (chart, k)
        if key not in worst or rel > worst[key][0]:
            worst[key] = (rel, n, a, d, float(y), float(x.rad()))
for key in sorted(worst):
    rel, n, a, d, y, rad = worst[key]
    print(f"chart {key[0]:6s} L{key[1] + 1}: max relative deviation outside the ball {float(rel):.2e} "
          f"(n={n}, a={a}, d={d}, value {y:.6g}, ball radius {rad:.1e})")
