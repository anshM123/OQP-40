"""Numerical check (not a proof) of the far-tail strip form tb_sx_dtail.logG_dtail_strip against the definitions
(mpmath numerical differentiation of log ref_F): a L1, L2, a L3 at thin points with d >= 512, 0 <= a <= 3.
Usage: python tb_sx_dtail_test.py > tb_sx_dtail_test.log"""
from fractions import Fraction as Fr
import mpmath as mp
import tb_arb as T
import tb_sx_dtail as X
from tb_check_arb import ref_margins

worst = 0.0
for n, a, d in [(37, Fr(1, 2), 600), ('inf', Fr(1, 2), 600), (37, Fr(1, 100), 700), (100, Fr(3), 520),
                (37, Fr(1, 1000), 512), (1000, Fr(2), 2000), (50, Fr(1, 10), 1000)]:
    e = Fr(0) if n == 'inf' else Fr(1, n)
    w = Fr(1, d)
    G = X.logG_dtail_strip(T.J.var(X.q(a), 0, T.MP), w, w, e, e, T.MP)
    N, _ = X.norm_from_G(G, X.q(a))
    nn = 1000 if n == 'inf' else n
    mp.mp.dps = int(80 + (float(a) + d) / 2 + 3 * nn / 10)
    am = mp.mpf(a.numerator) / a.denominator
    L1, L2, L3 = ref_margins(n, am, am + d)
    ref = (am * L1, L2, am * L3)
    errs = [abs(mp.mpf(N[k].mid().str(40, radius=False)) - ref[k]) for k in range(3)]
    worst = max(worst, max(float(x) for x in errs))
    print(f"n={n!s:5s} a={float(a):<6g} d={d}: aL1 {float(ref[0]):.12f} L2 {float(ref[1]):.12f} aL3 {float(ref[2]):.12f}"
          f"  |form - definition| = {float(errs[0]):.1e} {float(errs[1]):.1e} {float(errs[2]):.1e}  (ball radius {float(N[1].rad()):.0e})", flush=True)
print(f"max deviation {worst:.2e}")
