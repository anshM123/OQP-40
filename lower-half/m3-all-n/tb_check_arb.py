"""Theorem B: numerical check of the ball-arithmetic formulas (tb_arb.py) against direct high-precision evaluation of
the definitions (tb_formulas_mp.ref_F, mpmath numerical differentiation).  Checks the values L1, L2, L3 and the
gradients used by the centred forms.  Numerical comparison, not a proof.
Usage: python tb_check_arb.py"""
import random
import mpmath as mp
from flint import arb
import tb_arb as T
import tb_formulas_mp as M


def ref_margins(n, a, b):
    if n == 'inf':
        f = lambda x, y: mp.log(M.ref_F_inf(x, y))
    else:
        f = lambda x, y: mp.log(M.ref_F(n, x, y))
    la = mp.diff(lambda x: f(x, b), a)
    lb = mp.diff(lambda y: f(a, y), b)
    lab = mp.diff(lambda x, y: f(x, y), (a, b), (1, 1))
    return la, -lb, -(lab + la * lb)


def arb_margins(n, a, d, form, mode=T.MP):
    eps = arb(0) if n == 'inf' else arb(1) / n
    cx = T.Ctx(eps)
    A = T.J.var(arb(str(a)), 0, mode)
    B = T.J.var(arb(str(a)) + arb(str(d)), 1, mode)
    G = form(A, B, cx)
    return T.margins_from_logF(G)


if __name__ == '__main__':
    random.seed(7)
    worst = {}
    cases = []
    for n in (37, 50, 100, 1000, 'inf'):
        for _ in range(6):
            cases.append((n, round(10 ** random.uniform(0.5, 2.3), 6), round(10 ** random.uniform(0.5, 2.0), 6), 'nu'))
            cases.append((n, round(10 ** random.uniform(0.5, 2.3), 6), round(10 ** random.uniform(-3, 0.6), 6), 'mixed'))
        cases += [(n, 3.0, 3.2, 'nu'), (n, 3.0, 3.2, 'mixed'), (n, 64.0, 40.0, 'nu'), (n, 3.0, 0.001, 'mixed'),
                  (n, 150.0, 0.5, 'mixed'), (n, 5.0, 120.0, 'nu')]
    for (n, a, d, form) in cases:
        nn = 1000 if n == 'inf' else n
        mp.mp.dps = int(50 + (a + d) / 2.3 + 3 * nn / 10)
        r = ref_margins(n, mp.mpf(str(a)), mp.mpf(str(a)) + mp.mpf(str(d)))
        (L1, L2, L3), _ = arb_margins(n, a, d, T.logF_nu2 if form == 'nu' else T.logF_mixed3)
        for k, (x, y) in enumerate(zip((L1, L2, L3), r)):
            err = abs(mp.mpf(x.mid().str(40, radius=False)) - y)
            rad = float(x.rad())
            key = (form, k)
            rel = err / max(abs(y), mp.mpf('1e-30'))
            if key not in worst or rel > worst[key][0]:
                worst[key] = (rel, n, a, d, float(y), rad)
    for key in sorted(worst):
        rel, n, a, d, y, rad = worst[key]
        print(f"form {key[0]:5s} L{key[1] + 1}: max rel. deviation {float(rel):.2e} (n={n}, a={a}, d={d}, value {y:.6g}, ball radius {rad:.1e})")
    # gradient check (mode MB) at a few points: compare d/da, d/db of L3 with finite differences of the reference
    for (n, a, d, form) in [(37, 20.0, 10.0, 'nu'), (100, 64.0, 2.0, 'mixed'), ('inf', 8.0, 30.0, 'nu')]:
        (L1, L2, L3), grads = arb_margins(n, a, d, T.logF_nu2 if form == 'nu' else T.logF_mixed3, T.MB)
        h = mp.mpf('1e-6')
        mp.mp.dps = 60
        A, Bv = mp.mpf(a), mp.mpf(a + d)
        fa = (ref_margins(n, A + h, Bv)[2] - ref_margins(n, A - h, Bv)[2]) / (2 * h)
        fb = (ref_margins(n, A, Bv + h)[2] - ref_margins(n, A, Bv - h)[2]) / (2 * h)
        print(f"grad L3 at n={n}, a={a}, d={d}: jets ({float(grads[2][0].mid()):.8g}, {float(grads[2][1].mid()):.8g}), "
              f"finite differences ({float(fa):.8g}, {float(fb):.8g})")
