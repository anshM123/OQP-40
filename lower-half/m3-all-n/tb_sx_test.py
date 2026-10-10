"""Numerical check (not a proof) of the strip formulas of tb_sx.py against direct high-precision evaluation of the
definitions (tb_formulas_mp.ref_F / ref_F_inf, mpmath numerical differentiation), near a = 0, d = 0 and the corner.
Ghat = log(F b/a):  Ghat_a = L1 - 1/a,  Ghat_b = 1/b - L2,  Ghat_ab = L1 L2 - L3.
Usage: python tb_sx_test.py > tb_sx_test.log"""
import sys
import time
from fractions import Fraction as Fr
import mpmath as mp
from flint import arb
import tb_sx as S
from tb_check_arb import ref_margins


def ref_G(n, a, b, dps=None):
    nn = 1000 if n == 'inf' else n
    mp.mp.dps = dps or int(70 + (a + b) / 2 + 3 * nn / 10)
    a, b = mp.mpf(a), mp.mpf(b)
    L1, L2, L3 = ref_margins(n, a, b)
    return L1 - 1 / a, 1 / b - L2, L1 * L2 - L3


def mid(x):
    return float(x.mid())


def eps_of(n):
    return Fr(0) if n == 'inf' else Fr(1, n)


def thin(form, coords, a, y, n, corner=False):
    e = eps_of(n)
    a, y = Fr(a), Fr(y)
    r = S.evaluate(form, coords, a, a, y, y, e, e, corner=corner)
    G = r.G.p
    if coords == 'ab':
        return G.coef(1, 0), G.coef(0, 1), G.coef(1, 1)
    c10, c01, c11, c02 = G.coef(1, 0), G.coef(0, 1), G.coef(1, 1), G.coef(0, 2)
    return c10 - c01, c01, c11 - 2 * c02


worst = 0.0
lines = []
cases = []
for n in (37, 100, 1000, 'inf'):
    for (a, b) in [(Fr(1, 2), Fr(3, 4)), (Fr(1, 4), Fr(2)), (Fr(0), Fr(1)), (Fr(0), Fr(5)), (Fr(0), Fr(15, 2)),
                   (Fr(1, 8), Fr(6)), (Fr(2), Fr(5, 2)), (Fr(3), Fr(31, 10)), (Fr(1), Fr(1001, 1000))]:
        cases.append(('direct', 'ab', a, b, n))
    for (a, d) in [(Fr(3, 4), Fr(1, 10 ** 6)), (Fr(3, 4), Fr(1, 100)), (Fr(2), Fr(1, 3)), (Fr(11, 4), Fr(5))]:
        cases.append(('direct', 'ad', a, d, n))
    for (a, b) in [(Fr(0), Fr(8)), (Fr(0), Fr(40)), (Fr(1, 2), Fr(20)), (Fr(3), Fr(200)), (Fr(0), Fr(500))]:
        cases.append(('nu', 'ab', a, b, n))
for (form, coords, a, y, n) in cases:
    t0 = time.time()
    g = thin(form, coords, a, y, n)
    dt = time.time() - t0
    b = y if coords == 'ab' else a + y
    aref = a if a > 0 else Fr(1, 10 ** 20)
    nn = 1000 if n == 'inf' else n
    ref = ref_G(n, float(aref) if a > 0 else mp.mpf('1e-20'), float(b), dps=None if a > 0 else int(100 + float(b) / 2 + 3 * nn / 10))
    errs = []
    for k in range(3):
        rv = ref[k]
        if a == 0 and k == 0:
            # Ghat_a at a = 1e-20 vs a = 0: difference ~ 1e-20 * Ghat_aa
            pass
        e = abs(mp.mpf(g[k].mid().str(30, radius=False)) - rv)
        errs.append(float(e))
        worst = max(worst, float(e))
    print(f"{form:6s} {coords} n={n!s:4s} a={float(a):.4g} y={float(y):.4g}: Ghat_a={mid(g[0]):+.12f} Ghat_b={mid(g[1]):+.12f} "
          f"Ghat_ab={mid(g[2]):+.12f}  |diff| = {errs[0]:.1e} {errs[1]:.1e} {errs[2]:.1e}  rad {float(g[0].rad()):.0e}  ({dt:.2f} s)", flush=True)

# corner: expansion at (0, 0), evaluated at small (a, b) through the Taylor polynomial
for n in (37, 100, 'inf'):
    e = eps_of(n)
    t0 = time.time()
    r = S.evaluate('direct', 'ab', Fr(0), Fr(0), Fr(0), Fr(0), e, e, corner=True)
    dt = time.time() - t0
    G = r.G.p
    L = G.L
    J = G.sp.top[0]
    for (a, b) in [(0.01, 0.02), (0.05, 0.06), (0.1, 0.3), (0.2, 0.25), (0.3, 0.5), (0.5, 0.55)]:
        ga = sum(float(((i + 1) * G.coef(i + 1, j)).mid()) * a ** i * b ** j for i in range(L - 1) for j in range(J + 1))
        gb = sum(float(((j + 1) * G.coef(i, j + 1)).mid()) * a ** i * b ** j for i in range(L) for j in range(J))
        gab = sum(float(((i + 1) * (j + 1) * G.coef(i + 1, j + 1)).mid()) * a ** i * b ** j for i in range(L - 1) for j in range(J))
        ref = [x.real for x in ref_G(n, a, b, dps=120)]
        errs = [abs(x - float(y)) for x, y in zip((ga, gb, gab), ref)]
        worst = max(worst, max(errs))
        print(f"corner n={n!s:4s} (a,b)=({a},{b}): Ghat_a={ga:+.12f} Ghat_b={gb:+.12f} Ghat_ab={gab:+.12f} |diff| = "
              f"{errs[0]:.1e} {errs[1]:.1e} {errs[2]:.1e}   (expansion {dt:.2f} s)", flush=True)
print(f"max |diff| = {worst:.2e}")
