"""Second implementation of the exact check of Lemma 6(n) (min-apex kernel PSD), written separately from
verify_n.py and using sympy instead of python-flint.

For the min-apex kernel E(s,t) = K_n(1,s,t) - sqrt(K_n(t,1,1) K_n(t,s,s)) (1 < s < t) and the weight
w(s) = sqrt(K_n(1,s,s)), F = E/(w(s) w(t)) must satisfy F >= 0, F_s >= 0, F_t <= 0, F_st <= 0 (Lemma 7).
Working variables X, Y with s = X^e, t = Y^e (e = 1 if 3 | n, else 3). With r = sqrt(q1 q2), every function
alpha + beta r is stored as a pair, and derivatives use r_X = r q2_X/(2 q2), r_Y = r (q1 q2)_Y/(2 q1 q2).
Here the four conditions are built directly from the quotient rule for F (not from the DX/DY operators of
verify_n.py), then each is reduced by its gcd and checked by Lemma 9 (squaring) and the shift X = 1+u, Y = 1+u+v.
Usage: python sympy_verify.py n"""
import sys
import time
from math import comb

import sympy as sp

n = int(sys.argv[1])
e = 1 if n % 3 == 0 else 3
X, Y, u, v = sp.symbols('X Y u v')


def h(k, a, b, c):
    return sp.Add(*[a**i * b**j * c**(k - i - j) for i in range(k + 1) for j in range(k + 1 - i)])


def Kw(a, b, c):
    """K_n(a^e, b^e, c^e) as a polynomial."""
    if e == 1:
        g = (a * b * c)**(n // 3)
    else:
        g = (a * b * c)**n
    return sp.expand(h(n, a**e, b**e, c**e) / comb(n + 2, 2) - g)


def exact_div(p, d):
    q, r = sp.div(sp.Poly(p, X, Y), sp.Poly(d, X, Y))
    assert r.is_zero, "division not exact"
    return q.as_expr()


t0 = time.time()
K1 = Kw(1, X, Y)
q1 = exact_div(Kw(Y, 1, 1), (Y - 1)**2)
q2 = exact_div(Kw(Y, X, X), (Y - X)**2)
pt = exact_div(Kw(1, X, X), (X - 1)**2)
ptY = pt.subs(X, Y)
# w(X) = (X-1) sqrt(pt(X));  lam(X) = w'/w = 1/(X-1) + pt'/(2 pt) = Nw/Dw
Nw = sp.expand(2 * pt + (X - 1) * sp.diff(pt, X))
Dw = sp.expand(2 * (X - 1) * pt)
NwY, DwY = Nw.subs(X, Y), Dw.subs(X, Y)
q12 = sp.expand(q1 * q2)


# a pair (a, b) means a + b r with r = sqrt(q1 q2); derivatives return pairs over the common denominators below
def dX(p):
    """2 q2 * d/dX (a + b r)"""
    a, b = p
    return (sp.expand(2 * q2 * sp.diff(a, X)), sp.expand(2 * q2 * sp.diff(b, X) + b * sp.diff(q2, X)))


def dY(p):
    """2 q1 q2 * d/dY (a + b r)"""
    a, b = p
    return (sp.expand(2 * q12 * sp.diff(a, Y)), sp.expand(2 * q12 * sp.diff(b, Y) + b * sp.diff(q12, Y)))


def comb_(*terms):
    a = sp.Add(*[c * p[0] for c, p in terms])
    b = sp.Add(*[c * p[1] for c, p in terms])
    return (sp.expand(a), sp.expand(b))


E = (K1, sp.expand(-(Y - 1) * (Y - X)))
EX = dX(E)                       # = 2 q2 E_X
EY = dY(E)                       # = 2 q1 q2 E_Y
EXY_raw = dY(EX)                 # = 2 q1 q2 d/dY(2 q2 E_X) = 4 q1 q2 q2_Y E_X + 4 q1 q2^2 E_XY
# quotient rule, all multiplied by positive factors:
# F_X ww = E_X - lam(X) E      -> times 2 q2 Dw(X):      Dw(X) EX - 2 q2 Nw(X) E            (sign of F_X)
# F_Y ww = E_Y - lam(Y) E      -> times 2 q1 q2 Dw(Y):   Dw(Y) EY - 2 q1 q2 Nw(Y) E         (sign of F_Y)
# F_XY ww = E_XY - lam(Y) E_X - lam(X) E_Y + lam(X) lam(Y) E, times 4 q1 q2^2 Dw(X) Dw(Y):
#   Dw Dw' (EXY_raw - 2 q1 q2_Y EX) - 2 q1 q2 Nw(Y) Dw(X) EX - 2 q2 Nw(X) Dw(Y) EY + 4 q1 q2^2 Nw Nw' E
q2Y = sp.diff(q2, Y)
FX = comb_((Dw, EX), (-2 * q2 * Nw, E))
FY = comb_((DwY, EY), (-2 * q12 * NwY, E))
FXY = comb_((Dw * DwY, EXY_raw), (-Dw * DwY * 2 * q1 * q2Y, EX), (-2 * q12 * NwY * Dw, EX),
            (-2 * q2 * Nw * DwY, EY), (4 * q1 * q2**2 * Nw * NwY, E))
conds = {'F >= 0': (E, +1), 'F_X >= 0': (FX, +1), 'F_Y <= 0': (FY, -1), 'F_XY <= 0': (FXY, -1)}


def shifted_coeffs(p):
    s = sp.Poly(sp.expand(p.subs({X: 1 + u, Y: 1 + u + v}, simultaneous=True)), u, v)
    return s.coeffs()


def SP(p):
    cs = shifted_coeffs(p)
    return len(cs) > 0 and all(c >= 0 for c in cs), len(cs)


ok = True
for name, p in [('q1', q1), ('q2', q2), ('pt', pt), ('Dw', Dw)]:
    good, nt = SP(p)
    if name != 'Dw':
        good = good and p.subs({X: 1, Y: 1}) > 0
    ok &= good
    print(f"  {name}: SP and positive on the closed region: {good} ({nt} terms)", flush=True)
for name, (pair, sign) in conds.items():
    a, b = sign * pair[0], sign * pair[1]          # we need a + b r >= 0
    g = sp.gcd(sp.Poly(a, X, Y), sp.Poly(b, X, Y)).as_expr()
    gc, gf = sp.factor_list(g)
    gpos = gc > 0 and all(SP(f)[0] for f, m in gf if f.free_symbols)
    a2, b2 = sp.cancel(a / g), sp.cancel(b / g)
    Delta = sp.expand(a2**2 - b2**2 * q12)
    # Lemma 9: either (a2 SP and Delta SP) or (b2 SP and -Delta SP)
    ok_a = SP(a2)[0] and SP(Delta)[0]
    ok_b = SP(b2)[0] and SP(-Delta)[0]
    good = gpos and (ok_a or ok_b)
    ok &= good
    print(f"  {name}: gcd positive {gpos}; route (a) {ok_a}; route (b) {ok_b}; deg Delta "
          f"{sp.Poly(Delta, X, Y).total_degree()}", flush=True)
print(f"RESULT n = {n}: {'VERIFIED' if ok else 'FAILED'} ({time.time() - t0:.0f} s)", flush=True)
