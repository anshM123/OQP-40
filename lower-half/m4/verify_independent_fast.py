"""Independent exact verification (sympy only, written separately from exact_rule.py / python-flint) of a
polynomial share rule stored in JSON.

Checks:
 (1) the share identity  k(xy;ef) + k(ef;xy) = 2 K_n(x,y,e,f)  as an identity of polynomials in the qd-th roots
     X, Y, U, V of x, y, e, f, where K_n is rebuilt from its definition (sympy expansion of h_n and the geometric
     mean (XYUV)^{n qd/4});
 (2) the kernel lemma: the exponent-indexed matrix C(1, s^qd) (entries polynomials in s) is positive definite for
     0 < s < 1: every leading principal minor (sympy determinant of the leading block) has no root in (0,1)
     (computed by fraction-free Bareiss over ZZ[s] with sympy Poly; real-root isolation by sympy's
     Poly.intervals on [0,1] after removing the factors s and (1-s)) and is positive at s = 1/2.
     Identically-zero rows are checked to be zero and removed.
Usage: python verify_independent.py rule.json"""
import json
import sys
from fractions import Fraction
from math import comb

import sympy as sp

d = json.load(open(sys.argv[1]))
n, qd = d["n"], d["qd"]
N = n * qd
z = [sp.Rational(Fraction(x).numerator, Fraction(x).denominator) for x in d["z"]]
var = [(tuple(p), tuple(q)) for p, q in d["var"]]
vidx = {k: t for t, k in enumerate(var)}
live = sorted(set(d["exponents_units"]))
liveset = set(live)
X, Y, U, V, s = sp.symbols("X Y U V s", positive=True)
Cn = sp.Integer(comb(n + 3, 3))

# K_n in root variables: x = X^qd etc.
x, y, e, f = X ** qd, Y ** qd, U ** qd, V ** qd
h = sp.Integer(0)
# h_n by expansion of the generating function coefficient: sum over compositions
for c1 in range(n + 1):
    for c2 in range(n + 1 - c1):
        for c3 in range(n + 1 - c1 - c2):
            c4 = n - c1 - c2 - c3
            h += x ** c1 * y ** c2 * e ** c3 * f ** c4
Kn = sp.expand(h / Cn - (X * Y * U * V) ** sp.Integer(N // 4) if N % 4 == 0 else None)
assert N % 4 == 0, "qd must make n qd divisible by 4"
Kpoly = sp.Poly(Kn, X, Y, U, V)


def kap(a, b, i, j):
    return Kpoly.coeff_monomial(X ** a * Y ** b * U ** i * V ** j)


def gam(p, q):
    # canonical pairs p=(a<=b), q=(i<=j)
    if p == q:
        return kap(p[0], p[1], q[0], q[1])
    if (p, q) in vidx:
        return z[vidx[(p, q)]]
    if (q, p) in vidx:
        return 2 * kap(p[0], p[1], q[0], q[1]) - z[vidx[(q, p)]]
    if q[1] not in liveset:
        return sp.Integer(0)
    if p[1] not in liveset:
        return 2 * kap(p[0], p[1], q[0], q[1])
    raise KeyError((p, q))


def k_rule(A_, B_, C_, D_):
    tot = sp.Integer(0)
    for a in range(N + 1):
        for b in range(N + 1 - a):
            for i in range(N + 1 - a - b):
                j = N - a - b - i
                g = gam((min(a, b), max(a, b)), (min(i, j), max(i, j)))
                if g != 0:
                    tot += g * A_ ** a * B_ ** b * C_ ** i * D_ ** j
    return sp.expand(tot)


k1 = k_rule(X, Y, U, V)
k2 = k_rule(U, V, X, Y)
ident = sp.expand(k1 + k2 - 2 * Kn)
print(f"n={n} qd={qd}: share identity holds exactly: {ident == 0}", flush=True)
assert ident == 0

# kernel matrix C(1, s^qd): entry (i,j) = coefficient of U^i V^j in k(1, s; U, V) where Y = s (root of t)
kp = sp.Poly(sp.expand(k1.subs({X: 1, Y: s})), U, V)
idx = list(range(N + 1))
Cm = sp.zeros(N + 1, N + 1)
for (i, j), c in zip(kp.monoms(), kp.coeffs()):
    Cm[i, j] = c
# symmetric?
assert all(sp.expand(Cm[i, j] - Cm[j, i]) == 0 for i in idx for j in idx)
rows = [i for i in idx if sp.expand(Cm[i, i]) != 0]
for i in idx:
    if i not in rows:
        assert all(sp.expand(Cm[i, j]) == 0 for j in idx), f"zero-diagonal row {i} not identically zero"
print(f"nonzero rows (exponents in units 1/{qd}): {rows}", flush=True)
Cr = Cm.extract(rows, rows)
# integer polynomial matrix (clear denominators), fraction-free Bareiss over ZZ[s] with sympy Poly
den = 1
for i in range(Cr.rows):
    for j in range(Cr.cols):
        for c in sp.Poly(Cr[i, j], s).all_coeffs():
            den = sp.ilcm(den, sp.Rational(c).q)
Afull = [[sp.Poly(sp.expand(Cr[i, j] * den), s, domain='ZZ') for j in range(Cr.cols)] for i in range(Cr.rows)]
# parity blocks: if every entry with (exponent_i + exponent_j) odd vanishes identically, the matrix is the direct sum
# of its even- and odd-exponent blocks, and it suffices to treat them separately
par = [rows[t] % 2 for t in range(len(rows))]
split = all(Afull[i][j].is_zero for i in range(len(rows)) for j in range(len(rows)) if (par[i] + par[j]) % 2 == 1)
groups = [[t for t in range(len(rows)) if par[t] == 0], [t for t in range(len(rows)) if par[t] == 1]] if split     else [list(range(len(rows)))]
groups = [g for g in groups if g]
print(f"parity block structure: {split}; blocks {[len(g) for g in groups]}", flush=True)
import flint


def to_fz(P):
    return flint.fmpz_poly([int(c) for c in reversed(P.all_coeffs())])


def to_sp(F):
    return sp.Poly(list(reversed([int(c) for c in F.coeffs()])) or [0], s, domain='ZZ')


minors = []
for g in groups:
    A = [[to_fz(Afull[i][j]) for j in g] for i in g]
    mdim = len(A)
    prev = flint.fmpz_poly([1])
    for k in range(mdim):
        piv = A[k][k]
        minors.append(to_sp(piv))
        if k == mdim - 1:
            break
        assert piv != 0, "zero pivot"
        for i in range(k + 1, mdim):
            for j in range(k + 1, mdim):
                num = piv * A[i][j] - A[i][k] * A[k][j]
                q, r = divmod(num, prev)
                assert r == 0, "inexact division"
                A[i][j] = q
        prev = piv
ok_all = True
one_minus_s = sp.Poly(1 - s, s, domain='ZZ')
spoly = sp.Poly(s, s, domain='ZZ')
for k, P in enumerate(minors, start=1):
    deg = P.degree()
    a0 = 0
    while P.eval(0) == 0:
        P = P.exquo(spoly); a0 += 1
    b0 = 0
    while P.eval(1) == 0:
        P = P.exquo(one_minus_s); b0 += 1
    ivs = P.intervals(inf=0, sup=1)
    val = P.eval(sp.Rational(1, 2))
    ok = (len(ivs) == 0 and val > 0)
    ok_all = ok_all and ok
    print(f"  minor {k}: degree {deg} = (scaled) s^{a0} (1-s)^{b0} Q, real roots of Q in [0,1]: {len(ivs)}, "
          f"Q(1/2) > 0: {val > 0} -> {'OK' if ok else 'FAIL'}", flush=True)
print("INDEPENDENT VERIFICATION (fast variant):", "PASSED" if ok_all else "FAILED")
