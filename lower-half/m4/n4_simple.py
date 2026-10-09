"""n = 4 (q = 2): the 3-parameter family of parity-normalised polynomial rules, and a rule with small rationals.

Free classes (half-integer units) with nonzero values, under (S), (D), (P):
  g1 = gamma((0,0);(4,4)), g2 = gamma((0,2);(2,4)), g3 = gamma((0,2);(3,3)), g4 = gamma((1,1);(2,4)),
  g5 = gamma((1,1);(3,3)), g6 = gamma((0,4);(2,2)), g7 = gamma((1,3);(2,2)).
The endpoint conditions C(1,1) v(+-1) = 0 reduce to (by hand, LOG.md)
  g3 = -g4 - g5,  g7 = -2 g4 - g5,  g6 = g4 + g5/2 + 13/35,  g1 = 9/35 + g5/2 - 2 g2.
This script builds the rule for given (g2, g4, g5), writes it in the JSON format of exact_rule.py and runs the exact
check (minors of both parity blocks positive on (0,1)).
Usage: python n4_simple.py g2 g4 g5 [out.json]"""
import json
import sys
from fractions import Fraction

import flint

from polyrule import Setup
from exactcheck import bareiss_minors, positive_on_open01

g2, g4, g5 = (Fraction(a) for a in sys.argv[1:4])
out = sys.argv[4] if len(sys.argv) > 4 else None
g3 = -g4 - g5
g7 = -2 * g4 - g5
g6 = g4 + g5 / 2 + Fraction(13, 35)
g1 = Fraction(9, 35) + g5 / 2 - 2 * g2
vals = {((0, 0), (4, 4)): g1, ((0, 2), (2, 4)): g2, ((0, 2), (3, 3)): g3, ((1, 1), (2, 4)): g4,
        ((1, 1), (3, 3)): g5, ((0, 4), (2, 2)): g6, ((1, 3), (2, 2)): g7}
S = Setup(4, 2, 0, 8)
z = []
for key in S.var:
    z.append(vals.get(key, Fraction(0)))
missing = [k for k in vals if k not in S.vidx]
assert not missing, missing


def gam(p, q):
    if p == q:
        return S.kappa(p, q, exact=True)
    if (p, q) in S.vidx:
        return z[S.vidx[(p, q)]]
    if (q, p) in S.vidx:
        return 2 * S.kappa(p, q, exact=True) - z[S.vidx[(q, p)]]
    if q[1] not in S.live:
        return Fraction(0)
    return 2 * S.kappa(p, q, exact=True)


E = S.E
N = S.N
m = len(E)
Cp = [[None] * m for _ in range(m)]
for ii, i in enumerate(E):
    for jj, j in enumerate(E):
        coeffs = [Fraction(0)] * (N + 1)
        for a in range(N + 1):
            b = N - i - j - a
            if b < 0:
                continue
            coeffs[a] += gam((min(a, b), max(a, b)), (min(i, j), max(i, j)))   # s^a (x=1, y=s^2, root s)
        Cp[ii][jj] = flint.fmpq_poly([flint.fmpq(c.numerator, c.denominator) for c in coeffs])
ok_all = True
for par in (0, 1):
    bl = [t for t in range(m) if E[t] % 2 == par]
    assert all(Cp[i][j] == 0 for i in bl for j in range(m) if E[j] % 2 != par)
    mins = bareiss_minors([[Cp[i][j] for j in bl] for i in bl])
    for k, p in enumerate(mins):
        ok, inf = positive_on_open01(p)
        ok_all = ok_all and ok
        print(f"  block {'even' if par == 0 else 'odd'} minor {k + 1}: {ok} {inf}")
print("g1..g7 =", [str(g) for g in (g1, g2, g3, g4, g5, g6, g7)])
print("RESULT:", "PROVED" if ok_all else "FAILED")
if out and ok_all:
    json.dump(dict(n=4, qd=2, exponents_units=E, var=[[list(p), list(q)] for (p, q) in S.var],
                   z=[str(x) for x in z], zero_rows=[], minor_degrees=[]), open(out, "w"))
