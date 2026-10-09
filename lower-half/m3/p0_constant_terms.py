"""(P0) supplement: q1(1), q2(1,1), pt(1) for each n (exact), compared with the closed form n(n+3)/36 (3 | n) or
n(n+3)/4 (cube-root variables), which follows from K_n(1+eps) = (n(n+3)/24) sum_i (eps_i - mean eps)^2 + O(eps^3)."""
import sys
from math import comb
from fractions import Fraction
import flint
ctx = flint.fmpq_mpoly_ctx.get(('X', 'Y'), 'lex'); X, Y = ctx.gens(); one = ctx.from_dict({(0, 0): 1}); zero = 0 * one
ok_all = True
for n in [int(a) for a in sys.argv[1:]]:
    e = 1 if n % 3 == 0 else 3
    def h(a, b, c):
        return sum((a**i * b**j * c**(n - i - j) for i in range(n + 1) for j in range(n + 1 - i)), zero)
    def Kw(a, b, c):
        inv = flint.fmpq(1, comb(n + 2, 2))
        return h(a, b, c) * inv - (a * b * c)**(n // 3) if e == 1 else h(a**3, b**3, c**3) * inv - (a * b * c)**n
    def div(a, b):
        q, r = divmod(a, b); assert r == 0; return q
    q1 = div(Kw(Y, one, one), (Y - 1)**2); q2 = div(Kw(Y, X, X), (Y - X)**2); pt = div(Kw(one, X, X), (X - 1)**2)
    o = flint.fmpq(1)
    vals = (q1(o, o), q2(o, o), pt(o, o))
    closed = Fraction(n * (n + 3), 36 if e == 1 else 4)
    ok = all(v > 0 for v in vals) and all(Fraction(int(v.p), int(v.q)) == closed for v in vals)
    ok_all &= ok
    print(f"n = {n}: q1(1) = {vals[0]}, q2(1,1) = {vals[1]}, pt(1) = {vals[2]}; closed form {closed}; OK = {ok}", flush=True)
print("ALL OK" if ok_all else "FAILED")
