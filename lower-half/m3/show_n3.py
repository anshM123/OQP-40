"""Display the n = 3 polynomials of verify_n.py (diag weight) in shifted variables u = s-1, v = t-s."""
import sys
from math import comb
import flint
n = 3
ctx = flint.fmpq_mpoly_ctx.get(('X', 'Y'), 'lex'); X, Y = ctx.gens(); one = ctx.from_dict({(0, 0): 1}); zero = 0 * one
cuv = flint.fmpq_mpoly_ctx.get(('u', 'v'), 'deglex'); u, v = cuv.gens()
def h(a, b, c):
    return sum((a**i * b**j * c**(n - i - j) for i in range(n + 1) for j in range(n + 1 - i)), zero)
def Kw(a, b, c): return h(a, b, c) * flint.fmpq(1, comb(n + 2, 2)) - a * b * c
def div(a, b):
    q, r = divmod(a, b); assert r == 0; return q
K1 = Kw(one, X, Y); q1 = div(Kw(Y, one, one), (Y - 1)**2); q2 = div(Kw(Y, X, X), (Y - X)**2)
ptX = div(Kw(one, X, X), (X - 1)**2); ptY = div(Kw(one, Y, Y), (Y - 1)**2)
NX, DXw = 2 * ptX + (X - 1) * ptX.derivative('X'), 2 * (X - 1) * ptX
NY, DYw = 2 * ptY + (Y - 1) * ptY.derivative('Y'), 2 * (Y - 1) * ptY
q1Y, q2X, q2Y = q1.derivative('Y'), q2.derivative('X'), q2.derivative('Y')
def DX(p): a, b = p; return (2 * q2 * a.derivative('X'), 2 * q2 * b.derivative('X') + b * q2X)
def DY(p): a, b = p; return (2 * q1 * q2 * a.derivative('Y'), 2 * q1 * q2 * b.derivative('Y') + b * (q1Y * q2 + q1 * q2Y))
def lin(*t):
    a, b = zero, zero
    for c, p in t: a += c * p[0]; b += c * p[1]
    return (a, b)
E = (K1, -(Y - 1) * (Y - X)); DXE, DYE = DX(E), DY(E); DYDXE = DY(DXE)
C = {'C0': E, 'C1': lin((DXw, DXE), (-2 * q2 * NX, E)), 'C2': lin((2 * q1 * q2 * NY, E), (-DYw, DYE))}
inner = lin((DXw * DYw, DYDXE), (-DXw * DYw * 2 * q1 * q2Y, DXE), (-2 * q1 * q2 * NY * DXw, DXE), (-2 * q2 * NX * DYw, DYE), (4 * q1 * q2**2 * NX * NY, E))
C['C3'] = (-inner[0], -inner[1])
sh = lambda p: p.compose(1 + u, 1 + u + v, ctx=cuv)
print("q1 =", sh(q1), "  q2 =", sh(q2), "  pt =", sh(ptX), " (shifted)")
for name, (al, be) in C.items():
    g = al.gcd(be); a2, b2 = div(al, g), div(be, g)
    D = a2 * a2 - b2 * b2 * q1 * q2
    gc, gf = g.factor()
    print(f"{name}: gcd = {g}")
    print(f"   alpha' = {sh(a2)}")
    print(f"   beta'  = {sh(b2)}")
    print(f"   Delta  = {sh(D)}")
