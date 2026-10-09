"""Standalone exact verification of Lemma 6(n): the min-apex kernel E_n is positive semidefinite on (1, inf).
Only python-flint and the standard library are used.  Usage: python verify_n.py n

Definitions (working variables X, Y; s = X^e, t = Y^e with e = 1 if 3 | n and e = 3 otherwise):
  Kw(a,b,c) = h_n(a^e,b^e,c^e)/C(n+2,2) - (abc)^{ne/3}             [= K_n(a^e,b^e,c^e), a polynomial]
  K1 = Kw(1,X,Y),  q1 = Kw(Y,1,1)/(Y-1)^2,  q2 = Kw(Y,X,X)/(Y-X)^2,  pt = Kw(1,X,X)/(X-1)^2   (exact divisions)
  E  = K1 - L r,  L = (Y-1)(Y-X),  r = sqrt(q1 q2)                     [E = E_n(s,t) for 1 < s < t]
  w(X) = (X-1) sqrt(pt(X)) = sqrt(K_n(1,s,s));  lambda = w'/w = Nw/Dw,  Nw = 2 pt + (X-1) pt',  Dw = 2 (X-1) pt.
Conditions as pairs (alpha, beta) meaning alpha + beta r:
  C0 = E;  C1 = Dw(X) DX E - 2 q2 Nw(X) E;  C2 = 2 q1 q2 Nw(Y) E - Dw(Y) DY E;
  C3 = -[Dw(X)Dw(Y)(DY DX E - 2 q1 q2_Y DX E) - 2 q1 q2 Nw(Y) Dw(X) DX E - 2 q2 Nw(X) Dw(Y) DY E
         + 4 q1 q2^2 Nw(X) Nw(Y) E],
  DX(a,b) = (2 q2 a_X, 2 q2 b_X + b q2_X),  DY(a,b) = (2 q1 q2 a_Y, 2 q1 q2 b_Y + b (q1_Y q2 + q1 q2_Y)).
  Then C0 = E, C1 = 2 q2 Dw(X) w w F_X, C2 = -2 q1 q2 Dw(Y) w w F_Y, C3 = -4 q1 q2^2 Dw(X) Dw(Y) w w F_XY,
  F = E/(w(X) w(Y)).
Proof obligations (shift X = 1+u, Y = 1+u+v, u, v > 0; "SP" = nonzero with all coefficients >= 0):
  (P0) q1, q2, pt, Dw(X) are SP, and q1, q2, pt are > 0 at X = Y = 1 (constant term after the shift), so
       q1, q2, pt > 0 on the closed region 1 <= X <= Y (regularity of F up to the diagonal);
  for each Ck = (alpha, beta), with g = gcd(alpha, beta) (content > 0, every irreducible factor SP),
  alpha' = alpha/g, beta' = beta/g, Delta = alpha'^2 - beta'^2 q1 q2:
  (P1) C0, C3: alpha' SP and Delta SP   =>  alpha' >= |beta'| r  =>  Ck >= 0;
  (P2) C1, C2: beta' SP and -Delta SP   =>  beta' r >= |alpha'|  =>  Ck >= 0."""
import sys, time, hashlib
from math import comb
from fractions import Fraction
import flint

n = int(sys.argv[1])
e = 1 if n % 3 == 0 else 3
ctx = flint.fmpq_mpoly_ctx.get(('X', 'Y'), 'lex')
X, Y = ctx.gens()
one = ctx.from_dict({(0, 0): 1}); zero = 0 * one
cuv = flint.fmpq_mpoly_ctx.get(('u', 'v'), 'lex')
u, v = cuv.gens()

def h(n, a, b, c):
    tot = zero
    for i in range(n + 1):
        for j in range(n + 1 - i):
            tot += a**i * b**j * c**(n - i - j)
    return tot

def Kw(a, b, c):
    inv = flint.fmpq(1, comb(n + 2, 2))
    if e == 1:
        return h(n, a, b, c) * inv - (a * b * c)**(n // 3)
    return h(n, a**3, b**3, c**3) * inv - (a * b * c)**n

def div(a, b):
    qq, rr = divmod(a, b)
    assert rr == 0
    return qq

def SP(p):
    """nonzero with all coefficients >= 0 after X = 1+u, Y = 1+u+v"""
    s = p.compose(1 + u, 1 + u + v, ctx=cuv)
    cs = s.coeffs()
    return (len(cs) > 0) and all(c >= 0 for c in cs), len(cs), (min(cs) if cs else None)

t0 = time.time()
K1 = Kw(one, X, Y)
q1 = div(Kw(Y, one, one), (Y - 1)**2)
q2 = div(Kw(Y, X, X), (Y - X)**2)
ptX = div(Kw(one, X, X), (X - 1)**2)
ptY = div(Kw(one, Y, Y), (Y - 1)**2)
NX, DXw = 2 * ptX + (X - 1) * ptX.derivative('X'), 2 * (X - 1) * ptX
NY, DYw = 2 * ptY + (Y - 1) * ptY.derivative('Y'), 2 * (Y - 1) * ptY
q1Y, q2X, q2Y = q1.derivative('Y'), q2.derivative('X'), q2.derivative('Y')
def DX(p):
    a, b = p
    return (2 * q2 * a.derivative('X'), 2 * q2 * b.derivative('X') + b * q2X)
def DY(p):
    a, b = p
    return (2 * q1 * q2 * a.derivative('Y'), 2 * q1 * q2 * b.derivative('Y') + b * (q1Y * q2 + q1 * q2Y))
def lin(*terms):
    a, b = zero, zero
    for c, p in terms:
        a += c * p[0]; b += c * p[1]
    return (a, b)
E = (K1, -(Y - 1) * (Y - X))
DXE, DYE = DX(E), DY(E)
DYDXE = DY(DXE)
C = {'C0': E,
     'C1': lin((DXw, DXE), (-2 * q2 * NX, E)),
     'C2': lin((2 * q1 * q2 * NY, E), (-DYw, DYE))}
inner = lin((DXw * DYw, DYDXE), (-DXw * DYw * 2 * q1 * q2Y, DXE), (-2 * q1 * q2 * NY * DXw, DXE),
            (-2 * q2 * NX * DYw, DYE), (4 * q1 * q2**2 * NX * NY, E))
C['C3'] = (-inner[0], -inner[1])
print(f"Lemma 6 verification, n = {n}, working variables {'s,t' if e == 1 else 'cube roots of s,t'}", flush=True)
ok = True
for name, p in [('q1', q1), ('q2', q2), ('pt', ptX), ('Dw', DXw)]:
    good, nt, mn = SP(p)
    c0 = p(flint.fmpq(1), flint.fmpq(1))   # = constant term after the shift
    if name != 'Dw':
        good = good and c0 > 0   # positive constant term: > 0 on the closed quadrant u, v >= 0
    ok &= good
    print(f"  (P0) {name}: degree {p.total_degree()}, shifted terms {nt}, value at X = Y = 1: {c0}, OK = {good}", flush=True)
q12 = q1 * q2
H = hashlib.sha256()
for name in ['C0', 'C1', 'C2', 'C3']:
    al, be = C[name]
    g = al.gcd(be)
    gc, gf = g.factor()
    gok = gc > 0 and all(SP(f)[0] for f, m in gf)
    al2, be2 = div(al, g), div(be, g)
    Delta = al2 * al2 - be2 * be2 * q12
    if name in ('C0', 'C3'):
        need = [("alpha'", al2), ('Delta', Delta)]
    else:
        need = [("beta'", be2), ('-Delta', -Delta)]
    line = f"  {name}: gcd factors (degree, mult) {[(f.total_degree(), m) for f, m in gf]} positive = {gok}"
    ok &= gok
    for k, p in need:
        good, nt, mn = SP(p)
        ok &= good
        H.update(str(p).encode())
        line += f";  {k}: degree {p.total_degree()}, {nt} shifted terms, all >= 0: {good}"
    print(line, flush=True)
print(f"RESULT n = {n}: {'ALL OBLIGATIONS VERIFIED' if ok else 'FAILED'}  (sha256 of proved polynomials "
      f"{H.hexdigest()[:16]}..., {time.time()-t0:.1f}s)", flush=True)
