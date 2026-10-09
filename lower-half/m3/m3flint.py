"""Exact polynomial pipeline (python-flint fmpq_mpoly) for the min-apex certificate, m = 3, general n.

Working variables X, Y with 1 < X < Y and s = X^e, t = Y^e (e = 1 if 3 | n, else e = 3).
  K(a,b,c) = h_n(a^e,b^e,c^e)/C(n+2,2) - (abc)^{n e/3}            (polynomial in the working variables)
  K1 = K(1,X,Y),  q1 = K(Y,1,1)/(Y-1)^2,  q2 = K(Y,X,X)/(Y-X)^2   (exact polynomial divisions)
  E = K1 - L r,   L = (Y-1)(Y-X),   r = sqrt(q1 q2) > 0.
An expression a + b r is stored as the pair (a, b).  Differentiation (r_X = r q2_X/(2 q2),
r_Y = r (q1_Y q2 + q1 q2_Y)/(2 q1 q2)) is done through the operators
  DX(a,b) := 2 q2 d/dX (a + b r)      = (2 q2 a_X, 2 q2 b_X + b q2_X)
  DY(a,b) := 2 q1 q2 d/dY (a + b r)   = (2 q1 q2 a_Y, 2 q1 q2 b_Y + b (q1_Y q2 + q1 q2_Y)),
and 4 q1 q2^2 E_XY = DY(DX E) - 2 q1 q2_Y DX E.
Weight w(b) = (b-1)^{g1} b^{g2}; mu(s) := g1 s + g2 (s-1), so w'/w = mu(s)/(s(s-1)).  With a_s = e X^{e-1}:
  C0 := E                                                                          (E >= 0)
  C1 := s(s-1) DX E - 2 q2 a_s mu(s) E           = 2 q2 s(s-1) a_s (F_s w(s)w(t))      (F_s >= 0)
  C2 := 2 q1 q2 a_t mu(t) E - t(t-1) DY E        = -2 q1 q2 t(t-1) a_t (F_t w w)        (F_t <= 0)
  C3 := -[ s(s-1)t(t-1)(DY DX E - 2 q1 q2_Y DX E) - 2 q1 q2 a_t mu(t) s(s-1) DX E
          - 2 q2 a_s mu(s) t(t-1) DY E + 4 q1 q2^2 a_s a_t mu(s) mu(t) E ]
                                                  = -4 q1 q2^2 s(s-1)t(t-1) a_s a_t (F_st w w)  (F_st <= 0)
All multipliers are positive on 1 < X < Y (q1, q2 > 0 there; checked separately)."""
import flint
from math import comb
from fractions import Fraction

CTX = flint.fmpq_mpoly_ctx.get(('X', 'Y'), 'lex')
X, Y = CTX.gens()
ONE = CTX.from_dict({(0, 0): 1})
CTXUV = flint.fmpq_mpoly_ctx.get(('u', 'v'), 'lex')
U, V = CTXUV.gens()


def q(x):
    return flint.fmpq(Fraction(x).numerator, Fraction(x).denominator)


def exact_div(a, b):
    qq, rr = divmod(a, b)
    assert rr == 0, "division not exact"
    return qq


def hcomplete(n, a, b, c):
    # h_n(a,b,c) = sum_{i+j+k=n} a^i b^j c^k
    hbc = []
    for j in range(n + 1):
        hbc.append(sum((b**i * c**(j - i) for i in range(j + 1)), 0 * ONE))
    return sum((a**i * hbc[n - i] for i in range(n + 1)), 0 * ONE)


def setup(n):
    e = 1 if n % 3 == 0 else 3
    Cn = comb(n + 2, 2)
    def K(a, b, c):
        if e == 1:
            return hcomplete(n, a, b, c) * q(Fraction(1, Cn)) - (a * b * c)**(n // 3)
        return hcomplete(n, a**3, b**3, c**3) * q(Fraction(1, Cn)) - (a * b * c)**n
    K1 = K(ONE, X, Y)
    q1 = exact_div(K(Y, ONE, ONE), (Y - 1)**2)
    q2 = exact_div(K(Y, X, X), (Y - X)**2)
    return dict(n=n, e=e, K1=K1, q1=q1, q2=q2, K=K)


def conditions(n, g1=Fraction(3, 2), g2=None):
    d = setup(n)
    if g2 is None:
        g2 = Fraction(n - 3, 2)
    e, K1, q1, q2 = d['e'], d['K1'], d['q1'], d['q2']
    q1Y, q2X, q2Y = q1.derivative('Y'), q2.derivative('X'), q2.derivative('Y')
    def DX(p):
        a, b = p
        return (2 * q2 * a.derivative('X'), 2 * q2 * b.derivative('X') + b * q2X)
    def DY(p):
        a, b = p
        return (2 * q1 * q2 * a.derivative('Y'), 2 * q1 * q2 * b.derivative('Y') + b * (q1Y * q2 + q1 * q2Y))
    def lin(*terms):  # sum of c * pair
        a = 0 * ONE; b = 0 * ONE
        for c, p in terms:
            a += c * p[0]; b += c * p[1]
        return (a, b)
    L = (Y - 1) * (Y - X)
    E = (K1, -L)
    s, t = X**e, Y**e
    a_s, a_t = e * X**(e - 1), e * Y**(e - 1)
    mu_s = q(g1) * s + q(g2) * (s - 1)
    mu_t = q(g1) * t + q(g2) * (t - 1)
    DXE, DYE = DX(E), DY(E)
    DYDXE = DY(DXE)
    C0 = E
    C1 = lin((s * (s - 1), DXE), (-2 * q2 * a_s * mu_s, E))
    C2 = lin((2 * q1 * q2 * a_t * mu_t, E), (-t * (t - 1), DYE))
    inner = lin((s * (s - 1) * t * (t - 1), DYDXE), (-s * (s - 1) * t * (t - 1) * 2 * q1 * q2Y, DXE),
                (-2 * q1 * q2 * a_t * mu_t * s * (s - 1), DXE), (-2 * q2 * a_s * mu_s * t * (t - 1), DYE),
                (4 * q1 * q2**2 * a_s * a_t * mu_s * mu_t, E))
    C3 = (-inner[0], -inner[1])
    return d, {'C0': C0, 'C1': C1, 'C2': C2, 'C3': C3}


def shift(p):
    """X = 1 + u, Y = 1 + u + v."""
    return p.compose(1 + U, 1 + U + V, ctx=CTXUV)


def shift_mult(p):
    """X = 1 + u, Y = (1 + u)(1 + v)."""
    return p.compose(1 + U, (1 + U) * (1 + V), ctx=CTXUV)


def neg_count(p):
    return sum(1 for c in p.coeffs() if c < 0)


def evalf(p, xv, yv):
    """exact rational evaluation"""
    return p.subs({'X': xv, 'Y': yv}) if False else p(q(xv), q(yv))
