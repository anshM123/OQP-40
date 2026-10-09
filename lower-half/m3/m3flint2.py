"""Exact polynomial pipeline, general weights (python-flint fmpq_mpoly), m = 3, general n.

Working variables X, Y with 1 < X < Y, s = X^e, t = Y^e (e = 1 if 3 | n, else 3).  Since s -> X is increasing,
F_s >= 0 <=> F_X >= 0, F_t <= 0 <=> F_Y <= 0 and F_st <= 0 <=> F_XY <= 0, so everything is done in X, Y.
  K1 = K(1,X,Y),  q1 = K(Y,1,1)/(Y-1)^2,  q2 = K(Y,X,X)/(Y-X)^2,  E = K1 - L r,  L = (Y-1)(Y-X),  r = sqrt(q1 q2).
Weight w(Z) = prod_i P_i(Z)^{gamma_i} (P_i > 0 on (1, inf)); its log-derivative is lambda = Nw/Dw with
  Dw = prod_i P_i,  Nw = sum_i gamma_i P_i' prod_{j != i} P_j   (polynomials in one variable).
Conditions (each multiplied by a positive factor; DX, DY as in m3flint):
  C0 := E                                                                       (F >= 0)
  C1 := Dw(X) DX E - 2 q2 Nw(X) E                    = 2 q2 Dw(X) w(X) w(Y) F_X       (F_X >= 0)
  C2 := 2 q1 q2 Nw(Y) E - Dw(Y) DY E                 = -2 q1 q2 Dw(Y) w w F_Y         (F_Y <= 0)
  C3 := -[ Dw(X)Dw(Y)(DY DX E - 2 q1 q2_Y DX E) - 2 q1 q2 Nw(Y) Dw(X) DX E - 2 q2 Nw(X) Dw(Y) DY E
          + 4 q1 q2^2 Nw(X) Nw(Y) E ]                = -4 q1 q2^2 Dw(X) Dw(Y) w w F_XY  (F_XY <= 0)
"""
import flint
from math import comb
from fractions import Fraction
from m3flint import CTX, X, Y, ONE, CTXUV, U, V, q, exact_div, hcomplete, setup, shift, shift_mult, neg_count


def weight_poly(spec, Z):
    """spec: list of (callable Z -> poly, gamma).  Returns (Nw(Z), Dw(Z))."""
    Ps = [(f(Z), q(g)) for f, g in spec]
    Dw = ONE
    for P, _ in Ps:
        Dw = Dw * P
    Nw = 0 * ONE
    var = 'X' if Z is X else 'Y'
    for i, (P, g) in enumerate(Ps):
        term = g * P.derivative(var)
        for j, (Pj, _) in enumerate(Ps):
            if j != i:
                term = term * Pj
        Nw = Nw + term
    return Nw, Dw


def std_weight(n, e, g1=Fraction(3, 2), g2=None):
    """w(b) = (b-1)^g1 b^g2 with b = Z^e."""
    if g2 is None:
        g2 = Fraction(n - 3, 2)
    return [(lambda Z: Z**e - 1, g1), (lambda Z: Z, e * g2)]


def diag_weight(n, d, g=Fraction(1, 2), extra=None):
    """w(b) = sqrt(K(1,b,b)) = (Z-1) * ptilde(Z)^{1/2}, ptilde(Z) = K(1,Z,Z)/(Z-1)^2 (working variables)."""
    K = d['K']
    def pt(Z):
        return exact_div(K(ONE, Z, Z), (Z - 1)**2)
    spec = [(lambda Z: Z - 1, Fraction(1)), (pt, g)]
    if extra:
        spec += extra
    return spec


def conditions(n, spec_fn=None, d=None):
    if d is None:
        d = setup(n)
    e, K1, q1, q2 = d['e'], d['K1'], d['q1'], d['q2']
    spec = spec_fn(n, d) if spec_fn else std_weight(n, e)
    NX, DXw = weight_poly(spec, X)
    NY, DYw = weight_poly(spec, Y)
    q1Y, q2X, q2Y = q1.derivative('Y'), q2.derivative('X'), q2.derivative('Y')
    def DX(p):
        a, b = p
        return (2 * q2 * a.derivative('X'), 2 * q2 * b.derivative('X') + b * q2X)
    def DY(p):
        a, b = p
        return (2 * q1 * q2 * a.derivative('Y'), 2 * q1 * q2 * b.derivative('Y') + b * (q1Y * q2 + q1 * q2Y))
    def lin(*terms):
        a = 0 * ONE; b = 0 * ONE
        for c, p in terms:
            a += c * p[0]; b += c * p[1]
        return (a, b)
    L = (Y - 1) * (Y - X)
    E = (K1, -L)
    DXE, DYE = DX(E), DY(E)
    DYDXE = DY(DXE)
    C1 = lin((DXw, DXE), (-2 * q2 * NX, E))
    C2 = lin((2 * q1 * q2 * NY, E), (-DYw, DYE))
    inner = lin((DXw * DYw, DYDXE), (-DXw * DYw * 2 * q1 * q2Y, DXE), (-2 * q1 * q2 * NY * DXw, DXE),
                (-2 * q2 * NX * DYw, DYE), (4 * q1 * q2**2 * NX * NY, E))
    C3 = (-inner[0], -inner[1])
    return d, {'C0': E, 'C1': C1, 'C2': C2, 'C3': C3}, (NX, DXw)
