"""Rigorous (python-flint arb ball arithmetic) verification of three one-variable facts about the stationary limit
of the min-apex kernel (RESULTS.md, Theorem A, Corollary A1, Section 3):

    f(d) = 2 sinh(d/2)/d - sqrt(kappa(d)/2),   kappa(d) = 2(e^d - 1 - d)/d^2 - e^{d/3}   (d > 0),
    rr(d) = (2 sinh(d/2)/d - e^{-lam d}) / sqrt(kappa(d)/2),   lam = 7/100.

Claims checked on (0, DMAX] (DMAX = 60; the tail d >= 60 is the analytic argument in RESULTS.md):
  (V1) f'(d) < 0,   (V2) f''(d) > 0 and f''/f >= 1.34e-4,   (V3) rr(d) < 1, i.e. e^{lam d} f(d) < 1 (checked in this form for d >= 2, as rr < 1 on [0, 2]).
Method: adaptive bisection of (0, 60] (initial pieces of length 1/4). On [0, 2]: second-order jets in ball arithmetic.
On [2, 60]: the closed forms as arb power series (python-flint arb_series, length 4) and the centred form
g(d) in g(c) + g'(I)(d - c) for g = f, f', f'' and e^{lam d} f.  (V3) is checked as rr < 1 on [0, 2] and as
e^{lam d} f(d) < 1 on [2, 60] (equivalent, since sqrt(kappa/2) > 0).
On [0, 2] the removable singularities are handled by Taylor polynomials (degree 40) with rigorous remainders:
    2 sinh(d/2)/d = sum_k d^{2k}/(4^k (2k+1)!),  (d - 1 + e^{-d})/d^2 = sum_k (-1)^k d^k/(k+2)!,
    kappa(d)/d^2 = sum_k [2/(k+4)! - 1/(3^{k+2} (k+2)!)] d^k,   (1 - e^{-lam d})/d = sum_k (-1)^k lam^{k+1} d^k/(k+1)!,
and f = [(d-1+e^{-d})/d^2 + e^{d/3}/2] / [2 sinh(d/2)/d + d sqrt(kappa/(2 d^2))] (the cancellation-free form).
Usage: python verify_stationary.py   (prints the minimum certified bounds and ALL VERIFIED / FAILED)"""
import sys
from fractions import Fraction
from math import factorial
import flint
from flint import arb

flint.ctx.prec = 256
LAM = arb(7) / 100
D0 = arb(1) / 2
SERIES_MAX = 2.0     # Taylor-series branch on [0, 2] (the remainder bounds below hold for hi <= 2)
DMAX = 60
N_TAYLOR = 40


class J:
    """second-order jet: value, first and second derivative (arb balls)."""
    __slots__ = ('v', 'a', 'b')

    def __init__(self, v, a=0, b=0):
        self.v, self.a, self.b = arb(v), arb(a), arb(b)

    def __add__(s, o):
        o = o if isinstance(o, J) else J(o)
        return J(s.v + o.v, s.a + o.a, s.b + o.b)
    __radd__ = __add__

    def __sub__(s, o):
        o = o if isinstance(o, J) else J(o)
        return J(s.v - o.v, s.a - o.a, s.b - o.b)

    def __rsub__(s, o):
        return J(o) - s

    def __neg__(s):
        return J(-s.v, -s.a, -s.b)

    def __mul__(s, o):
        o = o if isinstance(o, J) else J(o)
        return J(s.v * o.v, s.a * o.v + s.v * o.a, s.b * o.v + 2 * s.a * o.a + s.v * o.b)
    __rmul__ = __mul__

    def __truediv__(s, o):
        o = o if isinstance(o, J) else J(o)
        q = s.v / o.v
        q1 = (s.a - q * o.a) / o.v
        q2 = (s.b - 2 * q1 * o.a - q * o.b) / o.v
        return J(q, q1, q2)

    def __rtruediv__(s, o):
        return J(o) / s


def jexp(u):
    e = u.v.exp()
    return J(e, e * u.a, e * (u.b + u.a * u.a))


def jsqrt(u):
    r = u.v.sqrt()
    r1 = u.a / (2 * r)
    return J(r, r1, (u.b - 2 * r1 * r1) / (2 * r))


def jsinh(u):
    sh, ch = u.v.sinh(), u.v.cosh()
    return J(sh, ch * u.a, sh * u.a * u.a + ch * u.b)


def series_jet(coef, lo, hi, tailfac):
    """Jet over d in [lo, hi] (0 <= lo < hi <= 2) of g(d) = sum_k coef(k) d^k, where |coef(k)| <= tailfac/k! for
    k > N_TAYLOR.  Derivatives m = 0,1,2: polynomial part by Horner on the ball, plus the remainder
    sum_{k>N} |coef k!/(k-m)!| hi^{k-m} <= tailfac * sum_{j>N-m} hi^j/j! <= tailfac * hi^{N-m+1}/(N-m+1)! * e^{hi}."""
    d = arb.union(arb(lo), arb(hi)) if lo != hi else arb(lo)
    out = []
    for m in range(3):
        acc = arb(0)
        for k in range(N_TAYLOR, m - 1, -1):
            c = coef(k) * (factorial(k) // factorial(k - m))
            acc = acc * d + arb(c.numerator) / c.denominator if isinstance(c, Fraction) else acc * d + c
        j = N_TAYLOR - m + 1
        rem = arb(tailfac) * arb(hi) ** j / factorial(j) * arb(hi).exp()
        acc = acc + arb(0, rem.upper())
        out.append(acc)
    return J(*out)


def c_A(k):     # 2 sinh(d/2)/d
    return Fraction(1, 4**(k // 2) * factorial(k + 1)) if k % 2 == 0 else Fraction(0)


def c_Bn(k):    # (d - 1 + e^{-d})/d^2
    return Fraction((-1)**k, factorial(k + 2))


def c_kh(k):    # kappa(d)/d^2
    return Fraction(2, factorial(k + 4)) - Fraction(1, 3**(k + 2) * factorial(k + 2))


def c_A1(k):    # (2 sinh(d/2)/d - 1)/d
    return Fraction(1, 4**((k + 1) // 2) * factorial(k + 2)) if k % 2 == 1 else Fraction(0)


def c_L(k):     # (1 - e^{-lam d})/d, lam = 7/100
    return Fraction((-1)**k * 7**(k + 1), 100**(k + 1) * factorial(k + 1))


def jets(lo, hi):
    """jets of f and rr over [lo, hi]."""
    if hi <= SERIES_MAX:
        d = J(arb.union(arb(lo), arb(hi)), 1, 0)
        A = series_jet(c_A, lo, hi, 1)
        Bn = series_jet(c_Bn, lo, hi, 1)
        kh = series_jet(c_kh, lo, hi, 3)
        A1 = series_jet(c_A1, lo, hi, 1)
        Lq = series_jet(c_L, lo, hi, 1)
        sq = jsqrt(kh / 2)                      # sqrt(kappa/(2 d^2))
        f = (Bn + jexp(d / 3) / 2) / (A + d * sq)
        rr = (A1 + Lq) / sq                      # rr itself on [0, 2] (rr < 0.95 there, no tightness)
        return f, rr
    d = J(arb.union(arb(lo), arb(hi)), 1, 0)
    A = 2 * jsinh(d / 2) / d
    kap = 2 * (jexp(d) - 1 - d) / (d * d) - jexp(d / 3)
    sk = jsqrt(kap / 2)
    num = (d - 1 + jexp(-d)) / (d * d) + jexp(d / 3) / 2
    f = num / (A + sk)
    rr = (A - jexp(-LAM * d)) / sk
    return f, rr


from flint import arb_series


def closed_series(d0, L=4):
    """Taylor series (length L) at the ball d0 of f and rr from the closed forms (d0 > 0)."""
    flint.ctx.cap = L
    x = arb_series([d0, 1], prec=L)
    ex, emx = x.exp(), (-x).exp()
    A = ((x / 2).exp() - (-(x / 2)).exp()) / x          # 2 sinh(d/2)/d
    kap = 2 * (ex - 1 - x) / (x * x) - (x / 3).exp()
    sk = (kap / 2).sqrt()
    num = (x - 1 + emx) / (x * x) + (x / 3).exp() / 2
    f = num / (A + sk)
    rr = (LAM * x).exp() * f                 # V3 as e^{lam d} f(d) < 1  (equivalent to rr < 1)
    return f, rr


def coeffs(s, L=4):
    c = s.coeffs()
    return [c[k] if k < len(c) else arb(0) for k in range(L)]


def check_closed(lo, hi):
    """centered form: value/derivatives at the centre plus higher derivative over the interval times radius."""
    c = (lo + hi) / 2
    r = (hi - lo) / 2
    fc, rrc = closed_series(arb(c))
    fI, rrI = closed_series(arb.union(arb(lo), arb(hi)))
    fc, rrc, fI, rrI = coeffs(fc), coeffs(rrc), coeffs(fI), coeffs(rrI)
    R = arb(0, r)
    fv = fc[0] + fI[1] * R
    f1 = fc[1] + 2 * fI[2] * R
    f2 = 2 * fc[2] + 6 * fI[3] * R
    rv = rrc[0] + rrI[1] * R
    ok1 = f1 < 0
    ok2 = (f2 > 0) and (f2 / fv > arb('1.34e-4'))
    ok3 = rv < 1                               # e^{lam d} f(d) < 1  <=>  rr(d) < 1; rr > 0 since f < 2sinh(d/2)/d - ...
    return ok1 and ok2 and ok3, J(fv, f1, f2), J(rv)


def check(lo, hi):
    if hi <= SERIES_MAX:
        f, rr = jets(lo, hi)
        ok1 = f.a < 0
        ok2 = (f.b > 0) and (f.b / f.v > arb('1.34e-4'))
        ok3 = (rr.v > 0) and (rr.v < 1)
        return ok1 and ok2 and ok3, f, rr
    try:
        return check_closed(lo, hi)
    except ValueError:      # a ball containing 0 in a denominator or a square root: refine
        return False, J(arb(0, 1), arb(0, 1), arb(0, 1)), J(arb(0, 1))


def main():
    stack = [(Fraction(k, 4), Fraction(k + 1, 4)) for k in range(0, 4 * DMAX)]
    stack.reverse()
    n_ok = 0
    mins = {'-f1/f': None, 'f2/f': None, '1 - (rr on [0,2], e^{lam d} f on [2,60])': None}
    while stack:
        lo, hi = stack.pop()
        good, f, rr = check(float(lo) if lo else 0.0, float(hi))
        if good:
            n_ok += 1
            for key, val in (('-f1/f', -f.a / f.v), ('f2/f', f.b / f.v), ('1 - (rr on [0,2], e^{lam d} f on [2,60])', 1 - rr.v)):
                lb = val.lower()
                if mins[key] is None or lb < mins[key][0]:
                    mins[key] = (lb, float(lo), float(hi))
            continue
        if hi - lo < Fraction(1, 2**22):
            print(f"FAILED on [{float(lo)}, {float(hi)}]: f'={f.a}, f''/f={f.b / f.v}, rr={rr.v}")
            print("RESULT: FAILED")
            return 1
        mid = (lo + hi) / 2
        stack.append((mid, hi))
        stack.append((lo, mid))
    print(f"intervals: {n_ok}")
    for key, (lb, lo, hi) in mins.items():
        print(f"  certified min of {key} on (0, {DMAX}]: >= {float(lb):.6e}  (attained on [{lo}, {hi}])")
    print("RESULT: ALL VERIFIED  (V1) f' < 0, (V2) f''/f >= 1.34e-4, (V3) rr < 1 (= e^{lam d} f < 1) on (0, 60]")
    return 0


if __name__ == '__main__':
    sys.exit(main())
