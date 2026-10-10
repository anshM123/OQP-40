"""Independent verifier, part 1: truncated Taylor jets in (x0, x1, x2) = (a, d, eps) with ball coefficients.

A jet stores c[m] = d^m g / m!  (multi-index m = (i, j, k)) for the monomials of a downward-closed set.
Arithmetic is exact truncated polynomial arithmetic on ball coefficients, so a jet evaluated with ball
variables encloses the true Taylor coefficients at every point of the ball.  Univariate functions are composed
through their Taylor coefficients, which must be enclosures valid at every point of the argument ball.
Written independently of tb_arb.py / tb_sx.py (different code, different precision: 200 bits).
"""
from math import comb, factorial
import flint
from flint import arb, fmpq, arb_series

flint.ctx.prec = 200
ZERO = arb(0)
ONE = arb(1)


class Space:
    def __init__(self, monos):
        self.monos = list(monos)
        assert self.monos[0] == (0, 0, 0)
        self.idx = {m: i for i, m in enumerate(self.monos)}
        self.n = len(self.monos)
        for m in self.monos:                       # downward closed
            for t in range(3):
                if m[t] > 0:
                    mm = list(m)
                    mm[t] -= 1
                    assert tuple(mm) in self.idx
        self.table = []
        for p, m1 in enumerate(self.monos):
            for q, m2 in enumerate(self.monos):
                s = (m1[0] + m2[0], m1[1] + m2[1], m1[2] + m2[2])
                if s in self.idx:
                    self.table.append((p, q, self.idx[s]))
        self.order = max(sum(m) for m in self.monos)


# total order <= 3 in (a, d), eps-order <= 1 with total order <= 3
SP3 = Space(sorted({(i, j, k) for k in (0, 1) for i in range(4) for j in range(4) if i + j + k <= 3},
                   key=lambda m: (sum(m), m)))


class Jet:
    __slots__ = ('c', 'sp')

    def __init__(self, c, sp):
        self.c = c
        self.sp = sp

    @staticmethod
    def const(v, sp):
        c = [ZERO] * sp.n
        c[0] = arb(v)
        return Jet(c, sp)

    @staticmethod
    def var(v, t, sp):
        c = [ZERO] * sp.n
        c[0] = arb(v)
        e = [0, 0, 0]
        e[t] = 1
        c[sp.idx[tuple(e)]] = ONE
        return Jet(c, sp)

    def __add__(x, y):
        if isinstance(y, Jet):
            return Jet([u + v for u, v in zip(x.c, y.c)], x.sp)
        c = list(x.c)
        c[0] = c[0] + y
        return Jet(c, x.sp)
    __radd__ = __add__

    def __neg__(x):
        return Jet([-u for u in x.c], x.sp)

    def __sub__(x, y):
        if isinstance(y, Jet):
            return Jet([u - v for u, v in zip(x.c, y.c)], x.sp)
        c = list(x.c)
        c[0] = c[0] - y
        return Jet(c, x.sp)

    def __rsub__(x, y):
        return (-x) + y

    def __mul__(x, y):
        if isinstance(y, Jet):
            out = [ZERO] * x.sp.n
            xc, yc = x.c, y.c
            for p, q, r in x.sp.table:
                out[r] += xc[p] * yc[q]
            return Jet(out, x.sp)
        return Jet([u * y for u in x.c], x.sp)
    __rmul__ = __mul__

    def __truediv__(x, y):
        if isinstance(y, Jet):
            return x * y.recip()
        return Jet([u / y for u in x.c], x.sp)

    def __rtruediv__(x, y):
        return x.recip() * y

    def compose(x, g):
        """g[k] = f^(k)(x0)/k! for k = 0..order, enclosures valid on the ball x0 = x.c[0]."""
        K = x.sp.order
        delta = Jet([ZERO] + x.c[1:], x.sp)
        res = Jet.const(g[K], x.sp)
        for k in range(K - 1, -1, -1):
            res = res * delta + g[k]
        return res

    def exp(x):
        return x.compose(c_exp(x.c[0], x.sp.order))

    def log(x):
        return x.compose(c_log(x.c[0], x.sp.order))

    def sqrt(x):
        return x.compose(c_sqrt(x.c[0], x.sp.order))

    def recip(x):
        return x.compose(c_recip(x.c[0], x.sp.order))

    def phi1(x):
        return x.compose(c_phi1(x.c[0], x.sp.order))

    def neglog1m(x):
        """-log(1 - x), accurate for tiny x."""
        return x.compose(c_neglog1m(x.c[0], x.sp.order))

    def phihat(x):
        import iv_phi
        return x.compose(iv_phi.c_phihat(x.c[0], x.sp.order))

    def phismall(x):
        import iv_small
        return x.compose(iv_small.c_phi_small(x.c[0], x.sp.order))

    def co(x, i, j, k=0):
        return x.c[x.sp.idx[(i, j, k)]]


class NotPos(Exception):
    pass


def _need_pos(x0, what):
    if not (x0 > 0):
        raise NotPos(what + ': ' + str(x0))


def c_exp(x0, K):
    e = x0.exp()
    return [e / factorial(k) for k in range(K + 1)]


def _mono_pow(x0, e):
    """enclosure of {x^e : x in x0} for a ball x0 not containing 0 and rational e (x^e is monotone on each
    half-line): hull of the values at the two (exact) endpoints.  Avoids the loose mid-radius powers of wide balls."""
    if x0.rad() == 0:
        if e.q == 1:
            v = x0 ** int(e.p) if e.p >= 0 else 1 / x0 ** int(-e.p)
            return v
        return x0 ** arb(e)
    lo, hi = arb(x0.lower()), arb(x0.upper())
    if e.q == 1:
        f = (lambda t: t ** int(e.p)) if e.p >= 0 else (lambda t: 1 / t ** int(-e.p))
    else:
        f = lambda t: t ** arb(e)
    return arb.union(f(lo), f(hi))


def c_log(x0, K):
    _need_pos(x0, 'log')
    out = [x0.log()]
    for k in range(1, K + 1):
        out.append(arb(fmpq((-1) ** (k + 1), k)) * _mono_pow(x0, fmpq(-k)))
    return out


def c_sqrt(x0, K):
    _need_pos(x0, 'sqrt')
    out = []
    for k in range(K + 1):
        bk = fmpq(1)
        for i in range(k):
            bk *= fmpq(1, 2) - i
        bk /= factorial(k)
        out.append(arb(bk) * (x0.sqrt() if k == 0 else _mono_pow(x0, fmpq(1, 2) - k)))
    return out


def c_recip(x0, K):
    if not (x0 > 0 or x0 < 0):
        raise NotPos('recip: ' + str(x0))
    return [((-1) ** k) * _mono_pow(x0, fmpq(-(k + 1))) for k in range(K + 1)]


def c_neglog1m(y0, K):
    """f(y) = -log(1 - y): f(y0) = -log1p(-y0) (accurate for tiny y0), f^(k)/k! = 1/(k (1-y0)^k)."""
    if not (y0 < 1):
        raise NotPos('neglog1m: ' + str(y0))
    w = 1 - y0
    out = [-((-y0).log1p())]
    for k in range(1, K + 1):
        out.append(_mono_pow(w, fmpq(-k)) / k)
    return out


_PHI_M = 40


def _phi1_thin(x, K):
    """phi1^(k)(x)/k!, k = 0..K, at a thin (or tiny) ball x: series for |x| <= 1/2, closed form otherwise."""
    h = abs(x).upper()
    if h <= 0.5:
        # c_k(x) = sum_{m>=k} C(m,k) x^(m-k)/(m+1)!;  tail m > M: <= h^(M+1-k) e^h/(k! (M+1-k)!)
        out = []
        for k in range(K + 1):
            s = ZERO
            p = ONE
            for m in range(k, _PHI_M + 1):
                s += comb(m, k) * p / factorial(m + 1)
                p = p * x
            tail = arb(h) ** (_PHI_M + 1 - k) * arb(h).exp() / (factorial(k) * factorial(_PHI_M + 1 - k))
            out.append(s + arb(0, tail.upper()))
        return out
    flint.ctx.cap = K + 1
    X = arb_series([x, 1], prec=K + 1)
    s = (X.exp() - 1) / X
    c = s.coeffs()
    return [c[k] if k < len(c) else ZERO for k in range(K + 1)]


def c_phi1(x0, K):
    """phi1(x) = (e^x - 1)/x; every phi1^(k)(x) = int_0^1 t^k e^{xt} dt is positive and increasing in x, so on a ball
    the coefficient enclosure is the hull of the values at the two endpoints."""
    if x0.rad() == 0:
        return _phi1_thin(x0, K)
    lo = _phi1_thin(arb(x0.lower()), K)
    hi = _phi1_thin(arb(x0.upper()), K)
    return [arb.union(u, v) for u, v in zip(lo, hi)]
