"""Theorem B: verified ball arithmetic (python-flint arb) for the Gaussian-design certificate.

Truncated bivariate Taylor jets in the scaled variables (a, b) (b = a + d), with eps = 1/n a ball parameter.
A jet stores the Taylor coefficients c_{ij} = d_a^i d_b^j g / (i! j!) for the monomials of a fixed downward-closed
set.  Univariate functions are applied by composition with their Taylor coefficients, which are computed with arb
power series (arb_series) or with explicit series plus rigorous tail bounds.  Every arithmetic operation is a ball
operation, so every printed enclosure is rigorous.  The formulas are those of tb_formulas_mp.py (see there).
"""
from math import factorial, comb
import flint
from flint import arb, arb_series, fmpq

PREC = 160
flint.ctx.prec = PREC
ZERO = arb(0)
ONE = arb(1)
LAM = arb(7) / 100
ETA = arb(7) / 10


class Mode:
    def __init__(self, monos):
        self.monos = monos
        self.idx = {m: i for i, m in enumerate(monos)}
        self.n = len(monos)
        self.table = []
        for i, m1 in enumerate(monos):
            for j, m2 in enumerate(monos):
                m = (m1[0] + m2[0], m1[1] + m2[1], m1[2] + m2[2])
                if m in self.idx:
                    self.table.append((i, j, self.idx[m]))
        self.maxdeg = max(sum(m) for m in monos)
        self.has_eps = any(m[2] for m in monos)


_AB2 = [(0, 0), (1, 0), (0, 1), (1, 1)]
_AB3 = _AB2 + [(2, 0), (0, 2), (2, 1), (1, 2)]
MP = Mode([(i, j, 0) for (i, j) in _AB2])                                    # centre, eps a thin ball
MB = Mode([(i, j, 0) for (i, j) in _AB3])                                    # box, eps a ball constant
MBE = Mode([(i, j, 0) for (i, j) in _AB3] + [(i, j, 1) for (i, j) in _AB2])  # box, eps a jet variable


class NotPositive(ValueError):
    pass


class J:
    __slots__ = ('c', 'm')

    def __init__(self, c, m):
        self.c = c
        self.m = m

    @staticmethod
    def const(v, m):
        c = [ZERO] * m.n
        c[0] = arb(v)
        return J(c, m)

    @staticmethod
    def var(v, k, m):
        """the jet of the k-th coordinate (k = 0: a, 1: b, 2: eps) at the ball v."""
        c = [ZERO] * m.n
        c[0] = arb(v)
        c[m.idx[((1, 0, 0), (0, 1, 0), (0, 0, 1))[k]]] = ONE
        return J(c, m)

    def __add__(s, o):
        if isinstance(o, J):
            return J([x + y for x, y in zip(s.c, o.c)], s.m)
        c = list(s.c)
        c[0] = c[0] + o
        return J(c, s.m)
    __radd__ = __add__

    def __neg__(s):
        return J([-x for x in s.c], s.m)

    def __sub__(s, o):
        if isinstance(o, J):
            return J([x - y for x, y in zip(s.c, o.c)], s.m)
        c = list(s.c)
        c[0] = c[0] - o
        return J(c, s.m)

    def __rsub__(s, o):
        return (-s) + o

    def __mul__(s, o):
        if isinstance(o, J):
            out = [ZERO] * s.m.n
            a, b = s.c, o.c
            for i, j, k in s.m.table:
                out[k] = out[k] + a[i] * b[j]
            return J(out, s.m)
        return J([x * o for x in s.c], s.m)
    __rmul__ = __mul__

    def __truediv__(s, o):
        if isinstance(o, J):
            return s * o.recip()
        return J([x / o for x in s.c], s.m)

    def __rtruediv__(s, o):
        return s.recip() * o

    def compose(s, g):
        """g = [g_0, ..., g_K] Taylor coefficients of a univariate function at the constant term of s."""
        K = s.m.maxdeg
        d = J([ZERO] + s.c[1:], s.m)
        res = J.const(g[K], s.m)
        for k in range(K - 1, -1, -1):
            res = res * d + g[k]
        return res

    def exp(s):
        return s.compose(g_exp(s.c[0], s.m.maxdeg))

    def expm1(s):
        return s.compose(g_expm1(s.c[0], s.m.maxdeg))

    def log(s):
        return s.compose(g_log(s.c[0], s.m.maxdeg))

    def sqrt(s):
        return s.compose(g_sqrt(s.c[0], s.m.maxdeg))

    def recip(s):
        return s.compose(g_recip(s.c[0], s.m.maxdeg))

    def phi1(s):
        return s.compose(g_phi1(s.c[0], s.m.maxdeg))

    def coef(s, i, j, k=0):
        return s.c[s.m.idx[(i, j, k)]]


def _pos(x):
    if not (x > 0):
        raise NotPositive(str(x))


def g_exp(x0, K):
    e = x0.exp()
    return [e / factorial(k) for k in range(K + 1)]


def g_expm1(x0, K):
    e = x0.exp()
    return [x0.expm1()] + [e / factorial(k) for k in range(1, K + 1)]


def g_log(x0, K):
    _pos(x0)
    out = [x0.log()]
    p = ONE
    for k in range(1, K + 1):
        p = p / x0
        out.append(p * ((-1) ** (k + 1)) / k)
    return out


def g_sqrt(x0, K):
    _pos(x0)
    r = x0.sqrt()
    out = []
    p = r
    for k in range(K + 1):
        # binom(1/2, k) as an exact rational
        num, den = 1, 1
        for i in range(k):
            num *= (1 - 2 * i)
            den *= 2 * (i + 1)
        out.append(p * num / den)
        p = p / x0
    return out


def g_recip(x0, K):
    if not (x0 > 0 or x0 < 0):
        raise NotPositive('recip of ' + str(x0))
    out = []
    p = 1 / x0
    for k in range(K + 1):
        out.append(p if k % 2 == 0 else -p)
        p = p / x0
    return out


def taylor_from_series(coefs, x0, K, tailfn):
    """Taylor coefficients (orders 0..K) at the ball x0 of g(x) = sum_{k<=N} coefs[k] x^k + tail, with
    |m-th Taylor coefficient of the tail at x0| <= tailfn(m)."""
    flint.ctx.cap = K + 1
    X = arb_series([x0, 1], prec=K + 1)
    acc = arb_series([coefs[-1]], prec=K + 1)
    for k in range(len(coefs) - 2, -1, -1):
        acc = acc * X + coefs[k]
    c = acc.coeffs()
    c = [c[k] if k < len(c) else ZERO for k in range(K + 1)]
    return [c[m] + arb(0, tailfn(m)) for m in range(K + 1)]


N_PHI1 = 40
PHI1_COEF = [arb(fmpq(1, factorial(k + 1))) for k in range(N_PHI1 + 1)]


def g_phi1(x0, K):
    """phi1(x) = (e^x - 1)/x.  Every derivative phi1^(k)(x) = int_0^1 t^k e^{xt} dt is positive and increasing, so
    for a wide ball the coefficient enclosures are the hulls of the values at the two endpoints."""
    if x0.rad() > 1e-6:
        lo = g_phi1_thin(arb(x0.lower()), K)
        hi = g_phi1_thin(arb(x0.upper()), K)
        return [arb.union(p, q) for p, q in zip(lo, hi)]
    return g_phi1_thin(x0, K)


def g_phi1_thin(x0, K):
    h = abs(x0).upper()
    if h <= 1:
        # tail: sum_{k>N} C(k,m) h^{k-m}/(k+1)! <= (1/m!) h^{N+1-m} e^h/(N+1-m)!
        tail = lambda m: arb(h) ** (N_PHI1 + 1 - m) * arb(h).exp() / (factorial(m) * factorial(N_PHI1 + 1 - m))
        return taylor_from_series(PHI1_COEF, x0, K, lambda m: tail(m).upper())
    if not (x0 > 0 or x0 < 0):
        raise NotPositive('phi1 closed form needs x0 != 0')
    flint.ctx.cap = K + 1
    X = arb_series([x0, 1], prec=K + 1)
    s = (X.exp() - 1) / X
    c = s.coeffs()
    return [c[k] if k < len(c) else ZERO for k in range(K + 1)]


# ---------------- kappa_n(x)/x^2 as a series with eps-dependent coefficients ----------------
N_KAP = 60


def _stirling2(N):
    S = [[0] * (N + 1) for _ in range(N + 1)]
    S[0][0] = 1
    for k in range(1, N + 1):
        for r in range(1, k + 1):
            S[k][r] = r * S[k - 1][r] + S[k - 1][r - 1]
    return S


_S2 = _stirling2(N_KAP)
_mu_cache = {}


def mu_coeffs(eps):
    """mu_k(eps) = E[(eps J)^k] - 3^{-k}, k = 0..N_KAP, where P(J = j) = (n+1-j)/C(n+2,2), j = 0..n, n = 1/eps:
    E[(eps J)^k] = sum_r S2(k,r) 2/((r+1)(r+2)) eps^{k-r} prod_{i<r} (1 - i eps)   (exact for eps = 1/n and eps = 0)."""
    key = (eps.mid().str(30), eps.rad().str(5))
    if key in _mu_cache:
        return _mu_cache[key]
    prods = [ONE]
    for i in range(N_KAP):
        prods.append(prods[-1] * (1 - i * eps))
    epow = [ONE]
    for i in range(N_KAP):
        epow.append(epow[-1] * eps)
    out = []
    for k in range(N_KAP + 1):
        s = ZERO
        for r in range(0, k + 1):
            if _S2[k][r]:
                s += _S2[k][r] * arb(fmpq(2, (r + 1) * (r + 2))) * epow[k - r] * prods[r]
        out.append(s - arb(fmpq(1, 3 ** k)))
    _mu_cache[key] = out
    return out


def g_skap(x0, K, eps):
    """Taylor coefficients at x0 of S(x) = kappa_n(x)/x^2 = sum_{k>=2} mu_k x^{k-2}/k!  (entire in x).
    Tail (|mu_k| <= 1 for eps = 1/n or 0): (1/m!) h^{N-1-m} e^h/(N-1-m)!."""
    mu = mu_coeffs(eps)
    coefs = [mu[k] / factorial(k) for k in range(2, N_KAP + 1)]
    h = abs(x0).upper()
    tail = lambda m: (arb(h) ** (N_KAP - 1 - m) * arb(h).exp() / (factorial(m) * factorial(N_KAP - 1 - m))).upper()
    return taylor_from_series(coefs, x0, K, tail)


# ---------------- the design function Phi ----------------
N_PHI = 100
C_A = [arb(fmpq(1, 4 ** (k // 2) * factorial(k + 1))) if k % 2 == 0 else ZERO for k in range(N_PHI + 1)]
C_A1 = [arb(fmpq(1, 4 ** ((k + 1) // 2) * factorial(k + 2))) if k % 2 == 1 else ZERO for k in range(N_PHI + 1)]
C_KH = [arb(fmpq(2, factorial(k + 4)) - fmpq(1, 3 ** (k + 2) * factorial(k + 2))) for k in range(N_PHI + 1)]
C_L = [arb(fmpq((-1) ** k * 7 ** (k + 1), 100 ** (k + 1) * factorial(k + 1))) for k in range(N_PHI + 1)]


def _tail_fact(h, tailfac, m, N):
    # |c_k| <= tailfac/k! for k > N:  sum_{k>N} C(k,m) |c_k| h^{k-m} <= tailfac/m! * h^{N+1-m} e^h /(N+1-m)!
    return (arb(tailfac) * arb(h) ** (N + 1 - m) * arb(h).exp() / (factorial(m) * factorial(N + 1 - m))).upper()


def _ser(x0, K):
    flint.ctx.cap = K + 1
    return arb_series([x0, 1], prec=K + 1)


def _coeffs(s, K):
    c = s.coeffs()
    return [c[k] if k < len(c) else ZERO for k in range(K + 1)]


def _as_series(lst, K):
    flint.ctx.cap = K + 1
    return arb_series(lst, prec=K + 1)


def g_Phi_raw(z0, K):
    """Taylor coefficients of Phi(z) = -sqrt(-log(1 - eta (1 - rr(z)))) at the ball z0 >= 0."""
    if z0.upper() <= 2:
        h = abs(z0).upper()
        A1 = _as_series(taylor_from_series(C_A1, z0, K, lambda m: _tail_fact(h, 1, m, N_PHI)), K)
        Lq = _as_series(taylor_from_series(C_L, z0, K, lambda m: _tail_fact(h, 1, m, N_PHI)), K)
        kh = _as_series(taylor_from_series(C_KH, z0, K, lambda m: _tail_fact(h, 3, m, N_PHI)), K)
        rr = (A1 + Lq) / (kh / 2).sqrt()
        y = ETA * (1 - rr)
    else:
        if not (z0 > 0):
            raise NotPositive('Phi')
        x = _ser(z0, K)
        # scaled closed forms (no growing exponentials): with G = 1 - (1+z)e^{-z} - (z^2/2)e^{-2z/3},
        # 2 sinh(z/2)/z = (e^{z/2}/z)(1 - e^{-z}), sqrt(kappa/2) = (e^{z/2}/z) sqrt(G),
        # f_inf = [(z - 1 + e^{-z}) e^{-z/2}/z + (z/2) e^{-z/6}] / (1 - e^{-z} + sqrt(G)),
        # eta (1 - rr) = eta z e^{-z/2} (e^{-lam z} - f_inf)/sqrt(G).
        em = (-x).exp()
        G = 1 - (1 + x) * em - (x * x / 2) * (-(2 * x / 3)).exp()
        sqG = G.sqrt()
        finf = ((x - 1 + em) * (-(x / 2)).exp() / x + (x / 2) * (-(x / 6)).exp()) / (1 - em + sqG)
        y = ETA * x * (-(x / 2)).exp() * ((-LAM * x).exp() - finf) / sqG
    yc = _coeffs(y, K)
    _pos(yc[0])
    Y = max(abs(t).upper() for t in yc)
    if Y < 1e-20:
        # -log(1 - y) = y + y^2/2 + y^3/3 + sum_{j>=4} y^j/j (for tiny y).  If every z-Taylor coefficient of y (orders 0..K<=3)
        # is <= Y in modulus, the order-m coefficient of y^j is <= Y^j C(m+j-1, j-1) <= Y^j (j+2)^3/6, so the
        # order-m coefficient of the remainder is <= sum_{j>=4} Y^j (j+2)^3/(6j) <= 10 Y^4.
        Lg = y + y * y / 2 + y * y * y / 3
        bound = 10 * arb(Y) ** 4
        L = _as_series([t + arb(0, bound.upper()) for t in _coeffs(Lg, K)], K)
    else:
        if not (yc[0] < 1):
            raise NotPositive('Phi: y >= 1')
        L = -((1 - y).log())
    Lc0 = _coeffs(L, K)
    _pos(Lc0[0])
    P = -(L.sqrt())
    return _coeffs(P, K)


# ---------------- assembly ----------------
class Ctx:
    """eps-dependent constants for one eps ball."""

    def __init__(self, eps):
        self.eps = eps
        self.e1 = 1 + eps
        self.e2 = 1 + 2 * eps
        self.c = 2 / self.e1
        self.cp = 2 / (self.e1 * self.e2)
        self.sqcp = self.cp.sqrt()


def nu_of(z, cx):
    """nu(z) = eps/(1 - e^{-z eps}) = 1/(z phi1(-z eps))."""
    return 1 / (z * (-(z * cx.eps)).phi1())


PHI_CELL = 32          # cells [k/32, (k+1)/32] for z >= 2
_phi_cache = {}


def _union_lists(lists):
    out = list(lists[0])
    for l in lists[1:]:
        out = [arb.union(x, y) for x, y in zip(out, l)]
    return out


def g_Phi(z0, K):
    if z0.rad() < 1e-12:
        return g_Phi_raw(z0, K)
    """Taylor coefficients of Phi at every point of the ball z0 (enclosures): on [0, 2] directly (series branch),
    on [2, inf) as the union of the enclosures on the cells [k/32, (k+1)/32] that meet z0 (each cell evaluated
    once and cached), so that wide balls do not lose the relative accuracy of the exponential factors."""
    lo, hi = z0.lower(), z0.upper()
    parts = []
    if lo < 2:
        parts.append(g_Phi_raw(arb.union(lo, min(hi, arb(2))) if hi > lo else z0, K))
    if hi >= 2:
        from math import floor
        k0 = int(floor(float(max(lo, arb(2)).lower()) * PHI_CELL))
        k1 = int(floor(float(hi) * PHI_CELL))
        for k in range(max(k0, 2 * PHI_CELL), k1 + 1):
            key = (k, K)
            if key not in _phi_cache:
                cell = arb.union(arb(fmpq(k, PHI_CELL)), arb(fmpq(k + 1, PHI_CELL)))
                _phi_cache[key] = g_Phi_raw(cell, K)
            parts.append(_phi_cache[key])
    return _union_lists(parts)


def Phi_of(z):
    return z.compose(g_Phi(z.c[0], z.m.maxdeg))


def skap_of(x, cx):
    return x.compose(g_skap(x.c[0], x.m.maxdeg, cx.eps))


def logF_nu(A, B, cx):
    """log F in the nu-form (for a >= ~3 and d >= ~3)."""
    eps, e1, e2 = cx.eps, cx.e1, cx.e2
    Dd = B - A
    na, nb, nd = nu_of(A, cx), nu_of(B, cx), nu_of(Dd, cx)
    pb = (-(B * e2)).exp() + e2 * (-(B * e1)).exp() / nb
    pd = (-(Dd * e2)).exp() + e2 * (-(Dd * e1)).exp() / nd
    yb = (-(B / 3)).exp() / (nb * cx.sqcp)
    yd = (-(Dd / 3)).exp() / (nd * cx.sqcp)
    gb = 1 - pb - yb * yb
    gd = 1 - pd - yd * yd
    ea2 = (-(A * e2)).exp()
    oma = 1 - na * (1 - ea2) / e2 - (-(A / 3)).exp() / (cx.c * na)
    omb = 1 - nb * (1 - (-(B * e2)).exp()) / e2 - (-(B / 3)).exp() / (cx.c * nb)
    u1 = (-(Dd * e2)).exp()
    u2 = (1 - ea2) * (na / nd) * (-(Dd * e1)).exp()
    u12 = u1 + u2
    ybd = yb * yd
    kh = 1 - u12 - ybd
    N = (yb - yd) * (yb - yd) + (pb + pd - 2 * u12) + u12 * u12 + 2 * u12 * ybd - pb * pd - pb * yd * yd - pd * yb * yb
    sg = gb.sqrt() * gd.sqrt()
    x = Phi_of(B) - Phi_of(Dd)
    one_m_R = -((-(x * x)).expm1())
    D = N / (kh + sg) + sg * one_m_R
    return (Dd / 2 + nd.log() + (nb.log() - na.log()) / 2 + D.log() - (oma.log() + omb.log()) / 2
            - e2.log())


def logF_mixed(A, B, cx):
    """log F in the mixed form (for a >= ~3 and small d):
    F = sqrt(nu_b/nu_a) Bm / sqrt(om_a om_b),
    Bm = e^{-d(1/2+eps)} [P(d) - nu_a (1 - e^{-a(1+2eps)})/(1+2eps)] - e^{-a/3} e^{-d/6}/(c nu_b) - sqrt(c' gam_b)/c * d sqrt(S(d)) R."""
    eps, e1, e2 = cx.eps, cx.e1, cx.e2
    Dd = B - A
    na, nb = nu_of(A, cx), nu_of(B, cx)
    pb = (-(B * e2)).exp() + e2 * (-(B * e1)).exp() / nb
    yb = (-(B / 3)).exp() / (nb * cx.sqcp)
    gb = 1 - pb - yb * yb
    ea2 = (-(A * e2)).exp()
    oma = 1 - na * (1 - ea2) / e2 - (-(A / 3)).exp() / (cx.c * na)
    omb = 1 - nb * (1 - (-(B * e2)).exp()) / e2 - (-(B / 3)).exp() / (cx.c * nb)
    Pd = (Dd * e2).phi1() / (Dd * eps).phi1()
    x = Phi_of(B) - Phi_of(Dd)
    R = (-(x * x)).exp()
    Sd = skap_of(Dd, cx)
    Bm = ((-(Dd * (arb(1) / 2 + eps))).exp() * (Pd - na * (1 - ea2) / e2)
          - (-(A / 3)).exp() * (-(Dd / 6)).exp() / (cx.c * nb)
          - (cx.cp * gb).sqrt() / cx.c * Dd * Sd.sqrt() * R)
    return (nb.log() - na.log()) / 2 + Bm.log() - (oma.log() + omb.log()) / 2


def margins_from_logF(G):
    """(L1, L2, L3) and, for the box modes, their gradients ((d_a, d_b) or (d_a, d_b, d_eps)) from the jet G of log F:
    L1 = (log F)_a, L2 = -(log F)_b, L3 = -F_ab/F = L1 L2 - (log F)_ab."""
    L1 = G.coef(1, 0)
    L2 = -G.coef(0, 1)
    c11 = G.coef(1, 1)
    L3 = L1 * L2 - c11
    if G.m is MP:
        return (L1, L2, L3), None
    c20, c02, c21, c12 = G.coef(2, 0), G.coef(0, 2), G.coef(2, 1), G.coef(1, 2)
    dL1 = [2 * c20, c11]
    dL2 = [-c11, -2 * c02]
    dL3 = [dL1[0] * L2 + L1 * dL2[0] - 2 * c21, dL1[1] * L2 + L1 * dL2[1] - 2 * c12]
    if G.m.has_eps:
        e1, e2, e3 = G.coef(1, 0, 1), -G.coef(0, 1, 1), None
        e3 = e1 * L2 + L1 * e2 - G.coef(1, 1, 1)
        dL1.append(e1)
        dL2.append(e2)
        dL3.append(e3)
    return (L1, L2, L3), (dL1, dL2, dL3)


# ---------------- scaled design function Phihat(z) = Phi(z) e^{mu z}, mu = (1/2 + lam)/2 ----------------
MU = (arb(1) / 2 + LAM) / 2


def g_Phihat_raw(z0, K):
    """Taylor coefficients of Phihat(z) = -sqrt(Lg(z) e^{(1/2+lam) z}), Lg = -log(1 - y), y = eta (1 - rr(z)).
    For z >= 2: y e^{(1/2+lam) z} = eta z (1 - q)/sqrt(G), q = e^{lam z} f_inf(z) (scaled, moderate), and
    Lg e^{(1/2+lam) z} = ell(y) * y e^{(1/2+lam) z} with ell(y) = -log(1-y)/y."""
    if z0.upper() <= PHI_SERIES_MAX:
        h = abs(z0).upper()
        A1 = _as_series(taylor_from_series(C_A1, z0, K, lambda m: _tail_fact(h, 1, m, N_PHI)), K)
        Lq = _as_series(taylor_from_series(C_L, z0, K, lambda m: _tail_fact(h, 1, m, N_PHI)), K)
        kh = _as_series(taylor_from_series(C_KH, z0, K, lambda m: _tail_fact(h, 3, m, N_PHI)), K)
        rr = (A1 + Lq) / (kh / 2).sqrt()
        y = ETA * (1 - rr)
        x = _ser(z0, K)
        yc = _coeffs(y, K)
        _pos(yc[0])
        if not (yc[0] < 1):
            raise NotPositive('Phihat: y >= 1')
        L = -((1 - y).log()) * ((2 * MU) * x).exp()
    else:
        if not (z0 > 0):
            raise NotPositive('Phihat')
        x = _ser(z0, K)
        em = (-x).exp()
        G = 1 - (1 + x) * em - (x * x / 2) * (-(2 * x / 3)).exp()
        sqG = G.sqrt()
        q = (((x - 1 + em) * (-((arb(1) / 2 - LAM) * x)).exp() / x + (x / 2) * (-((arb(1) / 6 - LAM) * x)).exp())
             / (1 - em + sqG))
        ys = ETA * x * (1 - q) / sqG                     # y e^{(1/2+lam) z}
        y = ys * (-((2 * MU) * x)).exp()
        yc = _coeffs(y, K)
        _pos(yc[0])
        Y = max(abs(t).upper() for t in yc)
        if Y < 1e-20:
            # ell(y) = 1 + y/2 + y^2/3 + sum_{j>=3} y^j/(j+1); remainder coefficients <= sum_{j>=3} Y^j (j+2)^3/(6(j+1)) <= 4 Y^3
            el = 1 + y / 2 + y * y / 3
            bound = 4 * arb(Y) ** 3
            el = _as_series([t + arb(0, bound.upper()) for t in _coeffs(el, K)], K)
        else:
            if not (yc[0] < 1):
                raise NotPositive('Phihat: y >= 1')
            el = -((1 - y).log()) / y
        L = el * ys
    Lc = _coeffs(L, K)
    _pos(Lc[0])
    return _coeffs(-(L.sqrt()), K)


_phihat_cache = {}
PHI_SERIES_MAX = 2
PHI_W = 128           # cells [k/128, (k+1)/128]
PHI_TOL = 2e-4        # cells are bisected until every coefficient enclosure has radius <= PHI_TOL (or width 2^-14)


def _phihat_cell(lo, hi, K):
    """enclosures over [lo, hi] (fmpq) of the Taylor coefficients of order 0..K of Phihat, by the centred form
    c_k([lo,hi]) in c_k(mid) + (k+1) c_{k+1}([lo,hi]) [-r, r]; cells are bisected if the naive evaluation fails."""
    mid = (lo + hi) / 2
    r = (hi - lo) / 2
    try:
        naive = g_Phihat_raw(arb.union(arb(lo), arb(hi)), K + 1)
    except (NotPositive, ValueError):
        if hi - lo < fmpq(1, 2 ** 16):
            raise
        a = _phihat_cell(lo, mid, K)
        b = _phihat_cell(mid, hi, K)
        return [arb.union(x, y) for x, y in zip(a, b)]
    cm = g_Phihat_raw(arb(mid), K)
    R = arb(0, arb(r))
    out = [cm[k] + (k + 1) * naive[k + 1] * R for k in range(K + 1)]
    if max(float(x.rad()) for x in out) > PHI_TOL and hi - lo >= fmpq(1, 2 ** 14):
        a = _phihat_cell(lo, mid, K)
        b = _phihat_cell(mid, hi, K)
        return [arb.union(x, y) for x, y in zip(a, b)]
    return out


def g_Phihat(z0, K):
    """enclosures of the Taylor coefficients of Phihat at all points of z0 (thin balls directly; otherwise the
    union over the cached cells [k/128, (k+1)/128] that meet z0)."""
    if z0.rad() < 1e-12:
        return g_Phihat_raw(z0, K)
    from math import floor
    lo, hi = z0.lower(), z0.upper()
    if lo < 0 and lo > -1e-6:
        lo = arb(0)              # the argument is a distance d >= 0 (boxes have d_lo >= 0); unions of balls may stick out below 0 by ~1e-11
    k0 = int(floor(float(lo) * PHI_W))
    k1 = int(floor(float(hi) * PHI_W))
    if k0 < 0:
        raise NotPositive('Phihat at negative z')
    parts = []
    for k in range(k0, k1 + 1):
        key = (k, K)
        if key not in _phihat_cache:
            _phihat_cache[key] = _phihat_cell(fmpq(k, PHI_W), fmpq(k + 1, PHI_W), K)
        parts.append(_phihat_cache[key])
    return _union_lists(parts)


def Phihat_of(z):
    return z.compose(g_Phihat(z.c[0], z.m.maxdeg))


def logF_nu2(A, B, cx, Dd=None):
    """log F in the scaled nu-form (a >= ~3, d >= ~3); no growing or decaying exponential is left unnormalised:
    log F = -lam d + log nu_d + (log nu_b - log nu_a)/2 - log(1+2eps) - (log om_a + log om_b)/2 + log Dhat,
    Dhat = e^{-(1/6 - lam) d} Ntil/(khat + sg) + sg (Phihat_b e^{-mu a} - Phihat_d)^2 psi(x),
    x = e^{-(1/2+lam) d} (Phihat_b e^{-mu a} - Phihat_d)^2, psi(x) = (1 - e^{-x})/x = phi1(-x),
    Ntil = e^{2d/3} N (see tb_formulas_mp.py for N), with yh_z = 1/(nu_z sqrt(c')), ph_z = e^{-2 z eps} + (1+2eps) e^{-z eps}/nu_z,
    uh1 = e^{-2 d eps}, uh2 = (1 - e^{-a(1+2eps)}) (nu_a/nu_d) e^{-d eps}."""
    eps, e1, e2 = cx.eps, cx.e1, cx.e2
    Dd = B - A if Dd is None else Dd
    na, nb, nd = nu_of(A, cx), nu_of(B, cx), nu_of(Dd, cx)
    ema, emb, emd = (-A).exp(), (-B).exp(), (-Dd).exp()
    ema3, emd3 = (-(A / 3)).exp(), (-(Dd / 3)).exp()
    yhb, yhd = 1 / (nb * cx.sqcp), 1 / (nd * cx.sqcp)
    phb = (-(2 * eps) * B).exp() + e2 * (-eps * B).exp() / nb
    phd = (-(2 * eps) * Dd).exp() + e2 * (-eps * Dd).exp() / nd
    uh1 = (-(2 * eps) * Dd).exp()
    ea2 = (-(A * e2)).exp()
    uh2 = (1 - ea2) * (na / nd) * (-eps * Dd).exp()
    uh = uh1 + uh2
    emd43 = emd * emd3
    Nt = ((yhb * ema3 - yhd) * (yhb * ema3 - yhd) + emd3 * (phb * ema + phd - 2 * uh) + emd43 * uh * uh
          + 2 * emd * ema3 * uh * yhb * yhd - phb * phd * ema * emd43 - phb * yhd * yhd * ema * emd
          - phd * yhb * yhb * ema3 * ema3 * emd)
    gb = 1 - phb * emb - yhb * yhb * (-(2 * B / 3)).exp()
    gd = 1 - phd * emd - yhd * yhd * emd3 * emd3
    kh = 1 - emd * uh - yhb * yhd * ema3 * emd3 * emd3
    sg = gb.sqrt() * gd.sqrt()
    dif = Phihat_of(B) * (-MU * A).exp() - Phihat_of(Dd)
    dif2 = dif * dif
    xx = dif2 * (-((2 * MU) * Dd)).exp()
    psi = (-xx).phi1()
    Dh = (-((arb(1) / 6 - LAM) * Dd)).exp() * Nt / (kh + sg) + sg * dif2 * psi
    oma = 1 - na * (1 - ea2) / e2 - ema3 / (cx.c * na)
    omb = 1 - nb * (1 - (-(B * e2)).exp()) / e2 - (-(B / 3)).exp() / (cx.c * nb)
    return (-LAM * Dd + nd.log() + (nb.log() - na.log()) / 2 - e2.log() - (oma.log() + omb.log()) / 2 + Dh.log())


def logF_mixed2(A, B, cx):
    """mixed form with Phi = Phihat e^{-mu z} (for small d, a >= ~3)."""
    eps, e1, e2 = cx.eps, cx.e1, cx.e2
    Dd = B - A
    na, nb = nu_of(A, cx), nu_of(B, cx)
    pb = (-(B * e2)).exp() + e2 * (-(B * e1)).exp() / nb
    yb = (-(B / 3)).exp() / (nb * cx.sqcp)
    gb = 1 - pb - yb * yb
    ea2 = (-(A * e2)).exp()
    oma = 1 - na * (1 - ea2) / e2 - (-(A / 3)).exp() / (cx.c * na)
    omb = 1 - nb * (1 - (-(B * e2)).exp()) / e2 - (-(B / 3)).exp() / (cx.c * nb)
    Pd = (Dd * e2).phi1() / (Dd * eps).phi1()
    x = Phihat_of(B) * (-MU * B).exp() - Phihat_of(Dd) * (-MU * Dd).exp()
    R = (-(x * x)).exp()
    Sd = skap_of(Dd, cx)
    Bm = ((-(Dd * (arb(1) / 2 + eps))).exp() * (Pd - na * (1 - ea2) / e2)
          - (-(A / 3)).exp() * (-(Dd / 6)).exp() / (cx.c * nb)
          - (cx.cp * gb).sqrt() / cx.c * Dd * Sd.sqrt() * R)
    return (nb.log() - na.log()) / 2 + Bm.log() - (oma.log() + omb.log()) / 2


# ---------------- S(x; eps) = kappa_n(x)/x^2 with explicit eps-polynomial coefficients ----------------
# kappa_n(x) = K_n(e^{x eps}, 1, 1) = 2 Psi(x; eps) Bq(x eps) - e^{x/3}, where
#   Psi(x; eps) = [x eps, x(1+2eps)] phi1 = sum_i psi_i x^i,  psi_i = h_i(eps, 1+2eps)/(i+2)!,
#   h_i(u, v) = sum_{l=0}^i u^l v^{i-l},  Bq(z) = 1/phi1(z)^2 = (z/(e^z-1))^2 = sum_j beta_j z^j (exact rationals),
# so S(x; eps) = sum_{k>=2} s_k x^{k-2},  s_k = 2 sum_{i+j=k} psi_i beta_j eps^j - 1/(3^k k!)  (s_0 = s_1 = 0).
# (This is the closed form of tb_formulas_mp: kappa = c (P - 1)/Q - e^{x/3}, rewritten with a divided difference.)
# Bounds used for the tails (0 <= eps <= 1/37, v = 1 + 2 eps <= 39/37): |beta_j| <= 13 (Cauchy on |z| = 1, where
# |phi1(z)| >= 1 - (e - 2)), |psi_i| <= v^i/(i+1)!, |psi_i'| <= 2 v^i/i!.
N_S = 60
EPS_MAX = fmpq(1, 37)


def _beta_exact(N):
    p = [fmpq(1, factorial(k + 1)) for k in range(N + 1)]
    q = [fmpq(0)] * (N + 1)
    q[0] = fmpq(1)
    for k in range(1, N + 1):
        s = fmpq(0)
        for i in range(1, k + 1):
            s += p[i] * q[k - i]
        q[k] = -s
    return [sum((q[i] * q[k - i] for i in range(k + 1)), fmpq(0)) for k in range(N + 1)]


BETA = _beta_exact(N_S)
BETA_ARB = [arb(b) for b in BETA]
_s_cache = {}


def s_coeffs(eps):
    """[s_k(eps)] and [s_k'(eps)] for k = 0..N_S (balls), eps a ball in [0, 1/37].  For a wide ball the values are
    enclosed by the centred form s_k(eps) in s_k(mid) + s_k'(ball) [-r, r] (s_k' is enclosed directly)."""
    if eps.rad() > 1e-30:
        key = ('w', eps.mid().str(30), eps.rad().str(5))
        if key in _s_cache:
            return _s_cache[key]
        sm, _ = s_coeffs_raw(arb(eps.mid()))
        _, spb = s_coeffs_raw(eps)
        r = arb(0, eps.rad())
        res = ([x + y * r for x, y in zip(sm, spb)], spb)
        _s_cache[key] = res
        return res
    return s_coeffs_raw(eps)


def s_coeffs_raw(eps):
    key = (eps.mid().str(30), eps.rad().str(5))
    if key in _s_cache:
        return _s_cache[key]
    v = 1 + 2 * eps
    h = [ONE]
    hp = [ZERO]
    epow = [ONE]
    for i in range(1, N_S + 1):
        epow.append(epow[-1] * eps)
    for i in range(1, N_S + 1):
        h.append(v * h[i - 1] + epow[i])
        hp.append(2 * h[i - 1] + v * hp[i - 1] + i * epow[i - 1])
    psi = [h[i] / factorial(i + 2) for i in range(N_S + 1)]
    psip = [hp[i] / factorial(i + 2) for i in range(N_S + 1)]
    s, sp = [ZERO, ZERO], [ZERO, ZERO]
    for k in range(2, N_S + 1):
        acc, accp = ZERO, ZERO
        for i in range(k + 1):
            j = k - i
            acc += psi[i] * BETA_ARB[j] * epow[j]
            accp += psip[i] * BETA_ARB[j] * epow[j]
            if j >= 1:
                accp += psi[i] * BETA_ARB[j] * j * epow[j - 1]
        s.append(2 * acc - arb(fmpq(1, 3 ** k * factorial(k))))
        sp.append(2 * accp)
    _s_cache[key] = (s, sp)
    return s, sp


_stail_cache = {}


def s_tails(hq):
    """upper bounds, for m = 0..6, of sum_{k>N_S} T_k C(k-2, m) h^{k-2-m} and of the same with T'_k (h = hq/8)."""
    if hq in _stail_cache:
        return _stail_cache[hq]
    h = arb(fmpq(hq, 8))
    e = arb(EPS_MAX)
    v = 1 + 2 * e
    out, outp = [ZERO] * 7, [ZERO] * 7
    for k in range(N_S + 1, 401):
        T = ZERO
        Tp = ZERO
        for i in range(k + 1):
            T += v ** i * e ** (k - i) / factorial(i + 1)
            Tp += 2 * v ** i * e ** (k - i) / factorial(i)
            if k - i >= 1:
                Tp += v ** i / factorial(i + 1) * (k - i) * e ** (k - i - 1)
        T = 26 * T + arb(fmpq(1, 3 ** k * factorial(k)))
        Tp = 26 * Tp
        for m in range(7):
            if k - 2 - m >= 0:
                w = comb(k - 2, m) * h ** (k - 2 - m)
                out[m] += T * w
                outp[m] += Tp * w
    # k > 400: T_k <= 26 (v/37)^k e^37/37 + 1/(3^k k!), T'_k <= 26 (k+2) 37 (v/37)^k e^37; with h <= 8 the terms
    # times C(k-2,m) h^{k-2-m} decrease geometrically (ratio < 0.24), so the rest is < 1e-200.
    res = ([float(x.upper()) + 1e-200 for x in out], [float(x.upper()) + 1e-200 for x in outp])
    _stail_cache[hq] = res
    return res


def g_S_raw(x0, eps, K):
    from math import ceil
    h = abs(x0).upper()
    if h > 8:
        raise NotPositive('S series used beyond |x| <= 8')
    hq = int(ceil(float(h) * 8 + 1e-9))
    s, sp = s_coeffs(eps)
    tl, tlp = s_tails(hq)
    S = taylor_from_series(s[2:], x0, K, lambda m: tl[m])
    Sp = taylor_from_series(sp[2:], x0, K, lambda m: tlp[m])
    return S, Sp


def g_S(x0, eps, K):
    """Taylor coefficients (orders 0..K <= 5) at the ball x0 (|x0| <= 8) of S(x; eps) and of d_eps S(x; eps); for wide
    balls by the centred form c_m(ball) in c_m(mid) + (m+1) c_{m+1}(ball) [-r, r]."""
    if x0.rad() < 1e-10:
        return g_S_raw(x0, eps, K)
    mid = arb(x0.mid())
    r = arb(0, x0.rad())
    Sm, Spm = g_S_raw(mid, eps, K)
    Sb, Spb = g_S_raw(x0, eps, K + 1)
    return ([Sm[m] + (m + 1) * Sb[m + 1] * r for m in range(K + 1)],
            [Spm[m] + (m + 1) * Spb[m + 1] * r for m in range(K + 1)])


def S_of(X, cx):
    """the jet of S(x; eps) at the jet X (x = d or x = -a)."""
    if isinstance(cx.eps, J):
        S, Sp = g_S(X.c[0], cx.eps.c[0], X.m.maxdeg)
        dE = J([ZERO] + cx.eps.c[1:], X.m)
        return X.compose(S) + dE * X.compose(Sp)
    S, _ = g_S(X.c[0], cx.eps, X.m.maxdeg)
    return X.compose(S)


def logF_mixed3(A, B, cx, Dd=None):
    """mixed form (small d, a >= ~3) with S from the explicit series (works with eps a jet)."""
    eps, e1, e2 = cx.eps, cx.e1, cx.e2
    Dd = B - A if Dd is None else Dd
    na, nb = nu_of(A, cx), nu_of(B, cx)
    pb = (-(B * e2)).exp() + e2 * (-(B * e1)).exp() / nb
    yb = (-(B / 3)).exp() / (nb * cx.sqcp)
    gb = 1 - pb - yb * yb
    ea2 = (-(A * e2)).exp()
    oma = 1 - na * (1 - ea2) / e2 - (-(A / 3)).exp() / (cx.c * na)
    omb = 1 - nb * (1 - (-(B * e2)).exp()) / e2 - (-(B / 3)).exp() / (cx.c * nb)
    Pd = (Dd * e2).phi1() / (Dd * eps).phi1()
    x = Phihat_of(B) * (-MU * B).exp() - Phihat_of(Dd) * (-MU * Dd).exp()
    R = (-(x * x)).exp()
    Sd = S_of(Dd, cx)
    Bm = ((-(Dd * (arb(1) / 2 + eps))).exp() * (Pd - na * (1 - ea2) / e2)
          - (-(A / 3)).exp() * (-(Dd / 6)).exp() / (cx.c * nb)
          - (cx.cp * gb).sqrt() / cx.c * Dd * Sd.sqrt() * R)
    return (nb.log() - na.log()) / 2 + Bm.log() - (oma.log() + omb.log()) / 2


# ---------------- version 4: no small-argument cancellations in om_a, om_b, gam_b, gam_d ----------------
# nu_z om_z = W(z) e^{-z}/c = z^2 S(-z)/c,   c' gam_z = kappa(z) e^{-z}/nu_z^2 = z^4 phi1(-z eps)^2 S(z) e^{-z}   (S series, |z| <= 8)
SMALL = 2.5


def _small(Z):
    z0 = Z.bj.c[0] if hasattr(Z, 'bj') else Z.c[0]
    return z0.upper() <= SMALL


def apart(A, cx):
    """-(log nu_a + log om_a)/2."""
    if _small(A):
        return -A.log() - T_S(-A, cx).log() / 2 + cx.c.log() / 2 if not isinstance(cx.c, J) else \
            -A.log() - T_S(-A, cx).log() / 2 + cx.c.log() / 2
    na = nu_of(A, cx)
    oma = 1 - na * (1 - (-(A * cx.e2)).exp()) / cx.e2 - (-(A / 3)).exp() / (cx.c * na)
    return -(na.log() + oma.log()) / 2


def bpart(B, cx):
    """(log nu_b - log om_b)/2."""
    nb = nu_of(B, cx)
    if _small(B):
        return nb.log() - B.log() - T_S(-B, cx).log() / 2 + cx.c.log() / 2
    omb = 1 - nb * (1 - (-(B * cx.e2)).exp()) / cx.e2 - (-(B / 3)).exp() / (cx.c * nb)
    return (nb.log() - omb.log()) / 2


def T_S(X, cx):
    return S_of(X, cx)


def cpgam(Z, cx):
    """c' gam_z."""
    if _small(Z):
        p = (-(Z * cx.eps)).phi1()
        Z2 = Z * Z
        return Z2 * Z2 * p * p * T_S(Z, cx) * (-Z).exp()
    nz = nu_of(Z, cx)
    pz = (-(Z * cx.e2)).exp() + cx.e2 * (-(Z * cx.e1)).exp() / nz
    yz = (-(Z / 3)).exp() / (nz * cx.sqcp)
    return cx.cp * (1 - pz - yz * yz)


def qa_of(A, cx):
    """nu_a (1 - e^{-a(1+2eps)})/(1+2eps) = phi1(-a(1+2eps))/phi1(-a eps)."""
    return (-(A * cx.e2)).phi1() / (-(A * cx.eps)).phi1()


def logF_nu4(A, B, cx, Dd=None):
    """d in [~3, ~8]: log F = d/2 + log nu_d + apart + bpart - log(1+2eps) + log D, D = khat - R sqrt(gam_b gam_d)."""
    eps, e1, e2 = cx.eps, cx.e1, cx.e2
    Dd = B - A if Dd is None else Dd
    nb, nd = nu_of(B, cx), nu_of(Dd, cx)
    yb = (-(B / 3)).exp() / (nb * cx.sqcp)
    yd = (-(Dd / 3)).exp() / (nd * cx.sqcp)
    u1 = (-(Dd * e2)).exp()
    u2 = e2 * qa_of(A, cx) * (-(Dd * e1)).exp() / nd
    kh = 1 - u1 - u2 - yb * yd
    sg = (cpgam(B, cx) * cpgam(Dd, cx)).sqrt() / cx.cp
    x = Phihat_of(B) * (-MU * B).exp() - Phihat_of(Dd) * (-MU * Dd).exp()
    R = (-(x * x)).exp()
    D = kh - R * sg
    return Dd / 2 + nd.log() + apart(A, cx) + bpart(B, cx) - e2.log() + D.log()


def logF_nu5(A, B, cx, Dd=None):
    """d >= ~8: scaled perfect-square form (as logF_nu2) with apart/bpart."""
    eps, e1, e2 = cx.eps, cx.e1, cx.e2
    Dd = B - A if Dd is None else Dd
    nb, nd = nu_of(B, cx), nu_of(Dd, cx)
    ema, emb, emd = (-A).exp(), (-B).exp(), (-Dd).exp()
    ema3, emd3 = (-(A / 3)).exp(), (-(Dd / 3)).exp()
    yhb, yhd = 1 / (nb * cx.sqcp), 1 / (nd * cx.sqcp)
    phb = (-(2 * eps) * B).exp() + e2 * (-eps * B).exp() / nb
    phd = (-(2 * eps) * Dd).exp() + e2 * (-eps * Dd).exp() / nd
    uh1 = (-(2 * eps) * Dd).exp()
    uh2 = e2 * qa_of(A, cx) * (-eps * Dd).exp() / nd
    uh = uh1 + uh2
    emd43 = emd * emd3
    Nt = ((yhb * ema3 - yhd) * (yhb * ema3 - yhd) + emd3 * (phb * ema + phd - 2 * uh) + emd43 * uh * uh
          + 2 * emd * ema3 * uh * yhb * yhd - phb * phd * ema * emd43 - phb * yhd * yhd * ema * emd
          - phd * yhb * yhb * ema3 * ema3 * emd)
    gb = cpgam(B, cx) / cx.cp
    gd = 1 - phd * emd - yhd * yhd * emd3 * emd3
    kh = 1 - emd * uh - yhb * yhd * ema3 * emd3 * emd3
    sg = gb.sqrt() * gd.sqrt()
    dif = Phihat_of(B) * (-MU * A).exp() - Phihat_of(Dd)
    dif2 = dif * dif
    xx = dif2 * (-((2 * MU) * Dd)).exp()
    psi = (-xx).phi1()
    Dh = (-((arb(1) / 6 - LAM) * Dd)).exp() * Nt / (kh + sg) + sg * dif2 * psi
    return -LAM * Dd + nd.log() + apart(A, cx) + bpart(B, cx) - e2.log() + Dh.log()


def logF_mixed5(A, B, cx, Dd=None):
    """d <= ~3: log F = apart + bpart + log Bm."""
    eps, e1, e2 = cx.eps, cx.e1, cx.e2
    Dd = B - A if Dd is None else Dd
    nb = nu_of(B, cx)
    Pd = (Dd * e2).phi1() / (Dd * eps).phi1()
    x = Phihat_of(B) * (-MU * B).exp() - Phihat_of(Dd) * (-MU * Dd).exp()
    R = (-(x * x)).exp()
    Sd = S_of(Dd, cx)
    Bm = ((-(Dd * (arb(1) / 2 + eps))).exp() * (Pd - qa_of(A, cx))
          - (-(A / 3)).exp() * (-(Dd / 6)).exp() / (cx.c * nb)
          - cpgam(B, cx).sqrt() / cx.c * Dd * Sd.sqrt() * R)
    return apart(A, cx) + bpart(B, cx) + Bm.log()


def dvar(v, m):
    """the jet of d = b - a at the ball v (its constant term is the d-ball itself, not b-ball minus a-ball)."""
    c = [ZERO] * m.n
    c[0] = arb(v)
    c[m.idx[(1, 0, 0)]] = -ONE
    c[m.idx[(0, 1, 0)]] = ONE
    return J(c, m)


# ---------------- dual jets: centre jet + box jet, with jet-level centred forms ("tightening") ----------------
# Every intermediate quantity Q is carried as (Q at the thin centre c, Q over the box), both as jets of mode MT.  Before a
# univariate function is applied, each Taylor coefficient Q_m of the box jet is replaced by the (valid) enclosure
#   Q_m(c) + (m_a+1) Q_{m+e_a}(box) ... ,  precisely  Q_m(c) + [(d_a + d_b) Q_m](box) [-r_a, r_a] + [d_b Q_m](box) [-r_d, r_d]
#   + [d_eps Q_m](box) [-r_e, r_e],   with d_a Q_m = (m_a + 1) Q_{m + e_a} etc.,
# intersected with the naive enclosure (mean value theorem on the convex box {a = a_c + x, b = b_c + x + y, eps = eps_c + z}).
MT = Mode([(i, j, 0) for i in range(4) for j in range(4) if i + j <= 4] +
          [(i, j, 1) for i in range(3) for j in range(3) if i + j <= 3])
# with second-order eps terms, so that the eps-coefficients are tightened as well (used by dual_box from 00:20 on)
MT2 = Mode(list(MT.monos) + [(i, j, 2) for i in range(3) for j in range(3) if i + j <= 2])
DUAL_MODE = MT2
TIGHT = {'r': (ZERO, ZERO, ZERO)}
TIGHT_PRODUCTS = True       # also tighten the box part of every product of dual jets


def _tight_plan(m):
    plan = []
    for idx, (i, j, k) in enumerate(m.monos):
        ia, ib, ie = m.idx.get((i + 1, j, k)), m.idx.get((i, j + 1, k)), m.idx.get((i, j, k + 1))
        if ia is None or ib is None:
            continue
        plan.append((idx, ia, i + 1, ib, j + 1, ie, k + 1))
    return plan


_PLAN = {}


def tighten(bj, cj):
    ra, rd, re = TIGHT['r']
    m = bj.m
    if m not in _PLAN:
        _PLAN[m] = _tight_plan(m)
    out = list(bj.c)
    for (idx, ia, fa, ib, fb, ie, fe) in _PLAN[m]:
        if ie is None and re.rad() > 0:
            continue
        db = fb * bj.c[ib]
        t = cj.c[idx] + (fa * bj.c[ia] + db) * ra + db * rd
        if ie is not None:
            t = t + fe * bj.c[ie] * re
        try:
            out[idx] = t.intersection(out[idx])
        except ValueError:
            out[idx] = t
    return J(out, m)


class DJ:
    __slots__ = ('cj', 'bj')

    def __init__(self, cj, bj):
        self.cj = cj
        self.bj = bj

    def __add__(s, o):
        if isinstance(o, DJ):
            return DJ(s.cj + o.cj, s.bj + o.bj)
        return DJ(s.cj + o, s.bj + o)
    __radd__ = __add__

    def __neg__(s):
        return DJ(-s.cj, -s.bj)

    def __sub__(s, o):
        if isinstance(o, DJ):
            return DJ(s.cj - o.cj, s.bj - o.bj)
        return DJ(s.cj - o, s.bj - o)

    def __rsub__(s, o):
        return (-s) + o

    def __mul__(s, o):
        if isinstance(o, DJ):
            c = s.cj * o.cj
            b = s.bj * o.bj
            return DJ(c, tighten(b, c) if TIGHT_PRODUCTS else b)
        return DJ(s.cj * o, s.bj * o)
    __rmul__ = __mul__

    def __truediv__(s, o):
        if isinstance(o, DJ):
            return s * o.recip()
        return DJ(s.cj / o, s.bj / o)

    def __rtruediv__(s, o):
        return s.recip() * o

    def _u(s, name):
        return DJ(getattr(s.cj, name)(), getattr(tighten(s.bj, s.cj), name)())

    def exp(s):
        return s._u('exp')

    def expm1(s):
        return s._u('expm1')

    def log(s):
        return s._u('log')

    def sqrt(s):
        return s._u('sqrt')

    def recip(s):
        return s._u('recip')

    def phi1(s):
        return s._u('phi1')


class DCtx:
    """eps-dependent constants for dual jets (centre eps thin, box eps a ball, both jet variables)."""

    def __init__(self, Ec, Eb):
        self.eps = DJ(Ec, Eb)
        self.cc = Ctx(Ec)
        self.cb = Ctx(Eb)
        self.e1 = 1 + self.eps
        self.e2 = 1 + 2 * self.eps
        self.c = 2 / self.e1
        self.cp = 2 / (self.e1 * self.e2)
        self.sqcp = self.cp.sqrt()


_Phihat_of_J = Phihat_of
_S_of_J = S_of


def Phihat_of(z):
    if isinstance(z, DJ):
        return DJ(_Phihat_of_J(z.cj), _Phihat_of_J(tighten(z.bj, z.cj)))
    return _Phihat_of_J(z)


def S_of(X, cx):
    if isinstance(X, DJ):
        return DJ(_S_of_J(X.cj, cx.cc), _S_of_J(tighten(X.bj, X.cj), cx.cb))
    return _S_of_J(X, cx)


def T_S(X, cx):
    return S_of(X, cx)


def dual_box(form, a0, a1, d0, d1, e0, e1):
    """centre values (L1, L2, L3) and box gradients ((d_a, d_b, d_eps) for each) of the conditions, with tightening."""
    from flint import fmpq as _q
    A_ = lambda x: arb(_q(x.numerator, x.denominator))
    ac, dc, ec = (a0 + a1) / 2, (d0 + d1) / 2, (e0 + e1) / 2
    TIGHT['r'] = (arb(0, A_((a1 - a0) / 2)), arb(0, A_((d1 - d0) / 2)), arb(0, A_((e1 - e0) / 2)))
    Ac = J.var(A_(ac), 0, DUAL_MODE)
    Dc = dvar(A_(dc), DUAL_MODE)
    Ec = J.var(A_(ec), 2, DUAL_MODE)
    Ab = J.var(arb.union(A_(a0), A_(a1)), 0, DUAL_MODE)
    Db = dvar(arb.union(A_(d0), A_(d1)), DUAL_MODE)
    Eb = J.var(arb.union(A_(e0), A_(e1)), 2, DUAL_MODE)
    A = DJ(Ac, Ab)
    D = DJ(Dc, Db)
    B = A + D
    cx = DCtx(Ec, Eb)
    G = form(A, B, cx, D)
    Lc, _ = margins_from_logF(G.cj)
    _, grads = margins_from_logF(tighten(G.bj, G.cj))
    return Lc, grads
