"""Theorem B, the strip 0 <= a <= 3 (s < e^{3/n}) and the corner a, d -> 0: Taylor models in a.

Every quantity is a "TS": for each slot (j, k) of a fixed downward-closed set, an arb power series in the variable a
(length L), the slot standing for the Taylor coefficient of order j in the second variable y and of order k in eps.
The second variable is y = d (coordinates (a, d), b = a + d; the a-series is then taken at fixed d) or y = b
(coordinates (a, b), d = b - a; the a-series at fixed b).  Univariate functions are composed through their Taylor
coefficients (enclosures valid at every point of the argument ball); products are truncated.  Every operation is a
ball operation, so every coefficient of a TS evaluated at a ball point encloses the corresponding Taylor coefficient
at every point of the ball.

Three evaluations per box  a in a_c + DA, y in y_c + DY, eps in e_c + DE  (DA, DY, DE intervals containing 0):
  P (centre): a = a_c, y = y_c, eps = e_c thin (eps may be a ball where no eps slots are used),
  F (face):   a = a_c thin, y and eps balls,
  B (box):    a, y and eps balls.
F is tightened against P before every univariate function and after every product (Taylor in y up to the top slot,
mean value in eps):  F[j,k] <- P[j,k] + sum_{1<=q<Q} C(j+q,q) P[j+q,k] DY^q + C(j+Q,Q) F[j+Q,k] DY^Q + (k+1) F[j,k+1] DE
(j + Q = top y-order of row k), intersected coefficientwise with the naive F.  The removable a^2 of E^R:
E^R(0, y) = d_a E^R(0, y) = 0 (exact identities), so X = E^R/a^2 has the a-series of E^R shifted by two (P, F: exact
division; B with a in [0, a1]: X^{(m)}(a)/m! = int_0^1 (m+1)(m+2)(1-u) u^m E_{m+2}(ua) du is a weighted mean of the
(m+2)-th coefficient of E^R on [0, a], hence enclosed by the shifted box series).  The box series of X is then
replaced, coefficient by coefficient, by its Taylor expansion from the face:
  X_m(box) <- sum_{l<L-1-m} C(m+l,l) Xf_{m+l} DA^l + C(L-1,m) X_{L-1}(box) DA^{L-1-m}   (Xf: tightened face),
so that the cancellation in E^R never meets interval arithmetic in the a-direction (only the top coefficient of the box
series enters, multiplied by DA^{L-1-m}).  The final enclosure of any Taylor coefficient c_{i,(j,k)} of log Hhat on the
box is the same Taylor model in a with the tightened face coefficients and the top box coefficient.
"""
import sys
import time
from fractions import Fraction as Fr
from math import comb, factorial, floor, ceil
import flint
from flint import arb, arb_series, fmpq, arb_poly
import tb_arb as T

PREC = 160
CAP = 64
flint.ctx.prec = PREC
flint.ctx.cap = CAP
ZERO, ONE = arb(0), arb(1)
LAM, ETA, MU = T.LAM, T.ETA, T.MU


def q_(x):
    if isinstance(x, (int,)):
        return arb(x)
    return arb(fmpq(x.numerator, x.denominator))


def SER(c, L):
    flint.ctx.cap = CAP
    return arb_series(c, prec=L)


def coeffs(s, L):
    c = s.coeffs()
    return [c[i] if i < len(c) else ZERO for i in range(L)]


def prov(fn, *args):
    """call a coefficient provider of tb_arb (which may change flint.ctx.cap) and restore the cap."""
    try:
        return fn(*args)
    finally:
        flint.ctx.cap = CAP


class Space:
    def __init__(self, slots):
        self.slots = list(slots)
        assert self.slots[0] == (0, 0)
        self.idx = {s: i for i, s in enumerate(self.slots)}
        self.n = len(self.slots)
        self.table = []
        for p, s1 in enumerate(self.slots):
            for q, s2 in enumerate(self.slots):
                s = (s1[0] + s2[0], s1[1] + s2[1])
                if s in self.idx:
                    self.table.append((p, q, self.idx[s]))
        self.nil = max(j + k for j, k in self.slots)
        self.top = {}
        for j, k in self.slots:
            self.top[k] = max(self.top.get(k, 0), j)
        self.ke = max(k for _, k in self.slots)


def body_space(ke):
    sl = [(0, 0)]
    rows = {0: 3, 1: 2, 2: 1, 3: 0, 4: 0}
    for k in range(ke + 1):
        for j in range(rows[k] + 1):
            if (j, k) != (0, 0):
                sl.append((j, k))
    return Space(sl)


_CS = {}


def corner_space(J, ke=0):
    """slots (j, k), k <= ke, j <= J - k (Taylor in b up to order J in the corner)."""
    key = (J, ke)
    if key not in _CS:
        sl = [(0, 0)]
        for k in range(ke + 1):
            for j in range(J - k + 1):
                if (j, k) != (0, 0):
                    sl.append((j, k))
        _CS[key] = Space(sl)
    return _CS[key]


_RESTRICT = {}


def restrict(x, sp):
    if x.sp is sp:
        return x
    s = [None] * sp.n
    for i, sl in enumerate(sp.slots):
        j = x.sp.idx.get(sl)
        if j is None:
            raise ValueError('restrict: slot missing')
        s[i] = x.s[j]
    return TS(s, sp, x.L)


class TS:
    __slots__ = ('s', 'sp', 'L')

    def __init__(self, s, sp, L):
        self.s = s
        self.sp = sp
        self.L = L

    @staticmethod
    def const(v, sp, L):
        s = [None] * sp.n
        s[0] = SER([arb(v)], L)
        return TS(s, sp, L)

    @staticmethod
    def avar(a0, sp, L):
        s = [None] * sp.n
        s[0] = SER([arb(a0), ONE], L)
        return TS(s, sp, L)

    @staticmethod
    def yvar(y0, sp, L):
        s = [None] * sp.n
        s[0] = SER([arb(y0)], L)
        s[sp.idx[(1, 0)]] = SER([ONE], L)
        return TS(s, sp, L)

    @staticmethod
    def evar(e0, sp, L):
        s = [None] * sp.n
        s[0] = SER([arb(e0)], L)
        if (0, 1) in sp.idx:
            s[sp.idx[(0, 1)]] = SER([ONE], L)
        return TS(s, sp, L)

    def c0(self):
        c = self.s[0].coeffs()
        return c[0] if c else ZERO

    def __add__(x, y):
        if isinstance(y, TS):
            if x.sp is not y.sp:
                x, y = _common(x, y)
            s = [a if b is None else (b if a is None else a + b) for a, b in zip(x.s, y.s)]
            return TS(s, x.sp, min(x.L, y.L))
        s = list(x.s)
        s[0] = s[0] + y
        return TS(s, x.sp, x.L)
    __radd__ = __add__

    def __neg__(x):
        return TS([None if a is None else -a for a in x.s], x.sp, x.L)

    def __sub__(x, y):
        if isinstance(y, TS):
            return x + (-y)
        s = list(x.s)
        s[0] = s[0] - y
        return TS(s, x.sp, x.L)

    def __rsub__(x, y):
        return (-x) + y

    def __mul__(x, y):
        if isinstance(y, TS):
            if x.sp is not y.sp:
                x, y = _common(x, y)
            out = [None] * x.sp.n
            xs, ys = x.s, y.s
            for p, q, r in x.sp.table:
                a = xs[p]
                if a is None:
                    continue
                b = ys[q]
                if b is None:
                    continue
                t = a * b
                out[r] = t if out[r] is None else out[r] + t
            L = min(x.L, y.L)
            if out[0] is None:
                out[0] = SER([ZERO], L)
            return TS(out, x.sp, L)
        return TS([None if a is None else a * y for a in x.s], x.sp, x.L)
    __rmul__ = __mul__

    def __truediv__(x, y):
        if isinstance(y, TS):
            return x * y.recip()
        return TS([None if a is None else a / y for a in x.s], x.sp, x.L)

    def __rtruediv__(x, y):
        return x.recip() * y

    def compose(x, g):
        """g: Taylor coefficients (orders 0 .. L-1+nil) of a univariate function, valid at every point of the
        constant term of x."""
        L = x.L
        c = coeffs(x.s[0], L)
        has_delta = any(v is not None for v in x.s[1:])
        mmax = x.sp.nil if has_delta else 0
        if len(g) < L + mmax:
            raise ValueError('compose: not enough coefficients')
        t = SER([ZERO] + c[1:], L)
        tp = [SER([ONE], L)]
        nonconst = any(not (ci == 0) for ci in c[1:])
        if nonconst:
            for p in range(1, L):
                tp.append(tp[-1] * t)
        F = []
        for m in range(mmax + 1):
            acc = SER([g[m]], L)
            if nonconst:
                for p in range(1, L):
                    acc = acc + tp[p] * (g[m + p] * comb(m + p, m))
            F.append(acc)
        out = [None] * x.sp.n
        out[0] = F[0]
        if has_delta:
            delta = TS([None] + list(x.s[1:]), x.sp, L)
            dp = delta
            for m in range(1, mmax + 1):
                for i, v in enumerate(dp.s):
                    if v is None:
                        continue
                    w = v * F[m]
                    out[i] = w if out[i] is None else out[i] + w
                if m < mmax:
                    dp = _mul_nz(dp, delta)
        return TS(out, x.sp, L)

    def _K(self):
        return self.L - 1 + self.sp.nil

    def exp(x):
        return x.compose(prov(T.g_exp, x.c0(), x._K()))

    def log(x):
        return x.compose(prov(T.g_log, x.c0(), x._K()))

    def sqrt(x):
        return x.compose(prov(T.g_sqrt, x.c0(), x._K()))

    def recip(x):
        return x.compose(prov(T.g_recip, x.c0(), x._K()))

    def phi1(x):
        return x.compose(prov(T.g_phi1, x.c0(), x._K()))

    def coef(x, i, j=0, k=0):
        v = x.s[x.sp.idx[(j, k)]]
        if v is None:
            return ZERO
        c = v.coeffs()
        return c[i] if i < len(c) else ZERO


def _mul_nz(x, y):
    """product of two TS whose slot 0 may be None (nilpotent parts)."""
    out = [None] * x.sp.n
    for p, q, r in x.sp.table:
        a = x.s[p]
        if a is None:
            continue
        b = y.s[q]
        if b is None:
            continue
        t = a * b
        out[r] = t if out[r] is None else out[r] + t
    return TS(out, x.sp, min(x.L, y.L))


def _common(x, y):
    if x.sp.n <= y.sp.n:
        return x, restrict(y, x.sp)
    return restrict(x, y.sp), y


def ashift(x, k, check=False):
    """divide by a^k a TS whose a-series vanish to order k in every slot (exact identities); with check=True the
    dropped coefficients must contain 0."""
    L = x.L - k
    out = []
    for v in x.s:
        if v is None:
            out.append(None)
            continue
        c = coeffs(v, x.L)
        if check:
            for i in range(k):
                if not c[i].contains(0):
                    raise ValueError('ashift: coefficient %d does not contain 0: %s' % (i, c[i]))
        out.append(SER(c[k:], L))
    return TS(out, x.sp, L)


def yshift(x, sp_new, check=False):
    """divide by y a TS that vanishes at y = 0 (corner, y = b): slot (j, k) of the result = slot (j+1, k)."""
    out = [None] * sp_new.n
    for i, (j, k) in enumerate(sp_new.slots):
        src = x.sp.idx.get((j + 1, k))
        if src is None:
            raise ValueError('yshift: slot missing')
        out[i] = x.s[src]
    if check:
        for (j, k) in x.sp.slots:
            if j == 0:
                v = x.s[x.sp.idx[(0, k)]]
                if v is not None:
                    for c in v.coeffs():
                        if not c.contains(0):
                            raise ValueError('yshift: slot (0,%d) does not vanish: %s' % (k, c))
    if out[0] is None:
        out[0] = SER([ZERO], x.L)
    return TS(out, sp_new, x.L)


# ---------------- tightening ----------------
class Tight:
    DY = ZERO
    DE = ZERO
    DA = ZERO
    ON = True
    PRODUCTS = True
    INTERSECT = False
    BOX = False


def _ipow(x, n):
    r = ONE
    for _ in range(n):
        r = r * x
    return r


def tighten_face(f, p):
    """F <- Taylor in y from the centre P (up to the top y-slot of each eps-row, top from F), plus the mean value in
    eps (if DE != 0 and an eps-successor slot exists); slots that cannot be tightened keep the naive F."""
    if not Tight.ON:
        return f
    if p.sp is not f.sp:
        p = restrict(p, f.sp) if f.sp.n <= p.sp.n else p
        if p.sp is not f.sp:
            f = restrict(f, p.sp)
    sp = f.sp
    DY, DE = Tight.DY, Tight.DE
    ey = not (DY == 0)
    ee = not (DE == 0)
    L = min(f.L, p.L)
    out = list(f.s)
    for i, (j, k) in enumerate(sp.slots):
        if f.s[i] is None and p.s[i] is None:
            continue
        top = sp.top[k]
        Q = top - j
        if ey and Q == 0:
            continue
        if ee:
            ie = sp.idx.get((j, k + 1))
            if ie is None:
                continue
        acc = p.s[i] if p.s[i] is not None else SER([ZERO], L)
        if ey:
            for qq in range(1, Q):
                v = p.s[sp.idx[(j + qq, k)]]
                if v is not None:
                    acc = acc + v * (comb(j + qq, qq) * _ipow(DY, qq))
            v = f.s[sp.idx[(j + Q, k)]]
            if v is not None:
                acc = acc + v * (comb(j + Q, Q) * _ipow(DY, Q))
        if ee:
            v = f.s[ie]
            if v is not None:
                acc = acc + v * ((k + 1) * DE)
        if Tight.INTERSECT and f.s[i] is not None:
            a = coeffs(acc, L)
            b = coeffs(f.s[i], L)
            cc = []
            for u, w in zip(a, b):
                try:
                    cc.append(u.intersection(w))
                except ValueError:
                    cc.append(u)
            acc = SER(cc, L)
        out[i] = acc
    return TS(out, sp, L)


def taylor_box(b, f, DA):
    """box series <- Taylor model in a from the (tightened) face series f, the top coefficient from the box b:
    coefficient m <- sum_{l < L-1-m} C(m+l,l) f_{m+l} DA^l + C(L-1, m) b_{L-1} DA^{L-1-m}, i.e. the Taylor shift by the
    ball DA of the polynomial f_0 + ... + f_{L-2} t^{L-2} + b_{L-1} t^{L-1} (arb_poly composition)."""
    sp = b.sp
    if f.sp is not sp:
        f = restrict(f, sp) if sp.n <= f.sp.n else f
        if f.sp is not sp:
            b = restrict(b, f.sp)
            sp = f.sp
    L = min(b.L, f.L)
    shift = arb_poly([DA, ONE])
    out = [None] * sp.n
    for i in range(sp.n):
        fv, bv = f.s[i], b.s[i]
        if fv is None and bv is None:
            continue
        fc = coeffs(fv, L) if fv is not None else [ZERO] * L
        bc = coeffs(bv, L) if bv is not None else [ZERO] * L
        poly = arb_poly(fc[:L - 1] + [bc[L - 1]])
        sh = poly(shift).coeffs()
        res = []
        for m in range(L):
            u = sh[m] if m < len(sh) else ZERO
            if bv is not None:
                try:
                    u = u.intersection(bc[m])
                except ValueError:
                    pass
            res.append(u)
        out[i] = SER(res, L)
    if out[0] is None:
        out[0] = SER([ZERO], L)
    return TS(out, sp, L)


def tm_coef(fc, bc, i, DA):
    """enclosure on the box of the a-coefficient of order i from face coefficients fc and box coefficients bc
    (same slot): sum_{l < L-1-i} C(i+l,l) fc[i+l] DA^l + C(L-1, i) bc[L-1] DA^{L-1-i}."""
    L = len(fc)
    acc = ZERO
    p = ONE
    for l in range(L - 1 - i):
        acc += fc[i + l] * (comb(i + l, l) * p)
        p = p * DA
    acc += bc[L - 1] * (comb(L - 1, i) * p)
    return acc


# ---------------- triples ----------------
class TT:
    __slots__ = ('p', 'f', 'b')

    def __init__(self, p, f, b):
        self.p, self.f, self.b = p, f, b

    def __add__(x, y):
        if isinstance(y, TT):
            return TT(x.p + y.p, x.f + y.f, x.b + y.b)
        return TT(x.p + y, x.f + y, x.b + y)
    __radd__ = __add__

    def __neg__(x):
        return TT(-x.p, -x.f, -x.b)

    def __sub__(x, y):
        if isinstance(y, TT):
            return TT(x.p - y.p, x.f - y.f, x.b - y.b)
        return TT(x.p - y, x.f - y, x.b - y)

    def __rsub__(x, y):
        return (-x) + y

    def __mul__(x, y):
        if isinstance(y, TT):
            p = x.p * y.p
            f = x.f * y.f
            b = x.b * y.b
            if Tight.PRODUCTS:
                f = tighten_face(f, p)
                if Tight.BOX:
                    b = taylor_box(b, f, Tight.DA)
            return TT(p, f, b)
        return TT(x.p * y, x.f * y, x.b * y)
    __rmul__ = __mul__

    def __truediv__(x, y):
        if isinstance(y, TT):
            return x * y.recip()
        return TT(x.p / y, x.f / y, x.b / y)

    def __rtruediv__(x, y):
        return x.recip() * y

    def _u(x, name):
        f = tighten_face(x.f, x.p)
        b = taylor_box(x.b, f, Tight.DA) if Tight.BOX else x.b
        return TT(getattr(x.p, name)(), getattr(f, name)(), getattr(b, name)())

    def exp(x):
        return x._u('exp')

    def log(x):
        return x._u('log')

    def sqrt(x):
        return x._u('sqrt')

    def recip(x):
        return x._u('recip')

    def phi1(x):
        return x._u('phi1')

    def tight(x):
        return TT(x.p, tighten_face(x.f, x.p), x.b)


# ---------------- special functions ----------------
_SQ_CACHE = {}
NS2 = 120
BETA2 = [arb(x) for x in T._beta_exact(NS2)]


def s_coeffs_q(eps, ke):
    """eps-Taylor coefficients (orders 0..ke) of the exact eps-polynomials s_k(eps), k = 0..N_S, at the ball eps:
    for a thin eps exactly; for a wide ball the order-q coefficient is enclosed by the centred form
    c_q(mid) + (q+1) c_{q+1}(ball) [-r, r] for q < ke+1 (ball evaluation with one more order)."""
    key = (eps.mid().str(30), eps.rad().str(5), ke)
    if key in _SQ_CACHE:
        return _SQ_CACHE[key]

    def raw(e, kk):
        Ls = kk + 1
        E = SER([e, ONE], Ls) if kk > 0 else SER([e], 1)
        v = 1 + 2 * E
        h = [SER([ONE], Ls)]
        epow = [SER([ONE], Ls)]
        for i in range(1, NS2 + 1):
            epow.append(epow[-1] * E)
        for i in range(1, NS2 + 1):
            h.append(v * h[i - 1] + epow[i])
        psi = [h[i] / factorial(i + 2) for i in range(NS2 + 1)]
        out = [[ZERO] * (NS2 + 1) for _ in range(kk + 1)]
        for k in range(2, NS2 + 1):
            acc = SER([ZERO], Ls)
            for i in range(k + 1):
                j = k - i
                acc = acc + psi[i] * epow[j] * BETA2[j]
            acc = 2 * acc - arb(fmpq(1, 3 ** k * factorial(k)))
            c = coeffs(acc, Ls)
            for qq in range(kk + 1):
                out[qq][k] = c[qq]
        return out

    if eps.rad() > 1e-30:
        mid = raw(arb(eps.mid()), ke)
        ball = raw(eps, ke + 1)
        r = arb(0, eps.rad())
        res = [[mid[qq][k] + (qq + 1) * ball[qq + 1][k] * r for k in range(NS2 + 1)] for qq in range(ke + 1)]
    else:
        res = raw(eps, ke)
    _SQ_CACHE[key] = res
    return res


_STQ = {}
_TK = []


def _tk_list():
    """T_k = 26 sum_{i<=k} (41/37)^i/(i+1)! (2/37)^{k-i} + 1/(3^k k!), k = NS2+1 .. 600."""
    if not _TK:
        v = arb(41) / 37
        e = arb(2) / 37
        vp = [ONE]
        ep = [ONE]
        for i in range(601):
            vp.append(vp[-1] * v)
            ep.append(ep[-1] * e)
        for k in range(NS2 + 1, 601):
            Tk = ZERO
            for i in range(k + 1):
                Tk += vp[i] / factorial(i + 1) * ep[k - i]
            _TK.append((k, 26 * Tk + arb(fmpq(1, 3 ** k * factorial(k)))))
    return _TK


def s_tails_q(hq, qq, K):
    """bounds, m = 0..K, of sum_{k > NS2} |s_k^{[q]}| C(k-2, m) h^{k-2-m}, h = hq/8 <= 8, valid for all real eps in
    [0, 1/37]: by Cauchy's estimate on the disc |zeta - eps| <= 1/37 (|zeta| <= 2/37), |s_k^{[q]}(eps)| <= 37^q T_k with
    T_k = 26 sum_{i<=k} (41/37)^i/(i+1)! (2/37)^{k-i} + 1/(3^k k!)  (|beta_j| <= 13, |psi_i(zeta)| <= (41/37)^i/(i+1)!).
    The terms k > 600 decrease geometrically (ratio < 0.1 for h <= 8) and add < 1e-150."""
    key = (hq, qq, K)
    if key in _STQ:
        return _STQ[key]
    h = arb(fmpq(hq, 8))
    f = arb(37) ** qq
    out = [ZERO] * (K + 1)
    hp = [ONE]
    for i in range(601):
        hp.append(hp[-1] * h)
    for k, Tk in _tk_list():
        for m in range(K + 1):
            if k - 2 - m >= 0:
                out[m] += Tk * f * comb(k - 2, m) * hp[k - 2 - m]
    res = [float(x.upper()) + 1e-150 for x in out]
    _STQ[key] = res
    return res


def g_S_q(x0, eps, ke, K):
    """for q = 0..ke: Taylor coefficients (orders 0..K) at the ball x0 (|x0| <= 8) of S^{[q]}(x) = sum_k s_k^{[q]} x^{k-2}
    (the q-th eps-Taylor coefficient of S(x; eps) at eps).  Wide x-balls: centred form in x."""
    h = abs(x0).upper()
    if h > 8:
        raise T.NotPositive('S series used beyond |x| <= 8')
    sq = s_coeffs_q(eps, ke)

    def raw(xb, KK):
        hq = int(ceil(float(abs(xb).upper()) * 8 + 1e-9))
        res = []
        for qq in range(ke + 1):
            tl = s_tails_q(hq, qq, KK)
            res.append(prov(T.taylor_from_series, sq[qq][2:], xb, KK, lambda m, tl=tl: tl[m]))
        return res

    if x0.rad() < 1e-10:
        return raw(x0, K)
    mid = arb(x0.mid())
    r = arb(0, x0.rad())
    cm = raw(mid, K)
    cb = raw(x0, K + 1)
    return [[cm[qq][m] + (m + 1) * cb[qq][m + 1] * r for m in range(K + 1)] for qq in range(ke + 1)]


def S_ts(X, eball, ke):
    """S(x; eps) at the TS X: sum_q (eps - eps0)^q S^{[q]}(x), eps-slots up to ke (eball: the eps ball of this
    evaluation; (eps - eps0)^q is the slot (0, q))."""
    K = X._K()
    gs = g_S_q(X.c0(), eball, ke, K)
    res = X.compose(gs[0])
    for qq in range(1, ke + 1):
        if (0, qq) not in X.sp.idx:
            break
        eq = TS.const(ZERO, X.sp, X.L)
        eq.s[X.sp.idx[(0, qq)]] = SER([ONE], X.L)
        res = res + eq * X.compose(gs[qq])
    return res


PHW = 128
_PH2 = {}
PH_TOL = 2e-4
PH_TOL_ORD = 4


def _ph_cell(lo, hi, K):
    mid = (lo + hi) / 2
    r = (hi - lo) / 2
    try:
        naive = prov(T.g_Phihat_raw, arb.union(arb(lo), arb(hi)), K + 1)
    except (T.NotPositive, ValueError):
        if hi - lo < fmpq(1, 2 ** 16):
            raise
        a = _ph_cell(lo, mid, K)
        b = _ph_cell(mid, hi, K)
        return [arb.union(x, y) for x, y in zip(a, b)]
    cm = prov(T.g_Phihat_raw, arb(mid), K)
    R = arb(0, arb(r))
    out = [cm[k] + (k + 1) * naive[k + 1] * R for k in range(K + 1)]
    if max(float(x.rad()) for x in out[:PH_TOL_ORD + 1]) > PH_TOL and hi - lo >= fmpq(1, 2 ** 14):
        a = _ph_cell(lo, mid, K)
        b = _ph_cell(mid, hi, K)
        return [arb.union(x, y) for x, y in zip(a, b)]
    return out


def g_Phihat2(z0, K):
    """enclosures of the Taylor coefficients (0..K) of Phihat at all points of z0: thin balls directly; other balls in
    [-2, inf) by the union of cached cells [k/128, (k+1)/128] (centred forms, bisected until the coefficients of order
    <= 4 have radius <= 2e-4; on [-2, 2] the series branch, which is analytic there, is used; negative arguments
    occur only for box points with b < a, outside the region of interest, through the analytic continuation)."""
    if z0.rad() < 1e-12:
        return prov(T.g_Phihat_raw, z0, K)
    lo, hi = z0.lower(), z0.upper()
    if lo < 0 and lo > -1e-6:
        lo = arb(0)
    if lo < -2:
        raise T.NotPositive('Phihat2: argument below -2')
    k0 = int(floor(float(lo) * PHW))
    k1 = int(floor(float(hi) * PHW))
    parts = []
    for k in range(k0, k1 + 1):
        key = (k, K)
        if key not in _PH2:
            _PH2[key] = _ph_cell(fmpq(k, PHW), fmpq(k + 1, PHW), K)
        parts.append(_PH2[key])
    out = list(parts[0])
    for pp in parts[1:]:
        out = [arb.union(x, y) for x, y in zip(out, pp)]
    return out


def Phihat_ts(Z):
    return Z.compose(g_Phihat2(Z.c0(), Z._K()))


# TT versions of the special functions
def S_tt(X, cx):
    Xf = tighten_face(X.f, X.p)
    Xb = taylor_box(X.b, Xf, Tight.DA) if Tight.BOX else X.b
    return TT(S_ts(X.p, cx.ep, cx.ke), S_ts(Xf, cx.ef, cx.ke), S_ts(Xb, cx.ef, cx.ke))


def Phihat_tt(Z):
    Zf = tighten_face(Z.f, Z.p)
    Zb = taylor_box(Z.b, Zf, Tight.DA) if Tight.BOX else Z.b
    return TT(Phihat_ts(Z.p), Phihat_ts(Zf), Phihat_ts(Zb))


class Cx:
    """eps-dependent constants (TT); ep: eps ball of the centre, ef: eps ball of face and box."""

    def __init__(self, Ep, Ef, sp, L, ke):
        self.ke = ke
        self.ep, self.ef = Ep, Ef
        self.eps = TT(TS.evar(Ep, sp, L), TS.evar(Ef, sp, L), TS.evar(Ef, sp, L))
        self.e1 = 1 + self.eps
        self.e2 = 1 + 2 * self.eps
        self.c = 2 / self.e1
        self.cp = 2 / (self.e1 * self.e2)
        self.sqcp = self.cp.sqrt()


def nu_tt(Z, cx):
    return 1 / (Z * (-(Z * cx.eps)).phi1())


def P_tt(Z, cx):
    return (Z * cx.e2).phi1() / (Z * cx.eps).phi1()


def qa_tt(A, cx):
    return (-(A * cx.e2)).phi1() / (-(A * cx.eps)).phi1()


def cpgam_tt(Z, cx, small):
    """c' gam_z (small z: z^4 phi1(-z eps)^2 S(z) e^{-z}; else the nu-form)."""
    if small:
        p = (-(Z * cx.eps)).phi1()
        Z2 = Z * Z
        return Z2 * Z2 * p * p * S_tt(Z, cx) * (-Z).exp()
    nz = nu_tt(Z, cx)
    pz = (-(Z * cx.e2)).exp() + cx.e2 * (-(Z * cx.e1)).exp() / nz
    yz = (-(Z / 3)).exp() / (nz * cx.sqcp)
    return cx.cp * (1 - pz - yz * yz)


def bpart_tt(B, cx):
    """(log nu_b - log om_b)/2 for b >= 2.5 (nu-branch)."""
    nb = nu_tt(B, cx)
    omb = 1 - nb * (1 - (-(B * cx.e2)).exp()) / cx.e2 - (-(B / 3)).exp() / (cx.c * nb)
    return (nb.log() - omb.log()) / 2


# ---------------- forms ----------------
def yshift_tt(x, sp_new):
    return TT(yshift(x.p, sp_new, check=True), yshift(x.f, sp_new, check=False), yshift(x.b, sp_new))


def ER_direct(A, B, D, cx, corner_sp=None):
    """E^R = K_n(1,s,t) - e^{a/2} sqrt(kappa(b) kappa(d)) R  (direct form; b, d <= 8):
    K_n(1,s,t) = c [e^{a(1+eps)} P(d) - P(a)]/(b phi1(b eps)) - e^{(a+b)/3}, kappa(z) = z^2 S(z).
    corner_sp given (coordinates (a, b), box touching b = 0): the numerator N1 = e^{a(1+eps)} P(d) - P(a) vanishes
    at b = 0 (P(-a) = e^{-a(1+eps)} P(a)), so N1/b is the slot shift of N1 (weighted mean in b, as for a^2)."""
    N1 = (A * cx.e1).exp() * P_tt(D, cx) - P_tt(A, cx)
    if corner_sp is not None:
        K1 = cx.c * yshift_tt(N1, corner_sp) / (B * cx.eps).phi1() - ((A + B) / 3).exp()
    else:
        K1 = cx.c * N1 / (B * (B * cx.eps).phi1()) - ((A + B) / 3).exp()
    cap = (A / 2).exp() * B * D * (S_tt(B, cx) * S_tt(D, cx)).sqrt()
    dif = Phihat_tt(B) * (-MU * B).exp() - Phihat_tt(D) * (-MU * D).exp()
    R = (-(dif * dif)).exp()
    return K1 - cap * R


def Ghat_direct(A, B, D, cx, X):
    """log Hhat = log(F b/a) = log X - (a+b)/2 - log S(-a)/2 - log S(-b)/2   (X = E^R/a^2, W(z) = z^2 e^z S(-z))."""
    return X.log() - (A + B) / 2 - S_tt(-A, cx).log() / 2 - S_tt(-B, cx).log() / 2


def ER_nu(A, B, D, cx, corner_sp=None):
    """Dhat = e^{(1/2+lam) d} D (scaled nu-form with the perfect square, as tb_arb.logF_nu5; b, d >= ~2.5)."""
    eps, e1, e2 = cx.eps, cx.e1, cx.e2
    nb, nd = nu_tt(B, cx), nu_tt(D, cx)
    ema, emb, emd = (-A).exp(), (-B).exp(), (-D).exp()
    ema3, emd3 = (-(A / 3)).exp(), (-(D / 3)).exp()
    yhb, yhd = 1 / (nb * cx.sqcp), 1 / (nd * cx.sqcp)
    phb = (-(2 * eps) * B).exp() + e2 * (-eps * B).exp() / nb
    phd = (-(2 * eps) * D).exp() + e2 * (-eps * D).exp() / nd
    uh1 = (-(2 * eps) * D).exp()
    uh2 = e2 * qa_tt(A, cx) * (-eps * D).exp() / nd
    uh = uh1 + uh2
    emd43 = emd * emd3
    Nt = ((yhb * ema3 - yhd) * (yhb * ema3 - yhd) + emd3 * (phb * ema + phd - 2 * uh) + emd43 * uh * uh
          + 2 * emd * ema3 * uh * yhb * yhd - phb * phd * ema * emd43 - phb * yhd * yhd * ema * emd
          - phd * yhb * yhb * ema3 * ema3 * emd)
    # gam_z = c' gam_z / c': for z <= 8 by the cancellation-free series form z^4 phi1(-z eps)^2 S(z) e^{-z}
    gb = cpgam_tt(B, cx, B.b.c0().upper() <= 8) / cx.cp
    if D.b.c0().upper() <= 8:
        gd = cpgam_tt(D, cx, True) / cx.cp
    else:
        gd = 1 - phd * emd - yhd * yhd * emd3 * emd3
    kh = 1 - emd * uh - yhb * yhd * ema3 * emd3 * emd3
    sg = gb.sqrt() * gd.sqrt()
    dif = Phihat_tt(B) * (-MU * A).exp() - Phihat_tt(D)
    dif2 = dif * dif
    xx = dif2 * (-((2 * MU) * D)).exp()
    psi = (-xx).phi1()
    return (-((arb(1) / 6 - LAM) * D)).exp() * Nt / (kh + sg) + sg * dif2 * psi


def Ghat_nu(A, B, D, cx, X):
    """log Hhat = -lam d + log nu_d - log S(-a)/2 + log(c)/2 + bpart(b) - log(1+2eps) + log X + log b, X = Dhat/a^2."""
    return (-LAM * D + nu_tt(D, cx).log() - S_tt(-A, cx).log() / 2 + cx.c.log() / 2 + bpart_tt(B, cx)
            - cx.e2.log() + X.log() + B.log())


FORMS = {'direct': (ER_direct, Ghat_direct), 'nu': (ER_nu, Ghat_nu)}


# ---------------- one box ----------------
class Res:
    pass


def evaluate(form, coords, a0, a1, y0, y1, e0, e1, L=16, ke=1, corner=False, J=10):
    """Ghat (TT) on the box a in [a0, a1], y in [y0, y1] (y = b for coords 'ab', y = d for 'ad'), eps in [e0, e1].
    Face at a_c = a0 if a0 == 0 else the midpoint.  corner=True: coordinates (a, b), y0 = 0, no eps slots (eps a
    ball in all three evaluations), face at y_c = 0 with the Taylor expansion in b up to order J."""
    ER, GH = FORMS[form]
    if corner:
        spbig = corner_space(J + 1, ke)
        sp = corner_space(J, ke)
    else:
        spbig = body_space(ke)
        sp = None
    a_c = Fr(0) if a0 == 0 else (a0 + a1) / 2
    DA = arb.union(q_(a0 - a_c), q_(a1 - a_c))
    y_c = Fr(0) if corner else (y0 + y1) / 2
    DY = arb.union(q_(y0 - y_c), q_(y1 - y_c)) if y1 > y0 else ZERO
    e_c = (e0 + e1) / 2
    Eball = arb.union(q_(e0), q_(e1)) if e1 > e0 else q_(e0)
    if ke >= 1:
        Ep = q_(e_c)
        DE = arb.union(q_(e0 - e_c), q_(e1 - e_c)) if e1 > e0 else ZERO
    else:
        Ep = Eball
        DE = ZERO
    Tight.DY, Tight.DE, Tight.DA = DY, DE, DA
    Yball = arb.union(q_(y0), q_(y1)) if y1 > y0 else q_(y0)
    Aball = arb.union(q_(a0), q_(a1)) if a1 > a0 else q_(a0)
    A = TT(TS.avar(q_(a_c), spbig, L), TS.avar(q_(a_c), spbig, L), TS.avar(Aball, spbig, L))
    Y = TT(TS.yvar(q_(y_c), spbig, L), TS.yvar(Yball, spbig, L), TS.yvar(Yball, spbig, L))
    if coords == 'ab':
        B, D = Y, Y - A
    else:
        D, B = Y, A + Y
    cx = Cx(Ep, Eball, spbig, L, ke)
    E = ER(A, B, D, cx, corner_sp=sp) if corner else ER(A, B, D, cx)
    if a_c == 0:
        X = TT(ashift(E.p, 2, check=True), ashift(E.f, 2, check=True), ashift(E.b, 2))
    else:
        X = E / (A * A)
    Xf = tighten_face(X.f, X.p)
    Xb = taylor_box(X.b, Xf, DA)
    X = TT(X.p, Xf, Xb)
    G = GH(A, B, D, cx, X)
    r = Res()
    r.G, r.X, r.DA, r.DY, r.DE = G, X, DA, DY, DE
    r.coords, r.a0, r.a1, r.y0, r.y1 = coords, a0, a1, y0, y1
    return r


def coef_box(r, i, j):
    """enclosure on the box of the Taylor coefficient (a^i, y^j) of Ghat, and the radii contributed by the
    y-direction, the eps-direction and the a-remainder."""
    G = r.G
    p, f, b = G.p, G.f, G.b
    sp = f.sp
    if p.sp is not sp:
        p = restrict(p, sp)
    if b.sp is not sp:
        b = restrict(b, sp)
    L = min(p.L, f.L, b.L)
    DA, DY, DE = r.DA, r.DY, r.DE
    top = sp.top[0]
    Q = top - j

    def cs(x, slot):
        v = x.s[sp.idx[slot]] if slot in sp.idx else None
        return coeffs(v, L) if v is not None else [ZERO] * L

    pc = {jj: cs(p, (jj, 0)) for jj in range(j, top + 1)}
    fcj = cs(f, (j, 0))
    ftop = cs(f, (top, 0))
    fe = cs(f, (j, 1)) if (j, 1) in sp.idx else None
    ey = not (DY == 0)
    ee = not (DE == 0)
    face, ry, re_ = [], [], []
    for m in range(L):
        if (ey and Q == 0) or (ee and fe is None):
            face.append(fcj[m])
            ry.append(float(fcj[m].rad()))
            re_.append(0.0)
            continue
        yt = ZERO
        if ey:
            pw = ONE
            for qq in range(1, Q):
                pw = pw * DY
                yt += pc[j + qq][m] * (comb(j + qq, qq) * pw)
            yt += ftop[m] * (comb(j + Q, Q) * pw * DY)
        et = fe[m] * DE if ee else ZERO
        v = pc[j][m] + yt + et
        try:
            v = v.intersection(fcj[m])
        except ValueError:
            pass
        face.append(v)
        ry.append(float(yt.rad()))
        re_.append(float(et.rad()))
    bc = cs(b, (j, 0))
    acc = ZERO
    pw = ONE
    cy, ce = 0.0, 0.0
    for l in range(L - 1 - i):
        w = comb(i + l, l) * pw
        acc += face[i + l] * w
        mag = float(abs(w).upper())
        cy += ry[i + l] * mag
        ce += re_[i + l] * mag
        pw = pw * DA
    remt = bc[L - 1] * (comb(L - 1, i) * pw)
    acc += remt
    return acc, (cy, ce, float(remt.rad()))


def conditions(r):
    """M1 = a L1, M2 = b L2, M3 = a b L3 and (b > 0) N2 = L2, N3 = a L3 on the box (Hhat = F b/a,
    L1 = 1/a + Ghat_a, L2 = 1/b - Ghat_b, L3 = (1/a)(1/b - Ghat_b) + Ghat_a/b - Ghat_ab - Ghat_a Ghat_b)."""
    if r.coords == 'ab':
        ga, ca = coef_box(r, 1, 0)
        gb, cb = coef_box(r, 0, 1)
        gab, cab = coef_box(r, 1, 1)
        contrib = [x + y + z for x, y, z in zip(ca, cb, cab)]
        brange = arb.union(q_(r.y0), q_(r.y1)) if r.y1 > r.y0 else q_(r.y0)
    else:
        c10, k1 = coef_box(r, 1, 0)
        c01, k2 = coef_box(r, 0, 1)
        c11, k3 = coef_box(r, 1, 1)
        c02, k4 = coef_box(r, 0, 2)
        ga, gb, gab = c10 - c01, c01, c11 - 2 * c02
        contrib = [x + y + z + w for x, y, z, w in zip(k1, k2, k3, k4)]
        brange = arb.union(q_(r.a0 + r.y0), q_(r.a1 + r.y1))
    arange = arb.union(q_(r.a0), q_(r.a1)) if r.a1 > r.a0 else q_(r.a0)
    M1 = 1 + arange * ga
    M2 = 1 - brange * gb
    M3 = 1 - brange * gb + arange * ga - arange * brange * (gab + ga * gb)
    out = {'M1': M1, 'M2': M2, 'M3': M3}
    if brange > 0:
        ib = 1 / brange
        N2 = ib - gb
        N3 = N2 - arange * (gab + ga * (gb - ib))
        out['N2'] = N2
        out['N3'] = N3
    ok1 = M1 > 0
    ok2 = (M2 > 0) or ('N2' in out and out['N2'] > 0)
    ok3 = (M3 > 0) or ('N3' in out and out['N3'] > 0)
    xpos = r.X.b.c0() > 0
    return (ok1 and ok2 and ok3 and xpos), out, contrib, (ga, gb, gab)
