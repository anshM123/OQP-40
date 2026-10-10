"""Independent verifier, strip part: Taylor models in a (own implementation; no code of tb_arb.py / tb_sx.py is used).

An AS ("a-series with slots") stores, for every slot (j, k) of a downward-closed set (j = order in b, k = order in eps),
an arb power series in the variable a of length L: slot (j,k), coefficient m = the Taylor coefficient
d_a^m d_b^j d_eps^k g/(m! j! k!) at the evaluation point.  Products are truncated per slot and in a; univariate
functions are composed through Taylor-coefficient enclosures valid on the whole argument ball.  With ball inputs every
coefficient encloses the true coefficient at every point of the ball (inclusion isotonicity of ball arithmetic).

Three evaluations per box [a0,a1] x [b0,b1] x [e0,e1] (centre a_c, b_c, e_c):
  P  thin point (a_c, b_c, e_c);   F  a = a_c thin, b and eps balls (the "face");   B  a, b, eps balls.
* F is tightened against P before every univariate function and after every product:
    F_{j,k} <- P_{j,k} + sum_{1<=q<Q} C(j+q,q) P_{j+q,k} DB^q + C(j+Q,Q) F_{j+Q,k} DB^Q + (k+1) F_{j,k+1} DE
  (Taylor in b about b_c at eps = e_c with Lagrange remainder from F's top b-slot of row k, then the mean value in eps;
  Q = top b-order of row k minus j), intersected with the naive F.  Slots that cannot be tightened keep the naive F.
* B is replaced (where needed) by the Taylor model in a from the tightened face:
    B_{slot}[m] <- sum_{l <= L-2-m} C(m+l,l) F_{slot}[m+l] DA^l + C(L-1,m) B_{slot}[L-1] DA^{L-1-m}
  (Taylor in a about a_c with Lagrange remainder from the top coefficient over the box), intersected with the naive B.
* a^2-division: E^R(0,b) = d_a E^R(0,b) = 0 identically (exact identities), so X = E^R/a^2: for a_c = 0 the P and F
  series are shifted by 2 (exact; the dropped coefficients are checked to contain 0), and the B series likewise:
  X_m(a) = int_0^1 (m+1)(m+2)(1-u) u^m E_{m+2}(ua) du is a weighted mean of E_{m+2} over [0, a] (box enclosure).
* Corner (b-face at b = 0): N1/b with N1(a, 0) = 0 by the same argument in b (slot shift), P exact.
"""
from math import comb
import flint
from flint import arb, arb_series, fmpq
import iv_jet as JJ
from iv_jet import NotPos
import iv_small as SM
import iv_phi as PH

CAP = 64
flint.ctx.prec = 200
flint.ctx.cap = CAP
ZERO, ONE = arb(0), arb(1)


def prov(fn, *args):
    """call a coefficient provider (which may change flint.ctx.cap) and restore the cap (otherwise arb_series products
    would be silently truncated)."""
    try:
        return fn(*args)
    finally:
        flint.ctx.cap = CAP


def SER(c, L):
    flint.ctx.cap = CAP
    return arb_series(c, prec=L)


def coefs(s, L):
    if s is None:
        return [ZERO] * L
    c = s.coeffs()
    return [c[i] if i < len(c) else ZERO for i in range(L)]


class Slots:
    def __init__(self, rows):
        """rows[k] = top b-order of eps-row k."""
        self.rows = dict(rows)
        self.slots = [(0, 0)] + [(j, k) for k in sorted(rows) for j in range(rows[k] + 1) if (j, k) != (0, 0)]
        self.idx = {s: i for i, s in enumerate(self.slots)}
        self.n = len(self.slots)
        self.table = [(p, q, self.idx[(s1[0] + s2[0], s1[1] + s2[1])])
                      for p, s1 in enumerate(self.slots) for q, s2 in enumerate(self.slots)
                      if (s1[0] + s2[0], s1[1] + s2[1]) in self.idx]
        self.nil = max(j + k for j, k in self.slots)
        self.ke = max(rows)


BODY = Slots({0: 3, 1: 2, 2: 1})
_CORNER = {}


def corner_slots(J):
    if J not in _CORNER:
        _CORNER[J] = Slots({0: J, 1: J - 1, 2: J - 2})
    return _CORNER[J]


class AS:
    __slots__ = ('s', 'sp', 'L')

    def __init__(self, s, sp, L):
        self.s, self.sp, self.L = s, sp, L

    @staticmethod
    def const(v, sp, L):
        s = [None] * sp.n
        s[0] = SER([arb(v)], L)
        return AS(s, sp, L)

    @staticmethod
    def avar(a0, sp, L):
        s = [None] * sp.n
        s[0] = SER([arb(a0), ONE], L)
        return AS(s, sp, L)

    @staticmethod
    def slotvar(v0, slot, sp, L):
        s = [None] * sp.n
        s[0] = SER([arb(v0)], L)
        if slot in sp.idx:
            s[sp.idx[slot]] = SER([ONE], L)
        return AS(s, sp, L)

    def c0(self):
        return coefs(self.s[0], 1)[0]

    def __add__(x, y):
        if isinstance(y, AS):
            x, y = _same(x, y)
            return AS([u if v is None else (v if u is None else u + v) for u, v in zip(x.s, y.s)], x.sp, min(x.L, y.L))
        s = list(x.s)
        s[0] = s[0] + y
        return AS(s, x.sp, x.L)
    __radd__ = __add__

    def __neg__(x):
        return AS([None if u is None else -u for u in x.s], x.sp, x.L)

    def __sub__(x, y):
        return x + (-y) if isinstance(y, AS) else x + (-y)

    def __rsub__(x, y):
        return (-x) + y

    def __mul__(x, y):
        if isinstance(y, AS):
            x, y = _same(x, y)
            out = [None] * x.sp.n
            for p, q, r in x.sp.table:
                u, v = x.s[p], y.s[q]
                if u is None or v is None:
                    continue
                w = u * v
                out[r] = w if out[r] is None else out[r] + w
            if out[0] is None:
                out[0] = SER([ZERO], min(x.L, y.L))
            return AS(out, x.sp, min(x.L, y.L))
        return AS([None if u is None else u * y for u in x.s], x.sp, x.L)
    __rmul__ = __mul__

    def __truediv__(x, y):
        if isinstance(y, AS):
            return x * y.recip()
        return AS([None if u is None else u / y for u in x.s], x.sp, x.L)

    def __rtruediv__(x, y):
        return x.recip() * y

    def nilpart(x):
        return AS([None] + list(x.s[1:]), x.sp, x.L)

    def compose(x, g):
        """f(x) from g[k] = f^(k)(x0)/k! (k = 0 .. L-1+nil), valid on the ball x0 = constant term of slot (0,0)."""
        L, sp = x.L, x.sp
        c = coefs(x.s[0], L)
        has_d = any(v is not None for v in x.s[1:])
        M = sp.nil if has_d else 0
        if len(g) < L + M:
            raise ValueError('compose: too few coefficients')
        t = SER([ZERO] + c[1:], L)
        nonconst = any(not (ci == 0) for ci in c[1:])
        tp = [SER([ONE], L)]
        if nonconst:
            for p in range(1, L):
                tp.append(tp[-1] * t)
        Fm = []
        for m in range(M + 1):
            acc = SER([g[m]], L)
            if nonconst:
                for p in range(1, L):
                    acc = acc + tp[p] * (g[m + p] * comb(m + p, m))
            Fm.append(acc)
        out = [None] * sp.n
        out[0] = Fm[0]
        if has_d:
            dl = x.nilpart()
            dp = dl
            for m in range(1, M + 1):
                for i, v in enumerate(dp.s):
                    if v is not None:
                        w = v * Fm[m]
                        out[i] = w if out[i] is None else out[i] + w
                if m < M:
                    dp = dp * dl
                    dp.s[0] = None
        if out[0] is None:
            out[0] = SER([ZERO], L)
        return AS(out, sp, L)

    def _K(x):
        return x.L - 1 + x.sp.nil

    def exp(x):
        return x.compose(prov(JJ.c_exp, x.c0(), x._K()))

    def log(x):
        return x.compose(prov(JJ.c_log, x.c0(), x._K()))

    def sqrt(x):
        return x.compose(prov(JJ.c_sqrt, x.c0(), x._K()))

    def recip(x):
        return x.compose(prov(JJ.c_recip, x.c0(), x._K()))

    def phi1(x):
        return x.compose(prov(JJ.c_phi1, x.c0(), x._K()))

    def Phi(x):
        """the design function Phi (series branch for |z| <= 2.05, closed form Phihat e^{-mu z} for z >= 1.8)."""
        z0 = x.c0()
        K = x._K()
        if z0.upper() <= 2 and z0.lower() >= -0.5:
            return x.compose(prov(SM.c_phi_small, z0, K))
        if z0.lower() >= 1.8 or (z0.rad() < 1e-40 and z0 > 0):
            return x.compose(prov(PH.c_phihat, z0, K)) * (-(PH.MU * x)).exp()
        raise NotPos('Phi: ball straddles the branch switch')

    def Phihat(x):
        z0 = x.c0()
        if not (z0.lower() >= 1.8 or (z0.rad() < 1e-40 and z0 > 0)):
            raise NotPos('Phihat needs z >= 1.8')
        return x.compose(prov(PH.c_phihat, z0, x._K()))


def _same(x, y):
    if x.sp is y.sp:
        return x, y
    raise ValueError('mixed slot spaces')


def S_as(X, E, ke):
    """S(X; E) (X any AS with |X| <= 8; E = eps AS with slot (0,1) = 1 if ke >= 1)."""
    L, sp = X.L, X.sp
    K = X._K()
    c = prov(SM.S_coeffs, X.c0(), E.c0(), K, ke)        # c[m][q], m <= K, q <= ke
    res = X.compose([c[m][0] for m in range(K + 1)])
    if ke >= 1 and (0, 1) in sp.idx:
        de = AS([None] * sp.n, sp, L)
        de.s[sp.idx[(0, 1)]] = SER([ONE], L)
        dq = de
        for q in range(1, ke + 1):
            res = res + dq * X.compose([c[m][q] for m in range(K + 1)])
            if q < ke:
                dq = dq * de
                dq.s[0] = None
    return res


# ---------------- triples (P, F, B) ----------------
class Ctl:
    DA = ZERO
    DB = ZERO
    DE = ZERO
    BOX = False


def tighten_face(f, p):
    sp = f.sp
    DB, DE = Ctl.DB, Ctl.DE
    eb = not (DB == 0)
    ee = not (DE == 0)
    L = min(f.L, p.L)
    out = list(f.s)
    for i, (j, k) in enumerate(sp.slots):
        if f.s[i] is None and p.s[i] is None:
            continue
        Q = sp.rows[k] - j
        if eb and Q == 0:
            continue
        ie = sp.idx.get((j, k + 1))
        if ee and ie is None:
            continue
        acc = p.s[i] if p.s[i] is not None else SER([ZERO], L)
        if eb:
            pw = ONE
            for q in range(1, Q):
                pw = pw * DB
                v = p.s[sp.idx[(j + q, k)]]
                if v is not None:
                    acc = acc + v * (comb(j + q, q) * pw)
            v = f.s[sp.idx[(j + Q, k)]]
            if v is not None:
                acc = acc + v * (comb(j + Q, Q) * pw * DB)
        if ee:
            v = f.s[ie]
            if v is not None:
                acc = acc + v * ((k + 1) * DE)
        if f.s[i] is not None:
            a1, b1 = coefs(acc, L), coefs(f.s[i], L)
            cc = []
            for u, w in zip(a1, b1):
                try:
                    cc.append(u.intersection(w))
                except ValueError:
                    raise NotPos('face tightening: disjoint enclosures')
            acc = SER(cc, L)
        out[i] = acc
    return AS(out, sp, L)


def taylor_model_a(b, f):
    """box AS <- Taylor model in a from the face f, the top a-coefficient from the box b."""
    sp = b.sp
    L = min(b.L, f.L)
    DA = Ctl.DA
    pw = [ONE]
    for l in range(L):
        pw.append(pw[-1] * DA)
    out = [None] * sp.n
    for i in range(sp.n):
        fv, bv = f.s[i], b.s[i]
        if fv is None and bv is None:
            continue
        fc, bc = coefs(fv, L), coefs(bv, L)
        res = []
        for m in range(L):
            acc = ZERO
            for l in range(L - 1 - m):
                acc += fc[m + l] * (comb(m + l, l) * pw[l])
            acc += bc[L - 1] * (comb(L - 1, m) * pw[L - 1 - m])
            if bv is not None:
                try:
                    acc = acc.intersection(bc[m])
                except ValueError:
                    raise NotPos('a-Taylor model: disjoint enclosures')
            res.append(acc)
        out[i] = SER(res, L)
    if out[0] is None:
        out[0] = SER([ZERO], L)
    return AS(out, sp, L)


class T3:
    __slots__ = ('p', 'f', 'b')

    def __init__(self, p, f, b):
        self.p, self.f, self.b = p, f, b

    def __add__(x, y):
        if isinstance(y, T3):
            return T3(x.p + y.p, x.f + y.f, x.b + y.b)
        return T3(x.p + y, x.f + y, x.b + y)
    __radd__ = __add__

    def __neg__(x):
        return T3(-x.p, -x.f, -x.b)

    def __sub__(x, y):
        if isinstance(y, T3):
            return T3(x.p - y.p, x.f - y.f, x.b - y.b)
        return T3(x.p - y, x.f - y, x.b - y)

    def __rsub__(x, y):
        return (-x) + y

    def __mul__(x, y):
        if isinstance(y, T3):
            p = x.p * y.p
            f = tighten_face(x.f * y.f, p)
            b = x.b * y.b
            if Ctl.BOX:
                b = taylor_model_a(b, f)
            return T3(p, f, b)
        return T3(x.p * y, x.f * y, x.b * y)
    __rmul__ = __mul__

    def __truediv__(x, y):
        if isinstance(y, T3):
            return x * y.recip()
        return T3(x.p / y, x.f / y, x.b / y)

    def __rtruediv__(x, y):
        return x.recip() * y

    def _u(x, name):
        f = tighten_face(x.f, x.p)
        b = taylor_model_a(x.b, f) if Ctl.BOX else x.b
        return T3(getattr(x.p, name)(), getattr(f, name)(), getattr(b, name)())

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

    def Phi(x):
        return x._u('Phi')

    def Phihat(x):
        return x._u('Phihat')


def S_t3(X, cx):
    f = tighten_face(X.f, X.p)
    b = taylor_model_a(X.b, f) if Ctl.BOX else X.b
    return T3(S_as(X.p, cx.eps.p, cx.ke), S_as(f, cx.eps.f, cx.ke), S_as(b, cx.eps.b, cx.ke))


def ashift(x, k, check):
    L = x.L - k
    out = []
    for v in x.s:
        if v is None:
            out.append(None)
            continue
        c = coefs(v, x.L)
        if check:
            for i in range(k):
                if not c[i].contains(0):
                    raise NotPos('a-shift: coefficient %d does not contain 0' % i)
        out.append(SER(c[k:], L))
    return AS(out, x.sp, L)


def bshift(x, sp_new, check):
    """divide by b (b-face at 0): slot (j,k) <- slot (j+1,k)."""
    out = [None] * sp_new.n
    for i, (j, k) in enumerate(sp_new.slots):
        out[i] = x.s[x.sp.idx[(j + 1, k)]]
    if check:
        for (j, k) in x.sp.slots:
            if j == 0 and x.s[x.sp.idx[(0, k)]] is not None:
                for c in coefs(x.s[x.sp.idx[(0, k)]], x.L):
                    if not c.contains(0):
                        raise NotPos('b-shift: slot (0,%d) does not vanish' % k)
    if out[0] is None:
        out[0] = SER([ZERO], x.L)
    return AS(out, sp_new, x.L)


def restrict(x, sp):
    return AS([x.s[x.sp.idx[s]] for s in sp.slots], sp, x.L)


class Cx:
    def __init__(self, Ep, Ef, sp, L, ke):
        self.ke = ke
        mk = lambda e: AS.slotvar(e, (0, 1), sp, L) if ke >= 1 else AS.const(e, sp, L)
        self.eps = T3(mk(Ep), mk(Ef), mk(Ef))
        self.e1 = 1 + self.eps
        self.e2 = 1 + 2 * self.eps
        self.c = 2 / self.e1
        self.c2 = 2 / (self.e1 * self.e2)


# ---------------- forms ----------------
LAM = arb(7) / 100


def nu3(Z, cx):
    return 1 / (Z * (-(Z * cx.eps)).phi1())


def P3(Z, cx):
    return (Z * cx.e2).phi1() / (Z * cx.eps).phi1()


def ER_direct(A, B, D, cx, corner_sp=None):
    """E^R = K1 - cap R,  K1 = c (N1/b)/phi(b eps) - e^{(a+b)/3},  N1 = e^{a(1+eps)} P(d) - P(a),
    cap = e^{a/2} b d sqrt(S(b) S(d)) (analytic branch of sqrt(kappa(b) kappa(d))),  R = exp(-(Phi(b) - Phi(d))^2)."""
    N1 = (A * cx.e1).exp() * P3(D, cx) - P3(A, cx)
    if corner_sp is not None:
        Nb = T3(bshift(N1.p, corner_sp, True), bshift(N1.f, corner_sp, False), bshift(N1.b, corner_sp, False))
        A, B, D, cx = (_restrict3(A, corner_sp), _restrict3(B, corner_sp), _restrict3(D, corner_sp),
                       _restrict_cx(cx, corner_sp))
        K1 = cx.c * Nb / (B * cx.eps).phi1() - ((A + B) / 3).exp()
    else:
        K1 = cx.c * N1 / (B * (B * cx.eps).phi1()) - ((A + B) / 3).exp()
    cap = (A / 2).exp() * B * D * (S_t3(B, cx) * S_t3(D, cx)).sqrt()
    dif = B.Phi() - D.Phi()
    R = (-(dif * dif)).exp()
    return K1 - cap * R, (A, B, D, cx)


def _restrict3(x, sp):
    return T3(restrict(x.p, sp), restrict(x.f, sp), restrict(x.b, sp))


def _restrict_cx(cx, sp):
    new = Cx.__new__(Cx)
    new.ke = cx.ke
    for name in ('eps', 'e1', 'e2', 'c', 'c2'):
        setattr(new, name, _restrict3(getattr(cx, name), sp))
    return new


def G_direct(A, B, D, cx, X):
    """Ghat = log(F b/a) = log X - (a+b)/2 - log S(-a)/2 - log S(-b)/2   (W(z) = z^2 e^z S(-z))."""
    return X.log() - (A + B) / 2 - S_t3(-A, cx).log() / 2 - S_t3(-B, cx).log() / 2


def ER_nu(A, B, D, cx, corner_sp=None):
    """Dhat = e^{(1/2+lam) d} D (scaled nu-form with the perfect square; my derivation, see iv_forms.logF_nus)."""
    eps, e2 = cx.eps, cx.e2
    nb, nd = nu3(B, cx), nu3(D, cx)
    sc2 = cx.c2.sqrt()
    yhb, yhd = 1 / (nb * sc2), 1 / (nd * sc2)
    phb = (-(2 * B * eps)).exp() + e2 * (-(B * eps)).exp() / nb
    phd = (-(2 * D * eps)).exp() + e2 * (-(D * eps)).exp() / nd
    ema, ema3 = (-A).exp(), (-(A / 3)).exp()
    emd, emd3 = (-D).exp(), (-(D / 3)).exp()
    ea2 = (-(A * e2)).exp()
    qa = (-(A * e2)).phi1() / (-(A * eps)).phi1()           # nu_a (1 - e^{-a(1+2eps)})/(1+2eps)
    Uh = (-(2 * D * eps)).exp() + e2 * qa * (-(D * eps)).exp() / nd
    emd43 = emd * emd3
    t1 = yhb * ema3 - yhd
    Nt = (t1 * t1 + emd3 * (phb * ema + phd - 2 * Uh) + emd43 * Uh * Uh + 2 * emd * ema3 * Uh * yhb * yhd
          - phb * phd * ema * emd43 - phb * yhd * yhd * ema * emd - phd * yhb * yhb * ema3 * ema3 * emd)
    kh = 1 - emd * Uh - yhb * yhd * ema3 * emd3 * emd3
    Gb = 1 - (-B).exp() * phb - yhb * yhb * (-(2 * B / 3)).exp()
    dmax = D.b.c0().upper()
    if dmax <= 8:
        pz = (-(D * eps)).phi1()
        D2 = D * D
        Gd = D2 * D2 * pz * pz * S_t3(D, cx) * (-D).exp() / cx.c2
    else:
        Gd = 1 - emd * phd - yhd * yhd * emd3 * emd3
    sg = (Gb * Gd).sqrt()
    dif = B.Phihat() * (-(PH.MU * A)).exp() - D.Phihat()
    dif2 = dif * dif
    x = dif2 * (-((2 * PH.MU) * D)).exp()
    return (-((arb(1) / 6 - LAM) * D)).exp() * Nt / (kh + sg) + sg * dif2 * (-x).phi1(), (A, B, D, cx)


def G_nu(A, B, D, cx, X):
    """Ghat = -lam d + log nu_d - log S(-a)/2 + log(c)/2 + (log nu_b - log Om_b)/2 - log(1+2eps) + log X + log b,
    X = Dhat/a^2  (from F = e^{-lam d} nu_d sqrt(nu_b/nu_a) Dhat/((1+2eps) sqrt(Om_a Om_b)) and nu_a Om_a = a^2 S(-a)/c)."""
    nb = nu3(B, cx)
    Ob = 1 - nb * (1 - (-(B * cx.e2)).exp()) / cx.e2 - (-(B / 3)).exp() / (cx.c * nb)
    if A.b.c0().upper() <= 8:
        apart = -S_t3(-A, cx).log() / 2 + cx.c.log() / 2           # = -(log nu_a + log Om_a)/2 + log a
    else:
        na = nu3(A, cx)
        Oa = 1 - na * (1 - (-(A * cx.e2)).exp()) / cx.e2 - (-(A / 3)).exp() / (cx.c * na)
        apart = -(na.log() + Oa.log()) / 2 + A.log()
    return (-LAM * D + nu3(D, cx).log() + apart + (nb.log() - Ob.log()) / 2
            - cx.e2.log() + X.log() + B.log())


FORMS = {'direct': (ER_direct, G_direct), 'nu': (ER_nu, G_nu)}


class Res:
    pass


def evaluate(form, a0, a1, b0, b1, e0, e1, L=16, corner=False, J=10, ke=2):
    """box [a0,a1] x [b0,b1] x [e0,e1] (Fractions); corner=True: b0 = 0, face and centre at b = 0, b-order J."""
    ER, GH = FORMS[form]
    q = lambda x: arb(fmpq(x.numerator, x.denominator))
    sp_big = corner_slots(J + 1) if corner else BODY
    sp_c = corner_slots(J) if corner else None
    a_c = a0 if a0 == 0 else (a0 + a1) / 2
    b_c = b0 if corner else (b0 + b1) / 2
    e_c = (e0 + e1) / 2
    Ctl.DA = arb.union(q(a0 - a_c), q(a1 - a_c))
    Ctl.DB = arb.union(q(b0 - b_c), q(b1 - b_c)) if b1 > b0 else ZERO
    Ctl.DE = arb.union(q(e0 - e_c), q(e1 - e_c)) if e1 > e0 else ZERO
    Ab = arb.union(q(a0), q(a1)) if a1 > a0 else q(a0)
    Bb = arb.union(q(b0), q(b1)) if b1 > b0 else q(b0)
    Eb = arb.union(q(e0), q(e1)) if e1 > e0 else q(e0)
    A = T3(AS.avar(q(a_c), sp_big, L), AS.avar(q(a_c), sp_big, L), AS.avar(Ab, sp_big, L))
    B = T3(AS.slotvar(q(b_c), (1, 0), sp_big, L), AS.slotvar(Bb, (1, 0), sp_big, L), AS.slotvar(Bb, (1, 0), sp_big, L))
    D = B - A
    cx = Cx(q(e_c), Eb, sp_big, L, ke)
    E, (A, B, D, cx) = ER(A, B, D, cx, corner_sp=sp_c)
    if a_c == 0:
        X = T3(ashift(E.p, 2, True), ashift(E.f, 2, True), ashift(E.b, 2, False))
        A, B, D = _shorten(A, 2), _shorten(B, 2), _shorten(D, 2)
        cx = _shorten_cx(cx, 2)
    else:
        X = E / (A * A)
    Xf = tighten_face(X.f, X.p)
    X = T3(X.p, Xf, taylor_model_a(X.b, Xf))
    G = GH(A, B, D, cx, X)
    r = Res()
    r.G, r.X = G, X
    r.a0, r.a1, r.b0, r.b1 = a0, a1, b0, b1
    return r


def _shorten(x, k):
    L = x.p.L - k
    cut = lambda s: AS([None if v is None else SER(coefs(v, s.L)[:L], L) for v in s.s], s.sp, L)
    return T3(cut(x.p), cut(x.f), cut(x.b))


def _shorten_cx(cx, k):
    new = Cx.__new__(Cx)
    new.ke = cx.ke
    for name in ('eps', 'e1', 'e2', 'c', 'c2'):
        setattr(new, name, _shorten(getattr(cx, name), k))
    return new


def coef_on_box(r, i, j):
    """enclosure on the box of the Taylor coefficient (a^i, b^j) of Ghat: face coefficients tightened (Taylor in b,
    mean value in eps), then the Taylor model in a with the top coefficient from the box."""
    G = r.G
    sp = G.f.sp
    f = tighten_face(G.f, G.p)
    L = f.L
    fc = coefs(f.s[sp.idx[(j, 0)]], L)
    bc = coefs(G.b.s[sp.idx[(j, 0)]], L)
    DA = Ctl.DA
    acc = ZERO
    pw = ONE
    for l in range(L - 1 - i):
        acc += fc[i + l] * (comb(i + l, l) * pw)
        pw = pw * DA
    acc += bc[L - 1] * (comb(L - 1, i) * pw)
    return acc


def conditions(r):
    """a L1 = 1 + a Ghat_a,  L2: 1 - b Ghat_b (b L2) or 1/b - Ghat_b,  L3: 1 - b Ghat_b + a Ghat_a - a b (Ghat_ab + Ghat_a Ghat_b)
    (a b L3) or N2 - a (Ghat_ab + Ghat_a (Ghat_b - 1/b)) (a L3); X > 0 on the box."""
    q = lambda x: arb(fmpq(x.numerator, x.denominator))
    ga, gb, gab = coef_on_box(r, 1, 0), coef_on_box(r, 0, 1), coef_on_box(r, 1, 1)
    ar = arb.union(q(r.a0), q(r.a1)) if r.a1 > r.a0 else q(r.a0)
    br = arb.union(q(r.b0), q(r.b1)) if r.b1 > r.b0 else q(r.b0)
    M1 = 1 + ar * ga
    M2 = 1 - br * gb
    M3 = 1 - br * gb + ar * ga - ar * br * (gab + ga * gb)
    out = {'aL1': M1, 'bL2': M2, 'abL3': M3}
    ok2, ok3 = M2 > 0, M3 > 0
    if br > 0:
        ib = 1 / br
        N2 = ib - gb
        N3 = N2 - ar * (gab + ga * (gb - ib))
        out['L2'], out['aL3'] = N2, N3
        ok2 = ok2 or N2 > 0
        ok3 = ok3 or N3 > 0
    xpos = r.X.b.c0() > 0
    return (M1 > 0) and ok2 and ok3 and xpos, out


def coef_with_contrib(r, i, j):
    """as coef_on_box (same enclosure, computed from the same face/Taylor-model formula), with the widths attributed
    to the b-direction, the eps-direction and the a-direction (used only to choose the bisection direction)."""
    G = r.G
    sp = G.f.sp
    L = G.f.L
    p, f, b = G.p, G.f, G.b
    DA, DB, DE = Ctl.DA, Ctl.DB, Ctl.DE
    eb, ee = not (DB == 0), not (DE == 0)
    Q = sp.rows[0] - j
    ie = sp.idx.get((j, 1))
    pc = {jj: coefs(p.s[sp.idx[(jj, 0)]], L) for jj in range(j, sp.rows[0] + 1)}
    ftop = coefs(f.s[sp.idx[(sp.rows[0], 0)]], L)
    fe = coefs(f.s[ie], L) if ie is not None else None
    fj = coefs(f.s[sp.idx[(j, 0)]], L)
    face, ry, re_ = [], [], []
    plain = (eb and Q == 0) or (ee and fe is None)
    for m in range(L):
        if plain:
            face.append(fj[m])
            ry.append(float(fj[m].rad()))
            re_.append(0.0)
            continue
        ty = ZERO
        if eb:
            pw = ONE
            for qq in range(1, Q):
                pw = pw * DB
                ty += pc[j + qq][m] * (comb(j + qq, qq) * pw)
            ty += ftop[m] * (comb(j + Q, Q) * pw * DB)
        te = fe[m] * DE if ee else ZERO
        v = pc[j][m] + ty + te
        try:
            v = v.intersection(fj[m])
        except ValueError:
            raise NotPos('final coefficient: disjoint enclosures')
        face.append(v)
        ry.append(float(ty.rad()))
        re_.append(float(te.rad()))
    bc = coefs(b.s[sp.idx[(j, 0)]], L)
    acc, cy, ce = ZERO, 0.0, 0.0
    pw = ONE
    for l in range(L - 1 - i):
        w = comb(i + l, l) * pw
        acc += face[i + l] * w
        mag = float(abs(w).upper())
        cy += ry[i + l] * mag
        ce += re_[i + l] * mag
        pw = pw * DA
    acc += bc[L - 1] * (comb(L - 1, i) * pw)
    ca = max(float(acc.rad()) - cy - ce, 0.0)
    return acc, (cy, ce, ca)


def conditions_c(r):
    """the conditions of conditions(), with enclosures from coef_with_contrib, plus the summed width contributions
    (b, eps, a) for the bisection heuristic."""
    q = lambda x: arb(fmpq(x.numerator, x.denominator))
    (ga, c1), (gb, c2), (gab, c3) = coef_with_contrib(r, 1, 0), coef_with_contrib(r, 0, 1), coef_with_contrib(r, 1, 1)
    ar = arb.union(q(r.a0), q(r.a1)) if r.a1 > r.a0 else q(r.a0)
    br = arb.union(q(r.b0), q(r.b1)) if r.b1 > r.b0 else q(r.b0)
    M1 = 1 + ar * ga
    M2 = 1 - br * gb
    M3 = 1 - br * gb + ar * ga - ar * br * (gab + ga * gb)
    out = {'aL1': M1, 'bL2': M2, 'abL3': M3}
    ok2, ok3 = M2 > 0, M3 > 0
    if br > 0:
        ib = 1 / br
        N2 = ib - gb
        N3 = N2 - ar * (gab + ga * (gb - ib))
        out['L2'], out['aL3'] = N2, N3
        ok2 = ok2 or N2 > 0
        ok3 = ok3 or N3 > 0
    xpos = r.X.b.c0() > 0
    a1 = float(r.a1)
    contrib = [a1 * c1[t] + c2[t] + a1 * c3[t] for t in range(3)]
    return (M1 > 0) and ok2 and ok3 and xpos, out, contrib
