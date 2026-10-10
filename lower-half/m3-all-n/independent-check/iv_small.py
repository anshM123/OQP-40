"""Independent verifier, part 7: small-argument pieces (own implementation).

S(x; eps) = kappa_n(x)/x^2 = sum_{k>=2} s_k(eps) x^{k-2},  s_k = 2 sum_{i+j=k} psi_i beta_j eps^j - 1/(3^k k!),
  psi_i = h_i(eps, 1+2eps)/(i+2)!,  (z/(e^z-1))^2 = sum_j beta_j z^j   (re-derived: kappa_n = 2 [x eps, x(1+2eps)]phi
  / phi(x eps)^2 - e^{x/3}).  Exact rational polynomial coefficients in eps for k <= NS; tail k > NS: for real eps in
  [0, 1/37] and the eps-Taylor coefficient of order q, |s_k^[q](eps)| <= 37^q T_k (Cauchy on |zeta - eps| <= 1/37,
  |zeta| <= 2/37), T_k = 26 sum_{i<=k} (41/37)^i/(i+1)! (2/37)^{k-i} + 1/(3^k k!)  (|beta_j| <= 13 from Cauchy on
  |z| = 1 where |phi(z)| >= 3 - e; |psi_i(zeta)| <= (i+1) (41/37)^i/(i+2)! <= (41/37)^i/(i+1)!).
Phi for |z| <= 2: rr = (A1 + Lq)/sqrt(kh/2), A1 = (2 sinh(z/2)/z - 1)/z, Lq = (1 - e^{-lam z})/z, kh = kappa_inf/z^2,
  power series with |coefficient_k| <= C/k! (C = 1, 1, 3) and the tail bound
  sum_{k>N} C(k,m) h^{k-m} C/k! <= C h^{N+1-m} e^h/(m! (N+1-m)!).
"""
from math import comb, factorial, ceil, floor
import flint
from flint import arb, fmpq, fmpq_poly, arb_series
import iv_jet as JJ
from iv_jet import Jet, NotPos, ZERO, ONE

NS = 100
LAM_Q = fmpq(7, 100)
ETA = arb(7) / 10
LAM = arb(7) / 100


def _beta(N):
    # 1/phi(z) = z/(e^z - 1) = sum b_k z^k  (Bernoulli), then square
    p = [fmpq(1, factorial(k + 1)) for k in range(N + 1)]
    inv = [fmpq(0)] * (N + 1)
    inv[0] = fmpq(1)
    for k in range(1, N + 1):
        inv[k] = -sum((p[i] * inv[k - i] for i in range(1, k + 1)), fmpq(0))
    return [sum((inv[i] * inv[k - i] for i in range(k + 1)), fmpq(0)) for k in range(N + 1)]


BETA = _beta(NS)


def _s_polys():
    """s_k(eps) as exact rational polynomials (fmpq_poly in eps), k = 0..NS."""
    E = fmpq_poly([0, 1])
    V = fmpq_poly([1, 2])
    h = [fmpq_poly([1])]
    for i in range(1, NS + 1):
        h.append(V * h[-1] + E ** i)
    out = []
    for k in range(NS + 1):
        acc = fmpq_poly([0])
        for i in range(k + 1):
            j = k - i
            acc += h[i] * fmpq_poly([fmpq(1, factorial(i + 2))]) * fmpq_poly([BETA[j]]) * E ** j
        out.append(2 * acc - fmpq_poly([fmpq(1, 3 ** k * factorial(k))]))
    return out


SPOLY = _s_polys()
assert SPOLY[0] == 0 and SPOLY[1] == 0
_TK = None


def _tk():
    global _TK
    if _TK is None:
        v, e = arb(41) / 37, arb(2) / 37
        vp, ep = [ONE], [ONE]
        for i in range(700):
            vp.append(vp[-1] * v)
            ep.append(ep[-1] * e)
        _TK = {}
        for k in range(NS + 1, 701):
            t = ZERO
            for i in range(k + 1):
                t += vp[i] / factorial(i + 1) * ep[k - i]
            _TK[k] = 26 * t + arb(fmpq(1, 3 ** k * factorial(k)))
    return _TK


_TAIL = {}


def _s_tail(hq, m, q):
    """bound of sum_{k>NS} |s_k^[q]| C(k-2, m) h^(k-2-m), h = hq/16 <= 8; terms k > 700 are < 1e-200 (ratio <= 0.45)."""
    key = (hq, m, q)
    if key not in _TAIL:
        h = arb(fmpq(hq, 16))
        T = _tk()
        s = ZERO
        for k in range(NS + 1, 701):
            if k - 2 - m >= 0:
                s += T[k] * arb(37) ** q * comb(k - 2, m) * h ** (k - 2 - m)
        _TAIL[key] = s.upper() + arb('1e-200')
    return _TAIL[key]


def _seps(e0, Q):
    """[q][k]: eps-Taylor coefficient of order q of s_k at every eps of the ball e0 (centred form for wide balls)."""
    def raw(e, QQ):
        out = [[ZERO] * (NS + 1) for _ in range(QQ + 1)]
        for q in range(QQ + 1):
            dl = _sder(q)
            for k in range(2, NS + 1):
                out[q][k] = _eval_poly(dl[k], e) / factorial(q)
        return out
    if e0.rad() == 0:
        return raw(e0, Q)
    mid = arb(e0.mid())
    cm = raw(mid, Q)
    cb = raw(e0, Q + 1)
    r = arb(0, e0.rad())
    return [[cm[q][k] + (q + 1) * cb[q + 1][k] * r for k in range(NS + 1)] for q in range(Q + 1)]


_SDER = {}


def _sder(q):
    """[k] -> q-th derivative of the exact polynomial s_k(eps) (computed once)."""
    if q not in _SDER:
        out = []
        for k in range(NS + 1):
            dq = SPOLY[k]
            for _ in range(q):
                dq = dq.derivative()
            out.append(dq)
        _SDER[q] = out
    return _SDER[q]


def _eval_poly(p, x):
    c = p.coeffs()
    acc = ZERO
    for co in reversed(c):
        acc = acc * x + arb(co)
    return acc


_SE_CACHE = {}


def S_coeffs(x0, e0, M, Q):
    """c[m][q] = (1/(m! q!)) d_x^m d_eps^q S at every point of x0 x e0 (|x0| <= 8, e0 within [0, 1/37])."""
    if not (e0.lower() >= -1e-9 and e0.upper() <= arb(1) / 37 + arb('1e-9')):   # true eps lie in [0, 1/37]; balls may stick out by arb radius rounding
        raise NotPos('S: eps outside [0, 1/37]')
    h = abs(x0).upper()
    if not (h <= 8):
        raise NotPos('S: |x| > 8')
    key = (e0.mid().str(40, radius=False), e0.rad().str(5, radius=False), Q)
    if key not in _SE_CACHE:
        _SE_CACHE[key] = _seps(e0, Q)
    se = _SE_CACHE[key]

    def raw(xb, MM):
        hq = int(ceil(float(abs(xb).upper()) * 16 + 1e-9))
        out = [[None] * (Q + 1) for _ in range(MM + 1)]
        flint.ctx.cap = MM + 1
        X = arb_series([xb, 1], prec=MM + 1)
        for q in range(Q + 1):
            acc = arb_series([se[q][NS]], prec=MM + 1)
            for k in range(NS - 1, 1, -1):
                acc = acc * X + se[q][k]
            c = acc.coeffs()
            for m in range(MM + 1):
                cm = c[m] if m < len(c) else ZERO
                out[m][q] = cm + arb(0, _s_tail(hq, m, q))
        return out
    if x0.rad() < 1e-40:
        return raw(x0, M)
    mid = arb(x0.mid())
    cmid = raw(mid, M)
    cbox = raw(x0, M + 1)
    r = arb(0, x0.rad())
    return [[cmid[m][q] + (m + 1) * cbox[m + 1][q] * r for q in range(Q + 1)] for m in range(M + 1)]


def S_jet(X, E):
    """the jet of S(X; E) (X, E plain jets; E = the eps jet variable, X any jet with |X| <= 8)."""
    sp = X.sp
    M = sp.order
    Q = max(m[2] for m in sp.monos)
    c = S_coeffs(X.c[0], E.c[0], M, Q)
    dX = Jet([ZERO] + X.c[1:], sp)
    dE = Jet([ZERO] + E.c[1:], sp)
    pX = [Jet.const(ONE, sp)]
    for m in range(M):
        pX.append(pX[-1] * dX)
    pE = [Jet.const(ONE, sp)]
    for q in range(Q):
        pE.append(pE[-1] * dE)
    res = Jet.const(ZERO, sp)
    for q in range(Q + 1):
        inner = Jet.const(ZERO, sp)
        for m in range(M, -1, -1):
            inner = inner + pX[m] * c[m][q]
        res = res + (inner * pE[q] if q else inner)
    return res


def S_of(X, E):
    """S for plain jets or centre/box pairs (iv_dual.TJ)."""
    import iv_dual as DU
    if not isinstance(E, (Jet, DU.TJ)):          # eps given as a plain ball (no eps-jet): constant jet
        E = Jet.const(E, X.sp) if isinstance(X, Jet) else DU.TJ(Jet.const(E, X.c.sp), Jet.const(E, X.b.sp))
    if isinstance(X, DU.TJ):
        Eb = E.b if isinstance(E, DU.TJ) else E
        Ec = E.c if isinstance(E, DU.TJ) else E
        return DU.TJ(S_jet(X.c, Ec), S_jet(DU.tighten(X.b, X.c), Eb))
    return S_jet(X, E)


# ---------------- Phi for |z| <= 2 (series) ----------------
NPH = 80
C_A1 = [fmpq(1, 4 ** ((k + 1) // 2) * factorial(k + 2)) if k % 2 == 1 else fmpq(0) for k in range(NPH + 1)]
C_LQ = [fmpq((-1) ** k) * LAM_Q ** (k + 1) / factorial(k + 1) for k in range(NPH + 1)]
C_KH = [fmpq(2, factorial(k + 4)) - fmpq(1, 3 ** (k + 2) * factorial(k + 2)) for k in range(NPH + 1)]


def _series_with_tail(coefs, C, z0, L):
    """power series (length L) at the ball z0 of sum_k coefs[k] z^k with |coefs_k| <= C/k! beyond NPH."""
    h = abs(z0).upper()
    flint.ctx.cap = L
    X = arb_series([z0, 1], prec=L)
    acc = arb_series([arb(coefs[-1])], prec=L)
    for k in range(len(coefs) - 2, -1, -1):
        acc = acc * X + arb(coefs[k])
    c = acc.coeffs()
    out = []
    for m in range(L):
        cm = c[m] if m < len(c) else ZERO
        tail = C * arb(h) ** (NPH + 1 - m) * arb(h).exp() / (factorial(m) * factorial(NPH + 1 - m))
        out.append(cm + arb(0, tail.upper()))
    return arb_series(out, prec=L)


def phi_small_series(z0, K):
    """Taylor coefficients 0..K of Phi(z) = -sqrt(-log(1 - eta (1 - rr(z)))) at a ball z0 with |z0| <= 2.1."""
    if not (abs(z0).upper() <= 2.1):
        raise NotPos('phi_small: |z| > 2.1')
    L = K + 1
    A1 = _series_with_tail(C_A1, 1, z0, L)
    Lq = _series_with_tail(C_LQ, 1, z0, L)
    kh = _series_with_tail(C_KH, 3, z0, L)
    if not (kh.coeffs()[0] > 0):
        raise NotPos('phi_small: kh')
    rr = (A1 + Lq) / (kh / 2).sqrt()
    y = ETA * (1 - rr)
    y0 = y.coeffs()[0]
    if not (y0 > 0 and y0 < 1):
        raise NotPos('phi_small: y')
    g = -((1 - y).log())
    if not (g.coeffs()[0] > 0):
        raise NotPos('phi_small: g')
    res = -(g.sqrt())
    c = res.coeffs()
    return [c[i] if i < len(c) else ZERO for i in range(L)]


_PC = {}


def _pcell(lo, hi, K):
    key = (lo, hi, K)
    if key in _PC:
        return _PC[key]
    mid, r = (lo + hi) / 2, (hi - lo) / 2
    cm = phi_small_series(arb(mid), K)
    cb = phi_small_series(arb.union(arb(lo), arb(hi)), K + 1)
    out = [cm[j] + (j + 1) * cb[j + 1] * arb(0, arb(r)) for j in range(K + 1)]
    _PC[key] = out
    return out


def c_phi_small(z0, K):
    if z0.rad() < 1e-40:
        return phi_small_series(z0, K)
    lo, hi = z0.lower(), z0.upper()
    k0 = int(floor(float(lo) * 128)) - 1
    k1 = int(floor(float(hi) * 128)) + 1
    if k0 < -64 or k1 > 2 * 128 + 4:
        raise NotPos('phi_small cells out of range')
    parts = [_pcell(fmpq(k, 128), fmpq(k + 1, 128), K) for k in range(k0, k1 + 1)]
    out = parts[0]
    for p in parts[1:]:
        out = [arb.union(x, y) for x, y in zip(out, p)]
    return out


def Phi_any(z):
    """Phi at a jet / TJ z: series branch if the ball lies in [-1/2, 2], else Phihat e^{-mu z} (needs z >= 2)."""
    import iv_dual as DU
    import iv_phi
    z0 = z.ball() if isinstance(z, DU.TJ) else z.c[0]
    if z0.upper() <= 2 and z0.lower() >= -0.5:
        if isinstance(z, DU.TJ):
            return z._u('phismall')
        return z.compose(c_phi_small(z0, z.sp.order))
    if z0.lower() >= 1.8 or (z0.rad() < 1e-40 and z0 > 0):
        return z.phihat() * (-(iv_phi.MU * z)).exp()
    raise NotPos('Phi_any: ball straddles 2')
