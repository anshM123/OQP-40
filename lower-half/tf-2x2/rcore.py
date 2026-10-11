"""Rigorous (Arb ball arithmetic, python-flint) core for the closed-form inequality (C) of the 2x2 TF proof.
Ansh Mishra, Aryan Senthilkumar.

Coordinates (theta, a, c, w): A = e^{a xhat.sigma}, B = e^{b yhat.sigma}, xhat.yhat = w, b = theta c/(1-theta)
(so c = r b, r = (1-theta)/theta).  RE := |a xhat + c yhat| = sqrt(a^2 + c^2 + 2acw)  (= N0 * rho).

  eps_P = 8 a^2 c^2 (1-w^2) Ch[z-, z, z+],            z- = (a-c)^2, z = RE^2, z+ = (a+c)^2,  Ch(z) = cosh(sqrt z)
  eps_G = 2 (1-w^2) [ sinh^2 a sinh^2 b V[C-, C, C+] - 4 theta^4 a^2 c^2 Ch[theta^2 z-, theta^2 z, theta^2 z+] ],
          C- = cosh(a-b), C = cosh a cosh b - w sinh a sinh b, C+ = cosh(a+b),
          V(C) = U_theta(C) cosh a + U_{1-theta}(C) cosh b,  U_t(C) = sinh(t d)/sinh(d), C = cosh d.
  E_P = eps_P/((1-w^2)a^2c^2),  E_G = eps_G/((1-w^2)a^2b^2) = 2[S_a S_b V[..] - 4 th^2 (1-th)^2 Ch[..]],
  S_a = (sinh a/a)^2,  X_P = e^{RE} eps_P,  Y_G = e^{-theta RE} eps_G,
  F = theta log(1+X_P) + log(1-Y_G) = theta (1-w^2) a^2 c^2 R,
  R = e^{RE} E_P phi1(X_P) - theta/(1-theta)^2 e^{-theta RE} E_G phi2(Y_G),
  phi1(X) = log(1+X)/X (decreasing), phi2(Y) = -log(1-Y)/Y (increasing).
(C) <=> F >= 0 <=> R >= 0 (where (1-w^2)a^2c^2 > 0).

Facts used for the enclosures (PROVED in PROOF.md):
  (M1) Ch has positive Taylor coefficients: Ch[x_1..x_m] = sum_n h_{n-m+1}(x)/(2n)!, increasing in each node x_i >= 0.
  (M2) U_t(C) = (sin(pi t)/pi) int_0^inf lam^{-t} dlam/(1 + 2 C lam + lam^2) (0 < t < 1); hence
       U_t[x0,x1,x2] = (sin(pi t)/pi) int lam^{-t} (2 lam)^2 / prod_i (1 + 2 x_i lam + lam^2) dlam > 0 is
       DEcreasing in each node x_i >= 1.
  (M3) U_t(1+y) = t sum_k q_k(t) (-2y)^k, q_k(t) = prod_{j=1}^k (j^2 - t^2)/(2k+1)!, |q_k| <= 4^{-k} (|t| <= 1).
  Mean value theorem in theta for the U-terms (centred form).
"""
from math import comb, lgamma, log, exp
from flint import arb, arb_series, ctx

ctx.prec = 160

_FACT = [arb(1)]
for _k in range(1, 900):
    _FACT.append(_FACT[-1] * _k)


def fact(n):
    return _FACT[n]


def iv(lo, hi):
    """Ball containing the closed interval [lo, hi] (lo, hi exact binary numbers or arb)."""
    return arb(lo).union(arb(hi))


def clamp_ge(x, v):
    """Intersect the ball x with [v, +inf) (v exact).  Raises if x lies entirely below v."""
    v = arb(v)
    if x.upper() < v:
        raise ValueError("ball entirely below clamp value")
    if x.lower() < v:
        return v.union(x.upper())
    return x


def meet(x, y):
    """Intersection of two balls known to contain the same quantity."""
    lo = x.lower() if x.lower() > y.lower() else y.lower()
    hi = x.upper() if x.upper() < y.upper() else y.upper()
    if lo > hi:
        raise ValueError("empty intersection")
    return lo.union(hi)


def _up(x):
    """A Python float >= every point of the ball x."""
    u = float(x.upper())
    return u * (1 + 2.0 ** -40) + 2.0 ** -1000 if u >= 0 else u * (1 - 2.0 ** -40) + 2.0 ** -1000


def hull(*xs):
    out = xs[0]
    for x in xs[1:]:
        out = out.union(x)
    return out


# ------------------------------------------------------------------ Ch divided differences (positive series)

def ch_dd(nodes):
    """Ch[x_1, ..., x_m] for Ch(z) = cosh(sqrt z) = sum z^n/(2n)!; nodes = balls (|x_i| <= M).
    = sum_{n >= m-1} h_{n-m+1}(x_1..x_m)/(2n)!; tail bounded with |h_k| <= C(k+m-1, m-1) M^k."""
    m = len(nodes)
    M = max(_up(abs(x)) for x in nodes)
    prev = [arb(1)] * m
    total = arb(0)
    n = m - 1
    while True:
        total = total + prev[0] / fact(2 * n)
        nn = n + 1
        if M == 0:
            return total
        lt = log(comb(nn, m - 1)) + (nn - m + 1) * log(M) - lgamma(2 * nn + 1)
        q = (nn + 1) / max(nn - m + 2, 1) * M / ((2 * nn + 1) * (2 * nn + 2))
        if q < 0.5 and lt < -ctx.prec * 0.75 - 30:
            return total + arb(0, exp(lt) * 2.0 * (1 + 2.0 ** -30))
        new = [None] * m
        for j in range(m - 1, -1, -1):
            new[j] = nodes[j] * prev[j] if j == m - 1 else new[j + 1] + nodes[j] * prev[j]
        prev = new
        n += 1
        if n > 850:
            raise RuntimeError("ch_dd: too many terms")


# ------------------------------------------------------------------ U_t(C) = sinh(t d)/sinh(d), C = cosh d

def _tq(t, K, dt):
    """coef_k = t q_k(t) (dt=False) or d/dt [t q_k(t)] (dt=True), k = 0..K.  Bounds (|t| <= 1):
    |t q_k| <= 4^{-k},  |d/dt (t q_k)| <= (1+2k) 4^{-k}."""
    out = []
    p = arb(1)
    dp = arb(0)
    for k in range(K + 1):
        if k > 0:
            f = k * k - t * t
            dp = dp * f + p * (-2 * t)
            p = p * f
        if dt:
            out.append((p + t * dp) / fact(2 * k + 1))
        else:
            out.append(t * p / fact(2 * k + 1))
    return out


def _useries_derivs(t, y, nder, dt):
    """d^j/dy^j of sum_k coef_k (-2y)^k for j = 0..nder, y a ball in [0, 1/2]; tail bound:
    |coef_k| 2^k k^j Y^{k-j} <= (1+2k) 2^{-k} k^j Y^{k-j}."""
    Y = _up(y)
    assert Y <= 0.5 + 2.0 ** -18
    K = 30
    while K < 800:
        kk = K + 1
        if (1 + 2 * kk) * 0.5 ** kk * kk ** nder * (Y ** (kk - nder) if Y > 0 else 0.0) < 2.0 ** (-ctx.prec - 20):
            break
        K += 20
    co = _tq(t, K, dt)
    res = []
    for j in range(nder + 1):
        s = arb(0)
        for k in range(j, K + 1):
            s = s + co[k] * (arb(-2) ** k) * (fact(k) / fact(k - j)) * (y ** (k - j))
        kk = K + 1
        first = (1 + 2 * kk) * 0.5 ** kk * kk ** j * (Y ** (kk - j) if Y > 0 else 0.0)
        r = (Y / 2.0) * (1 + 1.0 / K) ** j * (1 + 2.0 / (1 + 2 * kk))
        res.append(s + arb(0, first / (1 - r) * (1 + 2.0 ** -20) + 2.0 ** -1000))
    return res


def _uclosed_derivs(t, C, nder, dt):
    """Taylor coefficients (times j!) at the ball C (lower > 1) of sinh(t d)/sinh d or of
    d cosh(t d)/sinh d  (= d/dt of the former), d = log(C + sqrt(C^2-1))."""
    n = nder + 1
    s = arb_series([C, 1], prec=n)
    d = (s + (s * s - 1).sqrt()).log()
    etd, emtd = (t * d).exp(), (-t * d).exp()
    den = d.exp() - (-d).exp()
    if dt:
        f = d * (etd + emtd) / den
    else:
        f = (etd - emtd) / den
    co = f.coeffs()
    while len(co) < n:
        co.append(arb(0))
    return [co[j] * fact(j) for j in range(n)]


def uf_derivs(t, C, nder, dt=False):
    """Enclosures over the ball C (>= 1) of the C-derivatives 0..nder of U_t (dt=False) or of d/dt U_t.
    Series (M3) when C <= 1.5 (+ rounding slack), closed form when C > 1.25, otherwise split at 1.375."""
    if C.upper() <= 1.5 + 2.0 ** -20:
        y = C - 1
        if y.lower() < 0:
            y = arb(0).union(y.upper())
        return _useries_derivs(t, y, nder, dt)
    if C.lower() > 1.25:
        return _uclosed_derivs(t, C, nder, dt)
    lo = _useries_derivs(t, clamp_ge(C - 1, 0).lower().union(arb(0.375)), nder, dt)
    hi = _uclosed_derivs(t, arb(1.375).union(C.upper()), nder, dt)
    return [x.union(y) for x, y in zip(lo, hi)]


def _useries_dd3(t, ys, dt):
    """sum_{k>=2} coef_k (-2)^k h_{k-2}(y0,y1,y2) for y_i in [0, 1/2]; tail |coef_k 2^k h_{k-2}| <=
    (1+2k) 2^{-k} C(k,2) Y^{k-2}."""
    Y = max(_up(y) for y in ys)
    K = 40
    while K < 800 and (1 + 2 * K) * (K + 1) ** 2 * (Y / 2.0) ** (K - 1) > 2.0 ** (-ctx.prec - 20):
        K += 20
    co = _tq(t, K, dt)
    m = 3
    prev = [arb(1)] * m
    s = arb(0)
    for k in range(2, K + 1):
        s = s + co[k] * (arb(-2) ** k) * prev[0]
        new = [None] * m
        for j in range(m - 1, -1, -1):
            new[j] = ys[j] * prev[j] if j == m - 1 else new[j + 1] + ys[j] * prev[j]
        prev = new
    kk = K + 1
    first = (1 + 2 * kk) * kk * (kk - 1) / 2 * Y ** (kk - 2) * 0.5 ** kk
    r = (Y / 2.0) * ((kk + 1) / (kk - 1)) * (1 + 2.0 / (1 + 2 * kk))
    return s + arb(0, first / (1 - r) * (1 + 2.0 ** -20) + 2.0 ** -1000)


def dd3_point(fd, x0, x1, x2, tau=2.0 ** -24):
    """Second divided difference f[x0,x1,x2] at near-point nodes; fd(ball, nder) returns enclosures of
    f, f', ... over the ball.  A pair of nodes is 'close' if its gap is <= tau*(1 + smaller node); close pairs are
    handled by the mean value theorem on their hull (f[xa,xb] in f'(hull), f[x0,x1,x2] in f''(hull)/2)."""
    xs = sorted([x0, x1, x2], key=lambda z: float(z.mid()))
    x0, x1, x2 = xs
    g01 = float((x1 - x0).mid())
    g12 = float((x2 - x1).mid())
    c01 = g01 <= tau * (1.0 + abs(float(x0.mid())))
    c12 = g12 <= tau * (1.0 + abs(float(x1.mid())))
    if c01 and c12:
        return fd(hull(x0, x2), 2)[2] / 2

    def d1(xa, xb, close):
        if close:
            return fd(hull(xa, xb), 1)[1]
        return (fd(xb, 0)[0] - fd(xa, 0)[0]) / (xb - xa)

    return (d1(x1, x2, c12) - d1(x0, x1, c01)) / (x2 - x0)


def u_dd_point(t, nodes, dt=False):
    """U_t[x0,x1,x2] (or (d/dt U_t)[x0,x1,x2]) at near-point nodes >= 1."""
    if max(_up(x) for x in nodes) <= 1.5:
        ys = []
        for x in nodes:
            y = x - 1
            ys.append(arb(0).union(y.upper()) if y.lower() < 0 else y)
        return _useries_dd3(t, ys, dt)
    return dd3_point(lambda C, n: uf_derivs(t, C, n, dt), *nodes)


def u_dd_box(TH, X0, X1, X2, flip=False):
    """Enclosure of U_t[x0,x1,x2] over t = theta in TH (or t = 1-theta if flip) and x_i in the balls X_i (>= 1).
    Uses (M2) (decreasing in each node) and the mean value theorem in theta around the midpoint of TH."""
    one = arb(1)
    lo_nodes = [X.lower() if X.lower() > one else one for X in (X0, X1, X2)]
    hi_nodes = [X.upper() if X.upper() > one else one for X in (X0, X1, X2)]
    thm = arb(TH.mid())
    thr = TH.rad()
    tm = (1 - thm) if flip else thm
    tb = (1 - TH) if flip else TH
    vals = []
    for nodes in (lo_nodes, hi_nodes):
        nodes = [arb(x) for x in nodes]
        v0 = u_dd_point(tm, nodes)
        if thr.is_zero():
            vals.append(v0)
        else:
            D = u_dd_point(tb, nodes, dt=True)
            vals.append(v0 + arb(0, thr.upper()) * D)
    return vals[0].union(vals[1])


# ------------------------------------------------------------------ small helpers

def shc(x):
    """sinh(x)/x for a ball x: series for |x| <= 1, else direct (x bounded away from 0)."""
    X = _up(abs(x))
    if X <= 1.0:
        s = arb(0)
        x2 = x * x
        term = arb(1)
        for k in range(0, 40):
            s = s + term / fact(2 * k + 1)
            term = term * x2
        return s + arb(0, X ** 80 / float(fact(81).mid()) * 2.0)
    if x.lower() > 0.5:
        return x.sinh() / x
    return shc(arb(0).union(arb(0.75))).union(shc(arb(0.75).union(x.upper())))


def phi1_box(X):
    """phi1(X) = log(1+X)/X, decreasing on X > -1, phi1(0) = 1."""
    def pt(x):
        xa = _up(abs(x))
        if xa < 1e-6:
            return 1 - x / 2 + arb(0, xa * xa / 3 / (1 - xa) * 1.0001)
        return (1 + x).log() / x
    return pt(arb(X.upper())).union(pt(arb(X.lower())))


def phi2_box(Y):
    """phi2(Y) = -log(1-Y)/Y, increasing on Y < 1, phi2(0) = 1."""
    def pt(y):
        ya = _up(abs(y))
        if ya < 1e-6:
            return 1 + y / 2 + arb(0, ya * ya / 3 / (1 - ya) * 1.0001)
        return -(1 - y).log() / y
    return pt(arb(Y.lower())).union(pt(arb(Y.upper())))


# ------------------------------------------------------------------ the normalised margin R on a box

def R_box(TH, A, Cc, W, want=False):
    """Enclosure of R over the box TH x A x Cc x W (balls; TH within [0, 1/2], A, Cc >= 0, W within [-1, 1]).
    Returns (R, epsP[, parts]).  R = arb(0, 1e300) signals an uninformative enclosure."""
    th = TH
    a = clamp_ge(A, 0)
    c = clamp_ge(Cc, 0)
    w = W
    b = th * c / (1 - th)
    opw = clamp_ge(1 + w, 0)
    omw = clamp_ge(1 - w, 0)
    zm = clamp_ge((a - c) * (a - c), 0)
    zp = (a + c) * (a + c)
    # z = (a-c)^2 + 2ac(1+w) = (a+c)^2 - 2ac(1-w)
    z = meet(clamp_ge(zm + 2 * a * c * opw, 0), clamp_ge(zp - 2 * a * c * omw, 0))
    RE = z.sqrt()
    EP = 8 * ch_dd([zm, z, zp])
    t2 = th * th
    chr_ = ch_dd([t2 * zm, t2 * z, t2 * zp])
    ca, sa = a.cosh(), a.sinh()
    cb, sb = b.cosh(), b.sinh()
    Cm = clamp_ge((a - b).cosh(), 1)
    Cp = (a + b).cosh()
    # C = cosh(a-b) + (1-w) sinh a sinh b = cosh(a+b) - (1+w) sinh a sinh b
    Cw = meet(clamp_ge(Cm + omw * sa * sb, 1), clamp_ge(Cp - opw * sa * sb, 1))
    Uth = u_dd_box(th, Cm, Cw, Cp)
    U1th = u_dd_box(th, Cm, Cw, Cp, flip=True)
    Sa = shc(a) ** 2
    Sb = shc(b) ** 2
    EG = 2 * (Sa * Sb * (ca * Uth + cb * U1th) - 4 * t2 * (1 - th) ** 2 * chr_)
    qf = omw * opw * a * a * c * c
    epsP = qf * EP
    XP = RE.exp() * epsP
    YG = (-th * RE).exp() * qf * (th / (1 - th)) ** 2 * EG
    parts = dict(EP=EP, EG=EG, XP=XP, YG=YG, RE=RE, Uth=Uth, U1th=U1th, chr=chr_)
    if not (YG.upper() < 1):
        R = arb(0, 1e300)
    else:
        p1 = phi1_box(XP)
        p2 = phi2_box(YG)
        R = RE.exp() * EP * p1 - th / (1 - th) ** 2 * (-th * RE).exp() * EG * p2
    if want:
        return R, epsP, parts
    return R, epsP
