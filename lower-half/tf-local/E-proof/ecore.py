"""Core ball-arithmetic routines (python-flint / Arb) for the proof of E(theta, X, Y) >= 0.

Coordinates: x = X, y = r Y with r = (1-theta)/theta, so s := x + y = Delta/theta >= 0 on the domain.
kappa = theta/(1-theta), Y = kappa*y, D = x - Y = X - Y.

Normalised function  H(theta, x, y) := E/(theta x^2 y^2) = g(x, y) - theta*m(theta, x, y)  with
  g  = C_GT/(xy),            C_GT = phi(s) - phi(x) phi(y)                       (theta-free)
  tm = theta*m = -theta*C_m1/(xy),  C_m1 = phi(-theta s) - phi(x) phi(Y) J,
  J  = [e^Y ee(0,(1-theta)D, D) + ee(0,-theta D,(1-theta)D)] / (e^{2Y} phi(D)^2)
  (ee = second divided difference of exp).
Second formula for tm (no division by x or y; needs s > 0):
  tm = kappa phi(x) phi(Y) [u* e^Y E1 - (1-u*) E2] / (e^{2Y} phi(D)^2 s),
  u* = theta psi(Y) + (1-theta) psi(x),  psi(z) = 1/z - 1/(e^z-1),  E1 = ee(0,(1-theta)D,D), E2 = ee(0,-theta D,(1-theta)D).

All functions accept arb (real balls) or acb (complex balls).  Monotone real special functions have *_iv versions
that return a rigorous enclosure over a whole real ball (interval) by evaluating at the endpoints.
"""
from flint import arb, acb, ctx

ctx.prec = 256

_FACT = [arb(1)]
for _k in range(1, 400):
    _FACT.append(_FACT[-1] * _k)


def fact(n):
    return _FACT[n]


def _absup(z):
    """Upper bound (float) for |z|: Arb upper bound, converted to a double (round to nearest, error <= 1/2 ulp)
    and then inflated by the relative factor 1 + 2^-40 (plus 2^-1000), so the returned float is >= |z|."""
    v = float(abs(z).upper())
    return v * (1 + 2.0 ** -40) + 2.0 ** -1000


def _iscomplex(z):
    return isinstance(z, acb)


def _err_ball(z, r):
    """Return a ball of radius r (r >= 0 float/arb) around 0, of the same kind as z."""
    r = arb(r)
    e = arb(0, r.upper()) if not r.is_zero() else arb(0)
    if _iscomplex(z):
        return acb(e, e)
    return e


# ---------------------------------------------------------------- phi(z) = (e^z - 1)/z

def _phi_series(z, zabs):
    # sum_{k>=0} z^k/(k+1)!, tail bound: |z|^{K+1}/(K+2)! / (1 - |z|/(K+3))
    K = 20
    while True:
        tb = zabs ** (K + 1) / float(fact(K + 2).mid()) / (1 - zabs / (K + 3)) if zabs < K + 3 else 1e300
        if tb < 2.0 ** (-ctx.prec - 10) or K > 380:
            break
        K += 10
    s = z * 0
    term = z * 0 + 1
    for k in range(0, K + 1):
        s = s + term / fact(k + 1)
        term = term * z
    zab = arb(zabs)
    tail = zab ** (K + 1) / fact(K + 2) / (1 - zab / (K + 3))
    return s + _err_ball(z, tail.upper())


def phi(z):
    """phi(z) = (e^z-1)/z, rigorous for any arb/acb ball z (series when |z| <= 1, else expm1/z)."""
    za = _absup(z)
    if za <= 1.0:
        return _phi_series(z, za)
    if (not _iscomplex(z)) and z.contains(0):
        return _phi_series(z, za)
    if _iscomplex(z) and z.contains(acb(0)):
        return _phi_series(z, za)
    return z.expm1() / z if not _iscomplex(z) else (z.exp() - 1) / z


def phi_iv(z):
    """Enclosure of phi over a real ball z (phi is increasing on R)."""
    lo, hi = z.lower(), z.upper()
    return arb.union(phi(lo), phi(hi))


# ---------------------------------------------------------------- phi2(z) = (e^z - 1 - z)/z^2 = exp[0,0,z]

def _phi2_series(z, zabs):
    K = 20
    while True:
        tb = zabs ** (K + 1) / float(fact(K + 3).mid()) / (1 - zabs / (K + 4)) if zabs < K + 4 else 1e300
        if tb < 2.0 ** (-ctx.prec - 10) or K > 380:
            break
        K += 10
    s = z * 0
    term = z * 0 + 1
    for k in range(0, K + 1):
        s = s + term / fact(k + 2)
        term = term * z
    zab = arb(zabs)
    tail = zab ** (K + 1) / fact(K + 3) / (1 - zab / (K + 4))
    return s + _err_ball(z, tail.upper())


def phi2(z):
    za = _absup(z)
    if za <= 1.0 or z.contains(acb(0) if _iscomplex(z) else 0):
        return _phi2_series(z, za)
    em1 = z.expm1() if not _iscomplex(z) else z.exp() - 1
    return (em1 - z) / (z * z)


# ---------------------------------------------------------------- psi(z) = 1/z - 1/(e^z - 1) = phi2(z)/phi(z)

def psi(z):
    return phi2(z) / phi(z)


def psi_iv(z):
    """psi is decreasing on R."""
    lo, hi = z.lower(), z.upper()
    return arb.union(psi(hi), psi(lo))


# ---------------------------------------------------------------- second divided difference of exp

def _ee_series(a, u, v, dm):
    """exp[a, a+u, a+v] = e^a sum_n h_n(u, v)/(n+2)!, |u|,|v| <= dm."""
    K = 20
    while True:
        # tail <= sum_{n>K} (n+1) dm^n/(n+2)!  <= (K+2) dm^{K+1}/(K+3)! / (1 - dm/(K+2))   (dm < K+2);
        # consecutive-term ratio (n+2) dm/((n+1)(n+3)) <= dm/(n+1) <= dm/(K+2) for n >= K+1
        tb = (K + 2) * dm ** (K + 1) / float(fact(K + 3).mid()) / (1 - dm / (K + 2)) if dm < K + 2 else 1e300
        if tb < 2.0 ** (-ctx.prec - 10) or K > 380:
            break
        K += 10
    s = u * 0
    h = u * 0 + 1          # h_0 = 1
    vp = u * 0 + 1         # v^n
    for n in range(0, K + 1):
        if n > 0:
            vp = vp * v
            h = u * h + vp
        s = s + h / fact(n + 2)
    d = arb(dm)
    tail = (K + 2) * d ** (K + 1) / fact(K + 3) / (1 - d / (K + 2))
    return a.exp() * (s + _err_ball(s, tail.upper()))


def _exp1(u, v):
    """first divided difference exp[u, v] = e^u phi(v - u)."""
    return u.exp() * phi(v - u)


def ee(a, b, c):
    """exp[a, b, c] for arb/acb balls (rigorous)."""
    dab = _absup(b - a)
    dac = _absup(c - a)
    dbc = _absup(c - b)
    dmax = max(dab, dac, dbc)
    if dmax <= 1.0:
        return _ee_series(a, b - a, c - a, max(dab, dac))
    # pick the farthest pair as the outer nodes
    if dac >= dab and dac >= dbc:
        za, zb, zc = a, b, c
    elif dab >= dac and dab >= dbc:
        za, zb, zc = a, c, b
    else:
        za, zb, zc = b, a, c
    if float(abs(zc - za).lower()) < 0.5:
        # wide balls: fall back to the (always valid) series around a
        return _ee_series(a, b - a, c - a, max(dab, dac))
    return (_exp1(zb, zc) - _exp1(za, zb)) / (zc - za)


def ee_iv(a, b, c):
    """Enclosure of exp[a,b,c] over real balls a, b, c (increasing in each node)."""
    return arb.union(ee(a.lower(), b.lower(), c.lower()), ee(a.upper(), b.upper(), c.upper()))


# ---------------------------------------------------------------- the functions g, tm, H at points

def g_point(x, y):
    """g = (phi(x+y) - phi(x) phi(y))/(xy) at a point with x, y != 0 (cancellation handled by precision)."""
    return (phi(x + y) - phi(x) * phi(y)) / (x * y)


def g_series(x, y, K=60):
    """g = sum_{j,k>=0} x^j y^k / (j! k! (j+k+3)(j+2)(k+2)), for |x|,|y| <= 1.1 (rigorous tail).
    Tail: |term| <= |x|^j |y|^k/(12 j! k!), sum_{j+k=n} = (|x|+|y|)^n/(12 n!), and with a = |x|+|y| <= 2.2,
    sum_{n>K} a^n/n! <= a^{K+1}/(K+1)! / (1 - a/(K+2))."""
    ax, ay = _absup(x), _absup(y)
    assert ax <= 1.1 and ay <= 1.1
    s = x * 0
    xp = [x * 0 + 1]
    yp = [y * 0 + 1]
    for i in range(1, K + 1):
        xp.append(xp[-1] * x)
        yp.append(yp[-1] * y)
    for j in range(K + 1):
        for k in range(K + 1 - j):
            s = s + xp[j] * yp[k] / (fact(j) * fact(k) * (j + k + 3) * (j + 2) * (k + 2))
    a = (abs(x) + abs(y)).upper()
    tail = a ** (K + 1) / fact(K + 1) / (1 - a / (K + 2)) / 12
    return s + _err_ball(s, tail.upper())


def J_parts(th, x, y):
    k = th / (1 - th)
    Y = k * y
    D = x - Y
    E1 = ee(x * 0, (1 - th) * D, D)
    E2 = ee(x * 0, -th * D, (1 - th) * D)
    den = (2 * Y).exp() * phi(D) ** 2
    return k, Y, D, E1, E2, den


def tm_point_I(th, x, y):
    """theta*m via formula (I') at a point (needs x, y != 0)."""
    k, Y, D, E1, E2, den = J_parts(th, x, y)
    J = (Y.exp() * E1 + E2) / den
    Cm1 = phi(-th * (x + y)) - phi(x) * phi(Y) * J
    return -th * Cm1 / (x * y)


def tm_point_II(th, x, y):
    """theta*m via formula (II'') at a point (needs s = x + y != 0)."""
    k, Y, D, E1, E2, den = J_parts(th, x, y)
    us = th * psi(Y) + (1 - th) * psi(x)
    return k * phi(x) * phi(Y) * (us * Y.exp() * E1 - (1 - us) * E2) / (den * (x + y))


def H_point(th, x, y):
    """H at a point via (I'); x, y != 0."""
    return g_point(x, y) - tm_point_I(th, x, y)


# ---------------------------------------------------------------- interval (box) enclosures, real balls

def tm_box_I(th, x, y):
    """Enclosure of theta*m over a box (real balls th, x, y; x, y must not contain 0), formula (I')."""
    k = th / (1 - th)
    Y = k * y
    D = x - Y
    s = x + y
    E1 = ee_iv(D * 0, (1 - th) * D, D)
    E2 = ee_iv(D * 0, -th * D, (1 - th) * D)
    pD = phi_iv(D)
    J = (Y.exp() * E1 + E2) / ((2 * Y).exp() * pD * pD)
    Cm1 = phi_iv(-th * s) - phi_iv(x) * phi_iv(Y) * J
    return -th * Cm1 / (x * y)


def tm_box_II(th, x, y):
    """Enclosure of theta*m over a box, formula (II'') (s must stay > 0)."""
    k = th / (1 - th)
    Y = k * y
    D = x - Y
    s = x + y
    E1 = ee_iv(D * 0, (1 - th) * D, D)
    E2 = ee_iv(D * 0, -th * D, (1 - th) * D)
    pD = phi_iv(D)
    us = th * psi_iv(Y) + (1 - th) * psi_iv(x)
    return k * phi_iv(x) * phi_iv(Y) * (us * Y.exp() * E1 - (1 - us) * E2) / ((2 * Y).exp() * pD * pD * s)


def g_box_lower(xlo, ylo):
    """Lower bound of g over a box with lower corner (xlo, ylo): g is increasing in x and in y.
    Evaluates g at (xlo - eps, ylo - eps) chosen off the axes (still a lower bound by monotonicity)."""
    eps = arb('1e-30')
    xa = xlo - eps
    ya = ylo - eps
    if _absup(xa) <= 1.0 and _absup(ya) <= 1.0:
        return g_series(xa, ya).lower()
    return g_point(xa, ya).lower()


def g_box_upper(xhi, yhi):
    eps = arb('1e-30')
    xa = xhi + eps
    ya = yhi + eps
    if _absup(xa) <= 1.0 and _absup(ya) <= 1.0:
        return g_series(xa, ya).upper()
    return g_point(xa, ya).upper()
