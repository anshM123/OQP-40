"""Theorem B, step 1: eps-smooth closed forms for the Gaussian-design certificate, in mpmath, and their comparison
with direct evaluation of the definitions (numerical check of the formulas, not a proof).

Notation: eps = 1/n, a = n log s, d = n log(t/s), b = a + d.  Design: lam = 7/100, eta = 7/10,
  rr(z) = (2 sinh(z/2)/z - e^{-lam z}) / sqrt(kappa_inf(z)/2),  Phi(z) = -sqrt(-log(1 - eta (1 - rr(z)))),
  R(b, d) = exp(-(Phi(b) - Phi(d))^2).
Definitions (reference): E = K_n(1,s,t) - sqrt(K_n(t,1,1) K_n(t,s,s)) R,  F = E / sqrt(K_n(1,s,s) K_n(1,t,t)).

eps-forms (exact for eps = 1/n; at eps = 0 they give the limit kernel K_inf = 2[x,y,z]exp - e^{(x+y+z)/3}):
  c = 2/(1+eps), c' = 2/((1+eps)(1+2eps)), phi1(x) = (e^x - 1)/x,
  Q(z) = z phi1(z eps),  nu(z) = 1/(z phi1(-z eps)) = eps/(1 - e^{-z eps}),  P(z) = phi1(z(1+2eps))/phi1(z eps),
  kappa(z) = K_n(e^{z eps},1,1) = c (P(z) - 1)/Q(z) - e^{z/3},   W(z) = K_n(1,e^{z eps},e^{z eps}) = c (e^{z(1+eps)} - P(z))/Q(z) - e^{2z/3},
  K1 = K_n(1,s,t) = c [e^{a(1+eps)} P(d) - P(a)]/Q(b) - e^{(a+b)/3},   cap = e^{a/2} sqrt(kappa(b) kappa(d)).
nu-form: kappa(z) = c' e^z nu^2 gam(z), W(z) = c e^z nu om(z), K1 = c' e^b nu_b nu_d khat, cap = c' e^b nu_b nu_d sqrt(gam_b gam_d),
  p(z) = e^{-z(1+2eps)} + (1+2eps) e^{-z(1+eps)}/nu(z),  y(z) = e^{-z/3}/(nu(z) sqrt(c')),  gam = 1 - p - y^2,
  om(z) = 1 - nu (1 - e^{-z(1+2eps)})/(1+2eps) - e^{-z/3}/(c nu),
  khat = 1 - u1 - u2 - u3, u1 = e^{-d(1+2eps)}, u2 = (1 - e^{-a(1+2eps)}) (nu_a/nu_d) e^{-d(1+eps)}, u3 = y_b y_d,
  F = e^{d/2} nu_d sqrt(nu_b/nu_a) D / ((1+2eps) sqrt(om_a om_b)),  D = khat - R sqrt(gam_b gam_d)
    = N/(khat + sqrt(gam_b gam_d)) + sqrt(gam_b gam_d)(1 - R),
  N = khat^2 - gam_b gam_d = (y_b - y_d)^2 + [p_b + p_d - 2u1 - 2u2] + (u1+u2)^2 + 2(u1+u2) y_b y_d - p_b p_d - p_b y_d^2 - p_d y_b^2.
"""
import mpmath as mp

LAM = mp.mpf(7) / 100
ETA = mp.mpf(7) / 10


def kap_inf(z):
    return 2 * (mp.expm1(z) - z) / z**2 - mp.e**(z / 3)


def rr(z):
    return (2 * mp.sinh(z / 2) / z - mp.e**(-LAM * z)) / mp.sqrt(kap_inf(z) / 2)


def Phi(z):
    return -mp.sqrt(-mp.log(1 - ETA * (1 - rr(z))))


def Rfun(b, d):
    return mp.e**(-(Phi(b) - Phi(d))**2)


# ---------------- reference: the definitions, integer n -----------------
def ref_F(n, a, b):
    n = mp.mpf(n)
    C = (n + 2) * (n + 1) / 2
    s, t = mp.e**(a / n), mp.e**(b / n)
    d = b - a
    h1st = 1 / ((1 - s) * (1 - t)) + s**(n + 2) / ((s - 1) * (s - t)) + t**(n + 2) / ((t - 1) * (t - s))
    K1 = h1st / C - (s * t)**(n / 3)
    Kt11 = (t**(n + 2) - (n + 2) * t + (n + 1)) / ((t - 1)**2 * C) - t**(n / 3)
    r_ = t / s
    Ktss = s**n * ((r_**(n + 2) - (n + 2) * r_ + (n + 1)) / ((r_ - 1)**2 * C) - r_**(n / 3))
    E = K1 - mp.sqrt(Kt11 * Ktss) * Rfun(b, d)
    w2 = lambda x: ((n + 1) * x**(n + 2) - (n + 2) * x**(n + 1) + 1) / ((x - 1)**2 * C) - x**(2 * n / 3)
    return E / mp.sqrt(w2(s) * w2(t))


def ref_F_inf(a, b):
    def dd2(x, y, z):
        return 2 * (mp.e**x / ((x - y) * (x - z)) + mp.e**y / ((y - x) * (y - z)) + mp.e**z / ((z - x) * (z - y)))
    d = b - a
    K1 = dd2(mp.mpf(0), a, b) - mp.e**((a + b) / 3)
    cap = mp.e**(a / 2) * mp.sqrt(kap_inf(b) * kap_inf(d))
    E = K1 - cap * Rfun(b, d)
    return E / mp.sqrt(mp.e**a * kap_inf(-a) * mp.e**b * kap_inf(-b))


# ---------------- eps-forms -----------------
def phi1(x):
    return mp.expm1(x) / x if x != 0 else mp.mpf(1)


def pieces(eps):
    eps = mp.mpf(eps)
    c = 2 / (1 + eps)
    cp = 2 / ((1 + eps) * (1 + 2 * eps))
    Q = lambda z: z * phi1(z * eps)
    nu = lambda z: 1 / (z * phi1(-z * eps))
    P = lambda z: phi1(z * (1 + 2 * eps)) / phi1(z * eps)
    kap = lambda z: c * (P(z) - 1) / Q(z) - mp.e**(z / 3)
    W = lambda z: c * (mp.e**(z * (1 + eps)) - P(z)) / Q(z) - mp.e**(2 * z / 3)
    return eps, c, cp, Q, nu, P, kap, W


def F_direct(a, d, eps):
    eps, c, cp, Q, nu, P, kap, W = pieces(eps)
    b = a + d
    K1 = c * (mp.e**(a * (1 + eps)) * P(d) - P(a)) / Q(b) - mp.e**((a + b) / 3)
    cap = mp.e**(a / 2) * mp.sqrt(kap(b) * kap(d))
    return (K1 - cap * Rfun(b, d)) / mp.sqrt(W(a) * W(b))


def nu_parts(a, d, eps):
    eps, c, cp, Q, nu, P, kap, W = pieces(eps)
    b = a + d
    na, nb, nd = nu(a), nu(b), nu(d)
    p = lambda z, nz: mp.e**(-z * (1 + 2 * eps)) + (1 + 2 * eps) * mp.e**(-z * (1 + eps)) / nz
    y = lambda z, nz: mp.e**(-z / 3) / (nz * mp.sqrt(cp))
    om = lambda z, nz: 1 - nz * (1 - mp.e**(-z * (1 + 2 * eps))) / (1 + 2 * eps) - mp.e**(-z / 3) / (c * nz)
    pb, pd, yb, yd = p(b, nb), p(d, nd), y(b, nb), y(d, nd)
    gb, gd = 1 - pb - yb**2, 1 - pd - yd**2
    u1 = mp.e**(-d * (1 + 2 * eps))
    u2 = (1 - mp.e**(-a * (1 + 2 * eps))) * (na / nd) * mp.e**(-d * (1 + eps))
    u3 = yb * yd
    kh = 1 - u1 - u2 - u3
    N = (yb - yd)**2 + (pb + pd - 2 * u1 - 2 * u2) + (u1 + u2)**2 + 2 * (u1 + u2) * yb * yd - pb * pd - pb * yd**2 - pd * yb**2
    return dict(eps=eps, c=c, cp=cp, na=na, nb=nb, nd=nd, pb=pb, pd=pd, yb=yb, yd=yd, gb=gb, gd=gd, kh=kh, N=N,
                oma=om(a, na), omb=om(b, nb), b=b)


def F_nu(a, d, eps):
    q = nu_parts(a, d, eps)
    R = Rfun(q['b'], d)
    sg = mp.sqrt(q['gb'] * q['gd'])
    D = q['N'] / (q['kh'] + sg) + sg * (1 - R)
    return mp.e**(d / 2) * q['nd'] * mp.sqrt(q['nb'] / q['na']) * D / ((1 + 2 * q['eps']) * mp.sqrt(q['oma'] * q['omb']))


if __name__ == '__main__':
    import random
    random.seed(20261009)
    mp.mp.dps = 60
    worst = {}
    pts = []
    for n in (37, 50, 100, 1000):
        for _ in range(25):
            a = mp.mpf(10) ** random.uniform(-1.5, 2.6)
            d = mp.mpf(10) ** random.uniform(-2, 2.2)
            pts.append((n, a, d))
        for a, d in ((0.05, 0.01), (0.05, 30), (0.5, 3), (3, 0.01), (64, 40), (300, 100), (1, 150), (150, 0.05)):
            pts.append((n, mp.mpf(a), mp.mpf(d)))
    for (n, a, d) in pts:
        mp.mp.dps = int(60 + (a + d) / 2.3 + 3 * n / 10)
        r = ref_F(n, a, a + d)
        f1 = F_direct(a, d, mp.mpf(1) / n)
        f2 = F_nu(a, d, mp.mpf(1) / n)
        e1, e2 = abs(f1 / r - 1), abs(f2 / r - 1)
        for key, e in (('direct', e1), ('nu', e2)):
            if key not in worst or e > worst[key][0]:
                worst[key] = (e, n, float(a), float(d), float(r))
    for key, v in worst.items():
        print(f"max rel. deviation of the {key} eps-form from the definition: {mp.nstr(v[0], 3)} at n={v[1]}, a={v[2]:.4g}, d={v[3]:.4g} (F={v[4]:.4g})")
    # limit eps = 0 against the limit kernel
    worst0 = 0
    for _ in range(40):
        mp.mp.dps = 80
        a = mp.mpf(10) ** random.uniform(-1.5, 2.5)
        d = mp.mpf(10) ** random.uniform(-1.5, 2)
        r = ref_F_inf(a, a + d)
        f2 = F_nu(a, d, mp.mpf(0))
        f1 = F_direct(a, d, mp.mpf(0))
        worst0 = max(worst0, abs(f2 / r - 1), abs(f1 / r - 1))
    print(f"eps = 0 (nu-form) and direct form at eps = 0 against the limit kernel: max rel. deviation {mp.nstr(worst0, 3)}")
