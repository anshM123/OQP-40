"""Independent reference implementation of the Gaussian-design certificate straight from the DEFINITIONS
(no closed forms of RESULTS 8.1 are used).  mpmath, high precision; numerical differentiation.

  K_n(x,y,z) = h_n(x,y,z)/C(n+2,2) - (xyz)^{n/3},  h_n = second divided difference of z^{n+2} at (x,y,z)
  limit kernel (eps = 0), log coordinates: K_inf(x,y,z) = 2 [x,y,z]exp - e^{(x+y+z)/3}
  kappa_inf(z) = 2(e^z - 1 - z)/z^2 - e^{z/3}
  rr(z) = (2 sinh(z/2)/z - e^{-lam z}) / sqrt(kappa_inf(z)/2),  Phi(z) = -sqrt(-log(1 - eta (1 - rr(z))))
  R(u, v) = exp(-(Phi(u) - Phi(v))^2)
  E^R(s,t) = K_n(1,s,t) - sqrt(K_n(t,1,1) K_n(t,s,s)) R(n log t, n log(t/s)),  w(s) = sqrt(K_n(1,s,s))
  F = E^R/(w(s) w(t));  a = n log s, b = n log t, d = b - a.
  L1 = (log F)_a, L2 = -(log F)_b, L3 = -F_ab/F   (partial derivatives in (a, b) at fixed n).
"""
import mpmath as mp

def LAMf():
    return mp.mpf(7) / 100      # evaluated at the current working precision


def ETAf():
    return mp.mpf(7) / 10


def dd2(f, df, x, y, z):
    """second divided difference [x,y,z]f for real nodes, with repeated nodes allowed (f' = df)."""
    xs = sorted([x, y, z])
    x, y, z = xs
    if x == y == z:
        raise ValueError('triple node')
    def dd1(u, v):
        if u == v:
            return df(u)
        return (f(v) - f(u)) / (v - u)
    if x == z:
        raise ValueError
    return (dd1(y, z) - dd1(x, y)) / (z - x)


def Kn(n, x, y, z):
    p = n + 2
    f = lambda u: u ** p
    df = lambda u: p * u ** (p - 1)
    h = dd2(f, df, x, y, z)
    C = mp.mpf((n + 2) * (n + 1)) / 2
    return h / C - (x * y * z) ** (mp.mpf(n) / 3)


def Kinf(x, y, z):
    """limit kernel in log coordinates."""
    return 2 * dd2(mp.exp, mp.exp, x, y, z) - mp.exp((x + y + z) / 3)


def kappa_inf(z):
    return 2 * (mp.exp(z) - 1 - z) / z ** 2 - mp.exp(z / 3)


def rr(z):
    return (2 * mp.sinh(z / 2) / z - mp.exp(-LAMf() * z)) / mp.sqrt(kappa_inf(z) / 2)


def Phi(z):
    y = ETAf() * (1 - rr(z))
    return -mp.sqrt(-mp.log(1 - y))


def Rcorr(u, v):
    return mp.exp(-(Phi(u) - Phi(v)) ** 2)


def F_ab(n, a, b):
    """F as a function of the scaled variables (a, b), b > a > 0; n = None means the limit kernel."""
    if n is None:
        K1 = Kinf(0, a, b)
        cap = mp.sqrt(Kinf(b, 0, 0) * Kinf(b, a, a))
        Wa = Kinf(0, a, a)
        Wb = Kinf(0, b, b)
    else:
        s = mp.exp(mp.mpf(a) / n)
        t = mp.exp(mp.mpf(b) / n)
        K1 = Kn(n, 1, s, t)
        cap = mp.sqrt(Kn(n, t, 1, 1) * Kn(n, t, s, s))
        Wa = Kn(n, 1, s, s)
        Wb = Kn(n, 1, t, t)
        # sanity: the arguments of R are n log t = b, n log(t/s) = b - a
    E = K1 - cap * Rcorr(b, b - a)
    return E / mp.sqrt(Wa * Wb)


def margins(n, a, d, dps=None, h=None):
    """(F, L1, L2, L3) at (a, b = a + d) by central differences (step h) at high precision."""
    a = mp.mpf(a)
    d = mp.mpf(d)
    if dps is None:
        dps = int(120 + 0.30 * float(a + d) + 0.0)
    with mp.workdps(dps):
        a = mp.mpf(a)
        d = mp.mpf(d)
        b = a + d
        if h is None:
            h = mp.mpf(10) ** (-(dps // 5))
            h = min(h, a / 1000, d / 1000)
        f = {}
        for i in (-1, 0, 1):
            for j in (-1, 0, 1):
                if i * j != 0 or True:
                    f[(i, j)] = F_ab(n, a + i * h, b + j * h)
        F0 = f[(0, 0)]
        Fa = (f[(1, 0)] - f[(-1, 0)]) / (2 * h)
        Fb = (f[(0, 1)] - f[(0, -1)]) / (2 * h)
        Fab = (f[(1, 1)] - f[(1, -1)] - f[(-1, 1)] + f[(-1, -1)]) / (4 * h * h)
        L1 = Fa / F0
        L2 = -Fb / F0
        L3 = -Fab / F0
        return F0, L1, L2, L3


if __name__ == '__main__':
    import sys
    for n in (37, 100, None):
        for (a, d) in ((0.5, 1.0), (8.0, 8.36), (64.0, 40.0), (2.0, 0.01)):
            F0, L1, L2, L3 = margins(n, a, d)
            print(n, a, d, mp.nstr(F0, 12), mp.nstr(L1, 12), mp.nstr(L2, 12), mp.nstr(L3, 12))
