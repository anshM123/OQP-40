"""Hyperbolic-coordinate form of the 2x2 closed-form inequality (C) (mpmath, NUMERICAL reference).
Ansh Mishra, Aryan Senthilkumar.

Scale-normalise A = e^{x.sigma}, B = e^{y.sigma} (x, y in R^3), a = |x|, b = |y|, w = cos(angle(x, y)).
  rho  = |theta x + (1-theta) y|          (Z = theta log A + (1-theta) log B has eigenvalues -/+ rho)
  N0 rho = |x + r y|
  cosh D_P = cosh a cosh(rb) + w sinh a sinh(rb)          P = Tr(A B^r) = 2 cosh D_P
  cosh d   = cosh a cosh b - w sinh a sinh b
  G = Tr(A^{-1} #_{1-theta} B^{-1}) = 2 [sinh(theta d) cosh a + sinh((1-theta) d) cosh b] / sinh d
  eps_P = P - 2 cosh(N0 rho) (Golden-Thompson gap),  eps_G = 2 cosh(rho) - G (Ando-Hiai gap)
  (C)  <=>  F := theta log(1 + e^{N0 rho} eps_P) + log(1 - e^{-rho} eps_G) >= 0.
"""
import mpmath as mp


def parts(th, a, b, w):
    th, a, b, w = mp.mpf(th), mp.mpf(a), mp.mpf(b), mp.mpf(w)
    r = (1 - th) / th
    N0 = 1 / th
    rho = mp.sqrt(max(th ** 2 * a ** 2 + (1 - th) ** 2 * b ** 2 + 2 * th * (1 - th) * a * b * w, 0))
    c = r * b
    cDP = mp.cosh(a) * mp.cosh(c) + w * mp.sinh(a) * mp.sinh(c)
    P = 2 * cDP
    cd = mp.cosh(a) * mp.cosh(b) - w * mp.sinh(a) * mp.sinh(b)
    if cd <= 1:
        G = 2 * (th * mp.cosh(a) + (1 - th) * mp.cosh(b))  # d = 0 limit
    else:
        d = mp.acosh(cd)
        G = 2 * (mp.sinh(th * d) * mp.cosh(a) + mp.sinh((1 - th) * d) * mp.cosh(b)) / mp.sinh(d)
    epsP = P - 2 * mp.cosh(N0 * rho)
    epsG = 2 * mp.cosh(rho) - G
    return dict(rho=rho, P=P, G=G, epsP=epsP, epsG=epsG, N0=N0, r=r)


def F(th, a, b, w):
    q = parts(th, a, b, w)
    th = mp.mpf(th)
    return th * mp.log(1 + mp.exp(q['N0'] * q['rho']) * q['epsP']) + mp.log(1 - mp.exp(-q['rho']) * q['epsG'])


def Rhat(th, a, b, w):
    a, b, w = mp.mpf(a), mp.mpf(b), mp.mpf(w)
    return F(th, a, b, w) / (a ** 2 * b ** 2 * (1 - w ** 2))
