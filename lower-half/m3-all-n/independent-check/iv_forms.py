"""Independent verifier, part 2: log F of the Gaussian-design certificate as a jet in (a, d, eps).

Derivation (re-done by hand, see REPORT.md): with c = 2/(1+eps), c2 = 2/((1+eps)(1+2eps)), phi(x) = (e^x - 1)/x,
nu(z) = 1/(z phi(-z eps)) (= eps/(1 - e^{-z eps}); 1/z at eps = 0):
  kappa(z) = K_n(e^{z eps},1,1) = c2 e^z nu_z^2 Gam_z,  Gam_z = 1 - p_z - y_z^2,
      p_z = e^{-z(1+2eps)} + (1+2eps) e^{-z(1+eps)}/nu_z,   y_z = e^{-z/3}/(nu_z sqrt(c2)),
  W(z)     = K_n(1,e^{z eps},e^{z eps}) = c e^z nu_z Om_z,  Om_z = 1 - nu_z (1 - e^{-z(1+2eps)})/(1+2eps) - e^{-z/3}/(c nu_z),
  K_n(1,s,t) = c2 e^b nu_b nu_d khat,  khat = 1 - u1 - u2 - y_b y_d,
      u1 = e^{-d(1+2eps)},  u2 = nu_a (1 - e^{-a(1+2eps)}) e^{-d(1+eps)}/nu_d,
  cap = e^{a/2} sqrt(kappa(b) kappa(d)) = c2 e^b nu_b nu_d sqrt(Gam_b Gam_d),
  F = e^{d/2} nu_d sqrt(nu_b/nu_a) D/((1+2eps) sqrt(Om_a Om_b)),  D = khat - R sqrt(Gam_b Gam_d),
  D = N/(khat + sqrt(Gam_b Gam_d)) + sqrt(Gam_b Gam_d) (1 - R),   N = khat^2 - Gam_b Gam_d
    = (y_b - y_d)^2 + (p_b + p_d - 2U) + U^2 + 2 U Y - p_b p_d - p_b y_d^2 - p_d y_b^2   (U = u1 + u2, Y = y_b y_d),
  1 - R = x phi(-x), x = (Phi(b) - Phi(d))^2.
Design function, z >= 2 (cancellation-free):
  G(z) = 1 - (1+z) e^{-z} - (z^2/2) e^{-2z/3},
  q(z) = [(z - 1 + e^{-z}) e^{-(1/2-lam) z}/z + (z/2) e^{-(1/6-lam) z}] / (1 - e^{-z} + sqrt(G)),
  y(z) = eta (1 - rr(z)) = eta z e^{-(1/2+lam) z} (1 - q)/sqrt(G),   Phi(z) = -sqrt(-log(1 - y(z))).
"""
from flint import arb
import iv_jet as JJ
from iv_jet import Jet, NotPos

LAM = arb(7) / 100
ETA = arb(7) / 10


def Phi_big(z):
    """Phi at a jet z whose ball is >= 2: Phi = Phihat(z) e^{-mu z} (iv_phi.py, scaled closed form, cell enclosures)."""
    import iv_phi
    z0 = z.ball() if hasattr(z, 'ball') else z.c[0]
    if not (z0 >= arb(7) / 4 or (z0.rad() < 1e-40 and z0 > 0)):
        raise NotPos('Phi_big needs z >= 7/4')
    return z.phihat() * (-(iv_phi.MU * z)).exp()


def nu(z, eps):
    return 1 / (z * (-(z * eps)).phi1())


def logF_nu(a, d, eps):
    """log F (nu-form with the perfect square); intended for a, d >= ~3."""
    b = a + d
    e1 = 1 + eps
    e2 = 1 + 2 * eps
    c = 2 / e1
    c2 = 2 / (e1 * e2)
    sc2 = c2.sqrt()
    na, nb, nd = nu(a, eps), nu(b, eps), nu(d, eps)
    yb = (-(b / 3)).exp() / (nb * sc2)
    yd = (-(d / 3)).exp() / (nd * sc2)
    pb = (-(b * e2)).exp() + e2 * (-(b * e1)).exp() / nb
    pd = (-(d * e2)).exp() + e2 * (-(d * e1)).exp() / nd
    Gb = 1 - pb - yb * yb
    Gd = 1 - pd - yd * yd
    ea2 = (-(a * e2)).exp()
    Oa = 1 - na * (1 - ea2) / e2 - (-(a / 3)).exp() / (c * na)
    Ob = 1 - nb * (1 - (-(b * e2)).exp()) / e2 - (-(b / 3)).exp() / (c * nb)
    u1 = (-(d * e2)).exp()
    u2 = na * (1 - ea2) * (-(d * e1)).exp() / nd
    U = u1 + u2
    Y = yb * yd
    kh = 1 - U - Y
    N = (yb - yd) * (yb - yd) + (pb + pd - 2 * U) + U * U + 2 * U * Y - pb * pd - pb * yd * yd - pd * yb * yb
    sg = (Gb * Gd).sqrt()
    dPhi = Phi_big(b) - Phi_big(d)
    x = dPhi * dPhi
    omR = x * (-x).phi1()
    D = N / (kh + sg) + sg * omR
    return d / 2 + nd.log() + (nb.log() - na.log()) / 2 - e2.log() - (Oa.log() + Ob.log()) / 2 + D.log()


def conditions(G):
    """L1, L2, L3 from the jet G = log F in (a, d, eps) coordinates (partials at fixed d resp. fixed a):
    d/da|_b = d_a - d_d, d/db|_a = d_d.  L1 = G_a - G_d, L2 = -G_d, L3 = L1 L2 - (G_ad - G_dd)."""
    Ga, Gd = G.co(1, 0), G.co(0, 1)
    Gad, Gdd = G.co(1, 1), 2 * G.co(0, 2)
    L1 = Ga - Gd
    L2 = -Gd
    L3 = L1 * L2 - (Gad - Gdd)
    return L1, L2, L3


def gradients(G):
    """d/da, d/dd, d/deps of (L1, L2, L3) (in the (a, d, eps) coordinates) from the jet G."""
    Ga, Gd = G.co(1, 0), G.co(0, 1)
    Gaa, Gad, Gdd = 2 * G.co(2, 0), G.co(1, 1), 2 * G.co(0, 2)
    Gaad, Gadd, Gddd = 2 * G.co(2, 1), 2 * G.co(1, 2), 6 * G.co(0, 3)
    Gae, Gde, Gade, Gdde = G.co(1, 0, 1), G.co(0, 1, 1), G.co(1, 1, 1), 2 * G.co(0, 2, 1)
    L1 = Ga - Gd
    L2 = -Gd
    # d/da
    L1a, L2a = Gaa - Gad, -Gad
    L3a = L1a * L2 + L1 * L2a - (Gaad - Gadd)
    # d/dd
    L1d, L2d = Gad - Gdd, -Gdd
    L3d = L1d * L2 + L1 * L2d - (Gadd - Gddd)
    # d/deps
    L1e, L2e = Gae - Gde, -Gde
    L3e = L1e * L2 + L1 * L2e - (Gade - Gdde)
    return (L1a, L1d, L1e), (L2a, L2d, L2e), (L3a, L3d, L3e)


def logF_nus(a, d, eps):
    """log F, scaled nu-form (own re-derivation; no growing/decaying exponential left inside a jet):
      yh_z = 1/(nu_z sqrt c2) (y_z = e^{-z/3} yh_z),  ph_z = e^{-2 z eps} + (1+2eps) e^{-z eps}/nu_z (p_z = e^{-z} ph_z),
      Uh = e^{-2 d eps} + nu_a (1 - e^{-a(1+2eps)}) e^{-d eps}/nu_d   (U = e^{-d} Uh),
      Nt = e^{2d/3} N = (yh_b e^{-a/3} - yh_d)^2 + e^{-d/3} (ph_b e^{-a} + ph_d - 2 Uh) + e^{-4d/3} Uh^2
           + 2 e^{-d} e^{-a/3} Uh yh_b yh_d - ph_b ph_d e^{-a} e^{-4d/3} - ph_b yh_d^2 e^{-a} e^{-d} - ph_d yh_b^2 e^{-2a/3} e^{-d},
      khat = 1 - e^{-d} Uh - yh_b yh_d e^{-a/3} e^{-2d/3},  Gam_z = 1 - e^{-z} ph_z - yh_z^2 e^{-2z/3},
      dif = Phihat_b e^{-mu a} - Phihat_d,  x = dif^2 e^{-(1/2+lam) d},
      Dhat = e^{(1/2+lam) d} D = e^{-(1/6-lam) d} Nt/(khat + sg) + sg dif^2 phi(-x),  sg = sqrt(Gam_b Gam_d),
      log F = -lam d + log nu_d + (log nu_b - log nu_a)/2 - log(1+2eps) - (log Om_a + log Om_b)/2 + log Dhat."""
    import iv_phi
    b = a + d
    e1 = 1 + eps
    e2 = 1 + 2 * eps
    c = 2 / e1
    c2 = 2 / (e1 * e2)
    sc2 = c2.sqrt()
    na, nb, nd = nu(a, eps), nu(b, eps), nu(d, eps)
    yhb, yhd = 1 / (nb * sc2), 1 / (nd * sc2)
    phb = (-(2 * b * eps)).exp() + e2 * (-(b * eps)).exp() / nb
    phd = (-(2 * d * eps)).exp() + e2 * (-(d * eps)).exp() / nd
    ema, ema3 = (-a).exp(), (-(a / 3)).exp()
    emd, emd3 = (-d).exp(), (-(d / 3)).exp()
    ea2 = (-(a * e2)).exp()
    Uh = (-(2 * d * eps)).exp() + na * (1 - ea2) * (-(d * eps)).exp() / nd
    emd43 = emd * emd3
    t1 = yhb * ema3 - yhd
    Nt = (t1 * t1 + emd3 * (phb * ema + phd - 2 * Uh) + emd43 * Uh * Uh + 2 * emd * ema3 * Uh * yhb * yhd
          - phb * phd * ema * emd43 - phb * yhd * yhd * ema * emd - phd * yhb * yhb * ema3 * ema3 * emd)
    kh = 1 - emd * Uh - yhb * yhd * ema3 * emd3 * emd3
    Gb = 1 - (-b).exp() * phb - yhb * yhb * (-(2 * b / 3)).exp()
    Gd = 1 - emd * phd - yhd * yhd * emd3 * emd3
    sg = (Gb * Gd).sqrt()
    dif = b.phihat() * (-(iv_phi.MU * a)).exp() - d.phihat()
    dif2 = dif * dif
    x = dif2 * (-((2 * iv_phi.MU) * d)).exp()
    Dh = (-((arb(1) / 6 - LAM) * d)).exp() * Nt / (kh + sg) + sg * dif2 * (-x).phi1()
    Oa = 1 - na * (1 - ea2) / e2 - ema3 / (c * na)
    Ob = 1 - nb * (1 - (-(b * e2)).exp()) / e2 - (-(b / 3)).exp() / (c * nb)
    return -LAM * d + nd.log() + (nb.log() - na.log()) / 2 - e2.log() - (Oa.log() + Ob.log()) / 2 + Dh.log()


def _apart(a, eps, c, use_series):
    """-(log nu_a + log Om_a)/2;  series: nu_a Om_a = a^2 S(-a)/c."""
    import iv_small
    if use_series:
        return -a.log() - iv_small.S_of(-a, eps).log() / 2 + c.log() / 2
    na = nu(a, eps)
    e2 = 1 + 2 * eps
    Oa = 1 - na * (1 - (-(a * e2)).exp()) / e2 - (-(a / 3)).exp() / (c * na)
    return -(na.log() + Oa.log()) / 2


def _bpart(b, eps, c, use_series):
    """(log nu_b - log Om_b)/2."""
    import iv_small
    nb = nu(b, eps)
    if use_series:
        return nb.log() - b.log() - iv_small.S_of(-b, eps).log() / 2 + c.log() / 2
    e2 = 1 + 2 * eps
    Ob = 1 - nb * (1 - (-(b * e2)).exp()) / e2 - (-(b / 3)).exp() / (c * nb)
    return (nb.log() - Ob.log()) / 2


def _cpgam(z, eps, c2, use_series):
    """c2 Gam_z;  series: c2 Gam_z = z^4 phi(-z eps)^2 S(z) e^{-z}."""
    import iv_small
    if use_series:
        p = (-(z * eps)).phi1()
        z2 = z * z
        return z2 * z2 * p * p * iv_small.S_of(z, eps) * (-z).exp()
    nz = nu(z, eps)
    e1, e2 = 1 + eps, 1 + 2 * eps
    pz = (-(z * e2)).exp() + e2 * (-(z * e1)).exp() / nz
    yz2 = (-(2 * z / 3)).exp() / (nz * nz * c2)
    return c2 * (1 - pz - yz2)


def _ball(x):
    return x.ball() if hasattr(x, 'ball') else x.c[0]


def logF_mix(a, d, eps):
    """mixed form (F4), re-derived:  F = sqrt(nu_b/nu_a) Bm/sqrt(Om_a Om_b),
      Bm = e^{-d(1/2+eps)} (P(d) - qa) - e^{-a/3} e^{-d/6}/(c nu_b) - (sqrt(c2 Gam_b)/c) d sqrt(S(d)) R,
      P(d) = phi(d(1+2eps))/phi(d eps),  qa = nu_a (1 - e^{-a(1+2eps)})/(1+2eps) = phi(-a(1+2eps))/phi(-a eps).
    Series forms (no small-argument cancellation) for Om_a when a <= 8, for Om_b, Gam_b when b <= 8."""
    import iv_small
    b = a + d
    e1, e2 = 1 + eps, 1 + 2 * eps
    c = 2 / e1
    c2 = 2 / (e1 * e2)
    sa = _ball(a).upper() <= 8
    sb = _ball(b).upper() <= 8
    nb = nu(b, eps)
    Pd = (d * e2).phi1() / (d * eps).phi1()
    qa = (-(a * e2)).phi1() / (-(a * eps)).phi1()
    dPhi = iv_small.Phi_any(b) - iv_small.Phi_any(d)
    R = (-(dPhi * dPhi)).exp()
    Sd = iv_small.S_of(d, eps)
    Bm = ((-(d * (arb(1) / 2 + eps))).exp() * (Pd - qa) - (-(a / 3)).exp() * (-(d / 6)).exp() / (c * nb)
          - _cpgam(b, eps, c2, sb).sqrt() / c * d * Sd.sqrt() * R)
    return _apart(a, eps, c, sa) + _bpart(b, eps, c, sb) + Bm.log()


def logF_nus2(a, d, eps):
    """scaled nu-form (logF_nus) with the cancellation-free series pieces for small arguments:
    -(log nu_a + log Om_a)/2 and (log nu_b - log Om_b)/2 via nu_z Om_z = z^2 S(-z)/c when z <= 8,
    Gam_b, Gam_d via c2 Gam_z = z^4 phi(-z eps)^2 S(z) e^{-z} when z <= 8."""
    import iv_phi
    b = a + d
    e1 = 1 + eps
    e2 = 1 + 2 * eps
    c = 2 / e1
    c2 = 2 / (e1 * e2)
    sc2 = c2.sqrt()
    na, nb, nd = nu(a, eps), nu(b, eps), nu(d, eps)
    yhb, yhd = 1 / (nb * sc2), 1 / (nd * sc2)
    phb = (-(2 * b * eps)).exp() + e2 * (-(b * eps)).exp() / nb
    phd = (-(2 * d * eps)).exp() + e2 * (-(d * eps)).exp() / nd
    ema, ema3 = (-a).exp(), (-(a / 3)).exp()
    emd, emd3 = (-d).exp(), (-(d / 3)).exp()
    ea2 = (-(a * e2)).exp()
    Uh = (-(2 * d * eps)).exp() + na * (1 - ea2) * (-(d * eps)).exp() / nd
    emd43 = emd * emd3
    t1 = yhb * ema3 - yhd
    Nt = (t1 * t1 + emd3 * (phb * ema + phd - 2 * Uh) + emd43 * Uh * Uh + 2 * emd * ema3 * Uh * yhb * yhd
          - phb * phd * ema * emd43 - phb * yhd * yhd * ema * emd - phd * yhb * yhb * ema3 * ema3 * emd)
    kh = 1 - emd * Uh - yhb * yhd * ema3 * emd3 * emd3
    Gb = _cpgam(b, eps, c2, _ball(b).upper() <= 8) / c2
    Gd = _cpgam(d, eps, c2, _ball(d).upper() <= 8) / c2
    sg = (Gb * Gd).sqrt()
    dif = b.phihat() * (-(iv_phi.MU * a)).exp() - d.phihat()
    dif2 = dif * dif
    x = dif2 * (-((2 * iv_phi.MU) * d)).exp()
    Dh = (-((arb(1) / 6 - LAM) * d)).exp() * Nt / (kh + sg) + sg * dif2 * (-x).phi1()
    return (-LAM * d + nd.log() + _apart(a, eps, c, _ball(a).upper() <= 8) + _bpart(b, eps, c, _ball(b).upper() <= 8)
            - e2.log() + Dh.log())
