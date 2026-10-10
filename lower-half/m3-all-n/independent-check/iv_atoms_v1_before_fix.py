"""Independent verifier: rigorous bounds for the exponentially small terms ("atoms") of the tail charts.

Every atom Z is an analytic function of the complex variables (a', d') near the real point (a, d); if |Z| <= X on the
polydisc {|a'-a| <= 1, |d'-d| <= 1} then every Taylor coefficient of Z at (a, d) is <= X (Cauchy), so the jet of Z is
enclosed by the jet with all coefficients in [-X, X].  The sup bounds below use only:
  |e^{-c zeta}| = e^{-c Re zeta},  |zeta| <= Re zeta + 2 on these discs (|Im zeta| <= 2),
  |phi(-u)| <= 1 for Re u >= 0 (phi(-u) = int_0^1 e^{-ut} dt), hence |1/nu(zeta)| = |zeta phi(-zeta eps)| <= |zeta|,
  Re phi(-u) >= cos(Im u) phi(-Re u) >= 0.998 / (1 + Re u) for |Im u| <= 2/37, hence |nu(zeta)| <= (1/Re zeta + eps)/0.998,
  1/sqrt(c2) <= 0.74 (c2 = 2/((1+eps)(1+2eps)) >= 1.845), |1/c| <= 0.52.
Each bound is of the form poly(x) e^{-c x} with c x_min > deg, hence decreasing on the chart; it is evaluated at the
smallest real part x_min of the chart.
Design function (z = d' or b', Re z = x): with G = 1 - (1+z) e^{-z} - (z^2/2) e^{-2z/3},
  |1 - G| <= (x + 3) e^{-x} + ((x + 2)^2/2) e^{-2x/3} =: g,
  |q| <= [(x + 4) e^{-(1/2-lam) x}/x + ((x + 2)/2) e^{-(1/6-lam) x}]/(2 - e^{-x} - g) =: qq,
  |y| <= eta (x + 2) e^{-(1/2+lam) x} (1 + qq)/sqrt(1 - g) =: yy,
  phit = sqrt(eta (1-q) ell(y)/sqrt(G)) = sqrt(eta) sqrt(1 + u), |u| <= (1+qq)(1+yy)(1+2g) - 1,
  |phit - sqrt(eta)| <= sqrt(eta) |u| (|u| <= 1/2),  |phit| <= sqrt(eta (1 + |u|)).
"""
import flint
from flint import arb
flint.ctx.prec = 200

LAM = arb(7) / 100
ETA = arb(7) / 10
MU = (arb(1) / 2 + LAM) / 2


def phit_bounds(xmin):
    """(bound of |phit - sqrt(eta)|, bound of |phit|) for Re z >= xmin (xmin >= 20)."""
    x = arb(xmin)
    g = (x + 3) * (-x).exp() + (x + 2) ** 2 / 2 * (-(2 * x / 3)).exp()
    qq = ((x + 4) * (-((arb(1) / 2 - LAM) * x)).exp() / x + (x + 2) / 2 * (-((arb(1) / 6 - LAM) * x)).exp()) / (2 - (-x).exp() - g)
    yy = ETA * (x + 2) * (-((arb(1) / 2 + LAM) * x)).exp() * (1 + qq) / (1 - g).sqrt()
    u = (1 + qq) * (1 + yy) * (1 + 2 * g) - 1
    assert u.upper() <= 0.5
    return (ETA.sqrt() * u).upper(), (ETA * (1 + u)).sqrt().upper()


def far_d_atom_bound(dmin, amax, strip=False):
    """bound X (all atoms of the far-d chart, all Taylor coefficients) for d >= dmin, 0 <= a <= amax (amax <= 250):
    phit_d - sqrt(eta), phit_b - sqrt(eta) (Cauchy radius 3 margin), (phit_d - phit_b)/a (strip),
    Om_b atom nu_b e^{-b(1+2eps)}/(1+2eps) - e^{-b/3}/(c nu_b), sg phi(-x) - 1, tau-term."""
    d = arb(dmin)
    x = d - 3                                   # smallest real part of d' (radius 3: also covers phit' by Cauchy)
    Xphi, Pphi = phit_bounds(x)
    xb = d - 3                                   # b' = a' + d', Re b' >= d - 3 (a' within 1 of a >= 0... >= -1)
    # Om_b atom: |nu_b| <= (1/xb + 1/37)/0.998, |1/nu_b| <= |b'| <= amax + d + 3
    Xom = ((1 / xb + arb(1) / 37) / arb('0.998') * (-xb).exp() + arb('0.52') * (amax + d + 3) * (-(xb / 3)).exp()).upper()
    # Gam_z - 1 for z = b', d': e^{-z} ph_z + yh_z^2 e^{-2z/3}, |ph_z| <= 1 + 1.06 |z|, |yh_z| <= 0.74 |z|
    zz = amax + d + 3
    Xg = ((1 + arb('1.06') * zz) * (-x).exp() + arb('0.55') * zz ** 2 * (-(2 * x / 3)).exp()).upper()
    # psi - 1 = phi(-x_) - 1, |x_| = |dif|^2 e^{-(1/2+lam) d}, |dif| <= (sqrt(|b'|) + sqrt(|d'|)) * Pphi
    Xpsi = ((2 * zz.sqrt() * Pphi) ** 2 * (-((arb(1) / 2 + LAM) * x)).exp()).upper()
    Z1 = 3 * Xg + 2 * Xpsi                       # |sg psi - 1| <= |sg - 1| + |psi - 1| + products
    # tau-term e^{-(1/6-lam) d} Nt/(d (kh + sg)): |Nt| <= (0.74 |b'| + 0.74 |d'|)^2 (1 + small) + e^{-x/3} (...);
    # strip: Nt/a^2 bounded by its maximum on |a'| = 5 divided by 25 (Nt has a double zero at a' = 0), where
    # |yh_b e^{-a'/3}| <= 0.74 |b'| e^{5/3}.
    if strip:
        nt = (arb('0.74') * (d + 9) * arb(5 / 3).exp() + arb('0.74') * (d + 1)) ** 2 * 2 / 25
    else:
        nt = (arb('0.74') * zz + arb('0.74') * (d + 1)) ** 2 * 2
    nt = nt + 10 * zz ** 2 * (-(x / 3)).exp()
    Xtau = ((-((arb(1) / 6 - LAM) * x)).exp() * nt / ((d - 1) * arb('1.99'))).upper()
    X = max(float(Xphi), float(Xom), float(Z1), float(Xtau))
    return X, {'phit': float(Xphi), 'Om_b': float(Xom), 'sg psi - 1': float(Z1), 'tau': float(Xtau)}


def a_tail_atom_bound(amin, dmax):
    """bound X of the atoms of the a-tail chart (a >= amin, 0 <= d <= dmax):
    e^{-a}, e^{-a/3}, e^{-a(1+2eps)}, Q1 = yh_b e^{-a/3}, Q2 = ph_b e^{-a}, Om_a atom, Om_b atom, Gam_b - 1,
    PH = Phihat(b) e^{-mu a}; Cauchy radius 1 in a and d (Re a' >= amin - 1, |a'| unbounded but every bound
    poly(a) e^{-c a} is decreasing for a >= amin >= 30)."""
    a = arb(amin)
    xa = a - 1
    zb = a + dmax + 2                            # bound for |b'| at a = amin (the factor grows only polynomially)
    E3 = (-(xa / 3)).exp()
    Xq1 = arb('0.74') * zb * E3
    Xq2 = (1 + arb('1.06') * zb) * (-xa).exp()
    Xoa = ((1 / xa + arb(1) / 37) / arb('0.998') * (-xa).exp() + arb('0.52') * (a + 1) * E3)
    Xob = ((1 / xa + arb(1) / 37) / arb('0.998') * (-xa).exp() + arb('0.52') * zb * E3)
    Xgb = (1 + arb('1.06') * zb) * (-xa).exp() + arb('0.55') * zb ** 2 * (-(2 * xa / 3)).exp()
    Xph, Pph = phit_bounds(xa - 1)
    Xp = zb.sqrt() * Pph * (-(MU * xa)).exp()
    vals = {'e^-a/3 and e^-a': float(E3.upper()), 'Q1': float(Xq1.upper()), 'Q2': float(Xq2.upper()),
            'Om_a': float(Xoa.upper()), 'Om_b': float(Xob.upper()), 'Gam_b - 1': float(Xgb.upper()),
            'PH': float(Xp.upper())}
    return max(vals.values()), vals


def double_tail_bound(amin, dmin):
    """atoms of the double tail (a >= amin, d >= dmin): the far-d atoms (b >= d, so amax = 0 in far_d_atom_bound gives
    valid, larger bounds: every b-dependent bound is decreasing in b), the exponential part of Om_a, and the term
    sqrt(1 + a w) phit_b e^{-mu a} of M, bounded by sqrt(2 + a) |phit| e^{-mu (a-1)} (decreasing for a >= 10) at amin."""
    Xf, _ = far_d_atom_bound(dmin, 0)
    _, va = a_tail_atom_bound(amin, 0)
    _, Pph = phit_bounds(arb(dmin) - 3)
    Xm = ((2 + arb(amin)).sqrt() * Pph * (-(MU * (arb(amin) - 1))).exp()).upper()
    return max(Xf, va['Om_a'], float(Xm))


if __name__ == '__main__':
    for dmin, amax, strip in ((512, 250, False), (512, 3, True), (1024, 250, False)):
        print('far-d atoms, d >=', dmin, 'a <=', amax, 'strip' if strip else '', far_d_atom_bound(dmin, amax, strip))
    for amin in (240, 250, 300):
        print('a-tail atoms, a >=', amin, a_tail_atom_bound(amin, 512))
