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


def _up(x):
    """float upper bound of an arb (nudged up by 2^-50 against rounding to nearest)."""
    return float(x.upper()) * (1 + 2.0 ** -50)


def _a_tail_atoms(amin, dmax, complex_eps):
    """sup bounds of the a-tail atoms at a = amin (every bound is decreasing in a for a >= 100, also after the
    factors a^2 and (a + dmax + 2) used below), on the polydisc |a' - a| <= 1, |d' - d| <= 1 (0 <= d <= dmax), so
    Re a' >= a - 1, Re b' >= a - 2 (d >= 0), |Im a'| <= 1, |Im b'| <= 2, |a'| <= a + 1, |b'| <= a + dmax + 2 =: zb;
    eps real in [0, 1/37] (complex_eps False), or eps' complex with |eps' - eps| <= r = 1/(4 zb) (complex_eps True).
    With u = zeta eps' (zeta = a', b'): Re u >= -dl, |Im u| <= 2/37 + dl, where dl = zb r (= 1/4, resp. 0); hence
    |e^{-zeta eps'}| <= e^{dl}, |phi(-u)| <= e^{dl}, Re phi(-u) >= cos(2/37 + dl) / (1 + max(Re u, 0)), so
    |nu(zeta)| <= (1/Re zeta + epsmax)/cos(2/37 + dl), |1/nu(zeta)| <= e^{dl} |zeta|; |1/(1 + 2 eps')| <= 1/(1 - 2r),
    |1 + 2 eps'| <= 1 + 2 epsmax, |1/c| <= (1 + epsmax)/2, |1/sqrt(c2)| <= sqrt((1 + epsmax)(1 + 2 epsmax)/2).
    Atoms: Zea = nu_a e^{-a(1+2eps)}; Q1 = yh_b e^{-a/3}, yh = 1/(nu sqrt(c2)); Q2 = ph_b e^{-a},
    ph = e^{-2 z eps} + (1+2eps) e^{-z eps}/nu_z; Om atom (z = a, b) nu_z e^{-z(1+2eps)}/(1+2eps) - e^{-z/3}/(c nu_z);
    Gam_b - 1 = -e^{-b} ph_b - e^{-2b/3} yh_b^2; PH = Phihat(b) e^{-mu a} (eps-free), |Phihat| <= sqrt|b'| |phit|.
    (Fix of 2026-10-10: the first version used Re b' >= a - 1 for the b-exponentials of Om_b and Gam_b - 1; the
    correct a - 2 changes those two bounds by a factor <= e, inside the factor 10 applied by every caller.)"""
    a = arb(amin)
    xa, xb = a - 1, a - 2
    za, zb = a + 1, a + dmax + 2
    if complex_eps:
        r = 1 / (4 * zb)
        dl = arb(1) / 4
    else:
        r = arb(0)
        dl = arb(0)
    epsmax = arb(1) / 37 + r
    kc = (arb(2) / 37 + dl).cos().lower()
    eq = dl.exp()
    inv12 = 1 / (1 - 2 * r)
    c12 = 1 + 2 * epsmax
    ic = (1 + epsmax) / 2
    isc2 = ((1 + epsmax) * (1 + 2 * epsmax) / 2).sqrt()
    nub = lambda x: (1 / x + epsmax) / kc
    inu = lambda z: eq * z
    E3 = (-(xa / 3)).exp()
    vals = {
        'e^-a/3 and e^-a': E3,
        'Zea': nub(xa) * eq ** 2 * (-xa).exp(),
        'Q1': inu(zb) * isc2 * E3,
        'Q2': (eq ** 2 + c12 * eq * inu(zb)) * (-xa).exp(),
        'Om_a': nub(xa) * eq ** 2 * (-xa).exp() * inv12 + ic * inu(za) * E3,
        'Om_b': nub(xb) * eq ** 2 * (-xb).exp() * inv12 + ic * inu(zb) * (-(xb / 3)).exp(),
        'Gam_b - 1': (-xb).exp() * (eq ** 2 + c12 * eq * inu(zb)) + (-(2 * xb / 3)).exp() * (inu(zb) * isc2) ** 2,
    }
    Xph, Pph = phit_bounds(xa - 1)
    vals['PH'] = zb.sqrt() * arb(Pph) * (-(MU * xa)).exp()
    vals = {k: _up(v) for k, v in vals.items()}
    return max(vals.values()), vals


def a_tail_atom_bound(amin, dmax):
    """bound X of the atoms of the a-tail chart (a >= amin, 0 <= d <= dmax, real eps in [0, 1/37]); by Cauchy
    (radius 1 in a and d) X bounds every (a, d)-Taylor coefficient of every atom."""
    return _a_tail_atoms(amin, dmax, False)


def a_tail_atom_bound_ceps(amin, dmax):
    """sup of the atoms on the polydisc x the complex eps-disc of radius 1/(4 (a + dmax + 2)) (see _a_tail_atoms);
    Cauchy then bounds every coefficient d_a^i d_d^j d_eps / (i! j!) by 4 (a + dmax + 2) times this value."""
    return _a_tail_atoms(amin, dmax, True)


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
