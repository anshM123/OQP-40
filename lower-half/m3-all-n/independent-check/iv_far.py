"""Independent verifier, tail charts (own derivation and code).

Exact identities used (eps = 1/n or 0; nu(z) = eps/(1 - e^{-z eps}) = 1/(z phi(-z eps)), m(z) = nu(z) - eps = 1/(z phi(z eps)),
e^{-z eps} = m(z)/nu(z)):
  nu(z + h) = nu(z)/(1 + m(z) h phi(-h eps)),          1/nu(a + d) = 1/nu(a) + e^{-a eps}/nu(d)
  => nu_b = nu_a nu_d/(nu_d + nu_a - eps)  (no a or d needs to be finite),  log(d + h) = log d + log(1 + w h)  (w = 1/d).
log F (scaled nu-form):  -lam d + log(d nu_d) + (log nu_b - log nu_a)/2 - log(1+2eps) - (log Om_a + log Om_b)/2 + log(Dhat/d),
  Dhat/d = M^2 sg psi + tau',  M = phit_d - sqrt(1 + a w) phit_b e^{-mu a}  (Phihat(z) = -sqrt(z) phit(z), so
  Phihat_b e^{-mu a} - Phihat_d = sqrt(d) M);  for d >= 512 the atoms phit - sqrt(eta), sg psi - 1, tau', the
  exponential part of Om_b are bounded in iv_atoms.py (Cauchy, all jet coefficients).
Strip (0 <= a <= 3): G' = log(F/a) = -lam d + log(d nu_d) + (log nu_b - log Om_b)/2 + (log c - log S(-a))/2 - log(1+2eps)
  + log((M/a)^2 sg psi + tau'/a^2),  M/a = -v phi(a v) phit_d + e^{a v} (phit_d - phit_b)/a,  v = -mu + (w/2) Lg(a w),
  Lg(x) = log(1+x)/x  (sqrt(1 + a w) e^{-mu a} = e^{a v}).
Jets: variables (h_a, h_d) (partial derivatives at fixed eps); the cells in (w, eps) resp. (m_a, eps) enter as balls.
"""
from math import comb, factorial
import flint
from flint import arb, fmpq
import iv_jet as JJ
from iv_jet import Jet, Space, NotPos, ZERO, ONE
import iv_forms as FF
import iv_small as SM
import iv_atoms as AT

flint.ctx.prec = 200
LAM = arb(7) / 100
ETA = arb(7) / 10
MU = (arb(1) / 2 + LAM) / 2
SPT = Space(sorted({(i, j, 0) for i in range(4) for j in range(4) if i + j <= 3}, key=lambda m: (sum(m), m)))


def q(x):
    return arb(fmpq(x.numerator, x.denominator))


def atom(X, sp=SPT):
    return Jet([arb(0, arb(X))] * sp.n, sp)


def m_of(d, e):
    """m(d, eps) = 1/(d phi(d eps)) at thin d, e (arb)."""
    return 1 / (d * JJ._phi1_thin(d * e, 0)[0])


def m_range_w(w0, w1, e0, e1):
    """enclosure of m_d for d in [1/w1, 1/w0] (w0 = 0: d -> inf), eps in [e0, e1] (m decreasing in d and eps)."""
    hi = m_of(1 / q(w1), q(e0))
    lo = arb(0) if w0 == 0 else m_of(1 / q(w0), q(e1))
    return arb.union(lo, hi)


def c_Lg(x0, K):
    """Taylor coefficients of Lg(x) = log(1+x)/x = sum_k (-1)^k x^k/(k+1) at the ball x0, |x0| <= 1/50."""
    h = abs(x0).upper()
    if not (h <= arb(1) / 50):
        raise NotPos('Lg beyond 1/50')
    N = 40
    out = []
    for m in range(K + 1):
        s = ZERO
        p = ONE
        for k in range(m, N + 1):
            s += comb(k, m) * ((-1) ** k) * p / (k + 1)
            p = p * x0
        tail = 2 * comb(N + 1, m) * arb(h) ** (N + 1 - m)
        out.append(s + arb(0, tail.upper()))
    return out


def Phit_scalar():
    return ETA.sqrt()


# ---------------- far-d chart ----------------
def far_parts(A, w, md, eps, sp=SPT):
    """d-dependent exact jets on a (w, eps) cell: W = w(d), LDN = log(d nu_d) - const, nu_d jet, m_d jet."""
    Hd = Jet.var(ZERO, 1, sp)
    W = w / (1 + w * Hd)
    pd = (-(Hd * eps)).phi1()
    den = 1 + md * Hd * pd
    nd = (md + eps) / den
    LDN = (1 + w * Hd).log() - den.log()
    return Hd, W, nd, LDN


def logF_far_reg(A, w0, w1, e0, e1, X):
    """log F (up to a constant) on the cell, a-jet A (3 <= a <= 250), atoms bounded by X."""
    eps = arb.union(q(e0), q(e1)) if e1 > e0 else q(e0)
    w = arb.union(q(w0), q(w1)) if w1 > w0 else q(w0)
    md = m_range_w(w0, w1, e0, e1)
    e2 = 1 + 2 * eps
    c = 2 / (1 + eps)
    Hd, W, nd, LDN = far_parts(A, w, md, eps)
    na = FF.nu(A, eps)
    Ah = A + Hd
    den_b = 1 + md * Ah * (-(Ah * eps)).phi1()       # nu(d0 + a + h) = nu_d0/den_b
    nb = (md + eps) / den_b
    Oa = 1 - na * (1 - (-(A * e2)).exp()) / e2 - (-(A / 3)).exp() / (c * na)
    Ob = 1 - nb / e2 + atom(X)
    s = Phit_scalar()
    M = (s + atom(X)) - (1 + A * W).sqrt() * (s + atom(3 * X)) * (-(MU * A)).exp()
    DH = M * M * (1 + atom(X)) + atom(X)
    return (-LAM * Hd + LDN + (-den_b.log() - na.log()) / 2 - (Oa.log() + Ob.log()) / 2 + DH.log())


def logG_far_strip(A, w0, w1, e0, e1, X):
    """G' = log(F/a) (up to a constant), 0 <= a <= 3."""
    eps = arb.union(q(e0), q(e1)) if e1 > e0 else q(e0)
    w = arb.union(q(w0), q(w1)) if w1 > w0 else q(w0)
    md = m_range_w(w0, w1, e0, e1)
    e2 = 1 + 2 * eps
    c = 2 / (1 + eps)
    Hd, W, nd, LDN = far_parts(A, w, md, eps)
    # nu_b from nu_d and a (a may be 0): nu(d + a) = nu_d/(1 + m_d (a + h) phi(-(a+h) eps)) with the jet of d + a
    Ah = A + Hd
    den_b = 1 + md * Ah * (-(Ah * eps)).phi1()       # nu(d0 + a + h) = nu_d0/den_b; log nu_d0 is a constant
    nb = (md + eps) / den_b
    Ob = 1 - nb / e2 + atom(X)
    AW = A * W
    Lg = AW.compose(c_Lg(AW.c[0], SPT.order))
    v = -MU + (W / 2) * Lg
    s = Phit_scalar()
    Ma = -v * (A * v).phi1() * (s + atom(X)) + (A * v).exp() * atom(X)
    DHa = Ma * Ma * (1 + atom(X)) + atom(X)
    Sma = SM.S_jet(-A, Jet.const(eps, SPT))
    return (-LAM * Hd + LDN + (-den_b.log() - Ob.log()) / 2 - Sma.log() / 2 + DHa.log())


def logF_double(m0, m1, w0, w1, e0, e1, X):
    """a >= ~240 (m_a cell) and d >= 512 (w cell): every quantity naive over the cell."""
    eps = arb.union(q(e0), q(e1)) if e1 > e0 else q(e0)
    w = arb.union(q(w0), q(w1)) if w1 > w0 else q(w0)
    md = m_range_w(w0, w1, e0, e1)
    ma = arb.union(q(m0), q(m1))
    e2 = 1 + 2 * eps
    Hd, W, nd, LDN = far_parts(None, w, md, eps)
    Ha = Jet.var(ZERO, 0, SPT)
    da = 1 + ma * Ha * (-(Ha * eps)).phi1()
    na = (ma + eps) / da
    # nu_b around the base point b0 = a0 + d0: nu(b0 + H) = nu_b0/(1 + m_b0 H phi(-H eps)), H = h_a + h_d, with
    # m_b0 = m(a0 + d0) in [0, min(m_a, m_d)] (m is decreasing); only derivatives of log nu_b - log nu_a are needed.
    mb = arb.union(arb(0), arb(min(float(ma.upper()), float(md.upper()))) * (1 + arb('1e-15')))
    H = Ha + Hd
    db = 1 + mb * H * (-(H * eps)).phi1()
    nb = (mb + eps) / db
    Oa = 1 - na / e2 + atom(X)
    Ob = 1 - nb / e2 + atom(X)
    M = Phit_scalar() + atom(X)
    DH = M * M * (1 + atom(X)) + atom(X)
    return (-LAM * Hd + LDN + (-db.log() + da.log()) / 2 - (Oa.log() + Ob.log()) / 2 + DH.log())


# ---------------- a-tail chart (a >= 250 via m_a cells, 0 < d <= 512) ----------------
def logF_atail(ma, eps, D, X, form):
    """m_a ball, eps ball, D = d-jet (centre thin or box ball, variable h_d), atoms bounded by X (a >= amin)."""
    sp = D.sp
    e1, e2 = 1 + eps, 1 + 2 * eps
    c = 2 / e1
    c2 = 2 / (e1 * e2)
    sc2 = c2.sqrt()
    Ha = Jet.var(ZERO, 0, sp)
    na = (ma + eps) / (1 + ma * Ha * (-(Ha * eps)).phi1())
    ind = D * (-(D * eps)).phi1()                 # 1/nu_d (no division by d)
    den_ab = 1 + (na - eps) * ind                 # nu(a + d) = nu_a/(1 + m_a d phi(-d eps))
    nb = na / den_ab
    Oa = 1 - na / e2 + atom(X, sp)
    Ob = 1 - nb / e2 + atom(X, sp)
    Zea = atom(X, sp)                       # nu_a e^{-a(1+2eps)}
    Q1 = atom(X, sp)                        # yh_b e^{-a/3}
    Q2 = atom(X, sp)                        # ph_b e^{-a}
    PHb = atom(X, sp)                       # Phihat(b) e^{-mu a}
    Gb = 1 + atom(X, sp)
    if form == 'nu':
        yhd = ind / sc2
        phd = (-(2 * D * eps)).exp() + e2 * (-(D * eps)).exp() * ind
        emd, emd3 = (-D).exp(), (-(D / 3)).exp()
        Uh = (-(2 * D * eps)).exp() + (na - Zea) * (-(D * eps)).exp() * ind
        emd43 = emd * emd3
        t1 = Q1 - yhd
        Nt = (t1 * t1 + emd3 * (Q2 + phd - 2 * Uh) + emd43 * Uh * Uh + 2 * emd * Q1 * Uh * yhd
              - Q2 * phd * emd43 - Q2 * yhd * yhd * emd - phd * Q1 * Q1 * emd)
        kh = 1 - emd * Uh - Q1 * yhd * emd3 * emd3
        Gd = FF._cpgam(D, eps, c2, FF._ball(D).upper() <= 8) / c2
        sg = (Gb * Gd).sqrt()
        dif = PHb - D.phihat()
        dif2 = dif * dif
        xx = dif2 * (-((2 * MU) * D)).exp()
        Dh = (-((arb(1) / 6 - LAM) * D)).exp() * Nt / (kh + sg) + sg * dif2 * (-xx).phi1()
        return -LAM * D - ind.log() - den_ab.log() / 2 - (Oa.log() + Ob.log()) / 2 + Dh.log()
    # mixed form (small d)
    import iv_small
    Pd = (D * e2).phi1() / (D * eps).phi1()
    qa = (na - Zea) / e2
    dPhi = PHb * (-(MU * D)).exp() - iv_small.Phi_any(D)
    R = (-(dPhi * dPhi)).exp()
    Sd = iv_small.S_of(D, Jet.const(eps, sp))
    Bm = ((-(D * (arb(1) / 2 + eps))).exp() * (Pd - qa) - Q1 * sc2 * (-(D / 6)).exp() / c
          - (c2 * Gb).sqrt() / c * D * Sd.sqrt() * R)
    return -den_ab.log() / 2 + Bm.log() - (Oa.log() + Ob.log()) / 2


def atom_m(X, Xm, sp):
    """atom jet in (h_a, h_d, h_m): coefficients of m-order 0 in [-X, X], of m-order 1 in [-Xm, Xm]."""
    return Jet([arb(0, arb(Xm if m[2] else X)) for m in sp.monos], sp)


def logF_atail2(Mj, eps, D, X, Xm, form):
    """as logF_atail, with m_a a jet variable (third variable h_m) so that a mean-value form in m can be used.
    Atom bounds: X for the (h_a, h_d) coefficients; Xm for the coefficients of order 1 in h_m: since a = a(m, eps)
    and |da/dm| = 1/(m nu_a) = a^2 phi(a eps)^2 e^{-a eps} <= a^2 e^{a eps}, every such coefficient is
    <= (i+1) X a^2 e^{a eps} <= 3 X a^2 e^{a eps} (Cauchy in a), decreasing in a for a >= 10, taken at a_min."""
    sp = D.sp
    e1, e2 = 1 + eps, 1 + 2 * eps
    c = 2 / e1
    c2 = 2 / (e1 * e2)
    sc2 = c2.sqrt()
    Ha = Jet.var(ZERO, 0, sp)
    # m(a + h) = m/(m h phi(h eps) + e^{h eps}) (from e^{a eps} = 1 + eps/m); nu = m + eps.  Written without the
    # subtraction nu - eps, which loses the m-information when eps is a wide ball (dependency effect).
    ma_h = Mj / (Mj * Ha * (Ha * eps).phi1() + (Ha * eps).exp())
    na = ma_h + eps
    ind = D * (-(D * eps)).phi1()
    den_ab = 1 + ma_h * ind
    nb = na / den_ab
    A_ = lambda: atom_m(X, Xm, sp)
    Oa = 1 - na / e2 + A_()
    Ob = 1 - nb / e2 + A_()
    Zea, Q1, Q2, PHb = A_(), A_(), A_(), A_()
    Gb = 1 + A_()
    if form == 'nu':
        yhd = ind / sc2
        phd = (-(2 * D * eps)).exp() + e2 * (-(D * eps)).exp() * ind
        emd, emd3 = (-D).exp(), (-(D / 3)).exp()
        Uh = (-(2 * D * eps)).exp() + (na - Zea) * (-(D * eps)).exp() * ind
        emd43 = emd * emd3
        t1 = Q1 - yhd
        Nt = (t1 * t1 + emd3 * (Q2 + phd - 2 * Uh) + emd43 * Uh * Uh + 2 * emd * Q1 * Uh * yhd
              - Q2 * phd * emd43 - Q2 * yhd * yhd * emd - phd * Q1 * Q1 * emd)
        kh = 1 - emd * Uh - Q1 * yhd * emd3 * emd3
        Gd = FF._cpgam(D, eps, c2, FF._ball(D).upper() <= 8) / c2
        sg = (Gb * Gd).sqrt()
        dif = PHb - D.phihat()
        dif2 = dif * dif
        xx = dif2 * (-((2 * MU) * D)).exp()
        Dh = (-((arb(1) / 6 - LAM) * D)).exp() * Nt / (kh + sg) + sg * dif2 * (-xx).phi1()
        return -LAM * D - ind.log() - den_ab.log() / 2 - (Oa.log() + Ob.log()) / 2 + Dh.log()
    import iv_small
    Pd = (D * e2).phi1() / (D * eps).phi1()
    qa = (na - Zea) / e2
    dPhi = PHb * (-(MU * D)).exp() - iv_small.Phi_any(D)
    R = (-(dPhi * dPhi)).exp()
    Sd = iv_small.S_of(D, eps if isinstance(eps, Jet) else Jet.const(eps, sp))   # eps may be the jet variable (iv_tail3_run)
    Bm = ((-(D * (arb(1) / 2 + eps))).exp() * (Pd - qa) - Q1 * sc2 * (-(D / 6)).exp() / c
          - (c2 * Gb).sqrt() / c * D * Sd.sqrt() * R)
    return -den_ab.log() / 2 + Bm.log() - (Oa.log() + Ob.log()) / 2


# ---------------- conditions ----------------
def conds_ad(G):
    """L1 = G_a - G_d, L2 = -G_d, L3 = L1 L2 - (G_ad - G_dd), and their d/da and d/dd (from the order-3 jet)."""
    Ga, Gd = G.co(1, 0), G.co(0, 1)
    Gaa, Gad, Gdd = 2 * G.co(2, 0), G.co(1, 1), 2 * G.co(0, 2)
    Gaad, Gadd, Gddd = 2 * G.co(2, 1), 2 * G.co(1, 2), 6 * G.co(0, 3)
    L1, L2 = Ga - Gd, -Gd
    L3 = L1 * L2 - (Gad - Gdd)
    L1a, L2a = Gaa - Gad, -Gad
    L3a = L1a * L2 + L1 * L2a - (Gaad - Gadd)
    L1d, L2d = Gad - Gdd, -Gdd
    L3d = L1d * L2 + L1 * L2d - (Gadd - Gddd)
    return (L1, L2, L3), (L1a, L2a, L3a), (L1d, L2d, L3d)


def conds_strip(G, a):
    """N1 = a L1 = 1 + a (G_a - G_d), N2 = L2 = -G_d, N3 = a L3 = N1 N2 - a (G_ad - G_dd)  (G = log(F/a)), and d/da."""
    Ga, Gd = G.co(1, 0), G.co(0, 1)
    Gaa, Gad, Gdd = 2 * G.co(2, 0), G.co(1, 1), 2 * G.co(0, 2)
    Gaad, Gadd = 2 * G.co(2, 1), 2 * G.co(1, 2)
    N1 = 1 + a * (Ga - Gd)
    N2 = -Gd
    N3 = N1 * N2 - a * (Gad - Gdd)
    N1a = (Ga - Gd) + a * (Gaa - Gad)
    N2a = -Gad
    N3a = N1a * N2 + N1 * N2a - ((Gad - Gdd) + a * (Gaad - Gadd))
    return (N1, N2, N3), (N1a, N2a, N3a)
