"""Rigorous lower bound of the normalised margin R of inequality (C) over a box, by directed endpoint evaluation.
Ansh Mishra, Aryan Senthilkumar.

With q := (1-w^2) a^2 c^2,  m_P := e^{RE} E_P,  g_G := e^{-theta RE} theta E_G/(1-theta)^2  one has exactly
    R = m_P phi1(q m_P) - g_G phi2(theta q g_G),      X_P = q m_P,  Y_G = theta q g_G,
and  m phi1(q m) = log(1+qm)/q  is increasing in m and decreasing in q,  g phi2(t q g) = -log(1-tqg)/(tq)  is
increasing in g, t, q.  Hence over a box
    R >= m_P^lo phi1(q^hi m_P^lo) - g_G^hi phi2(theta^hi q^hi g_G^hi)
with  m_P^lo = e^{sqrt(z^lo)} 8 Ch[z-^lo, z^lo, z+^lo]                          (M1)
      g_G^hi = e^{-theta^lo RE^lo} theta^hi/(1-theta^hi)^2 max(E_G^hi, 0)          (E_G >= 0: Ando-Hiai)
      E_G^hi = 2[ S_a^hi S_b^hi (cosh a^hi U_theta[lo nodes]^hi + cosh b^hi U_{1-theta}[lo nodes]^hi)
                  - 4 (theta(1-theta))^2_lo Ch[theta_lo^2 (z-, z, z+)^lo] ]          (M1), (M2)
Exact ranges of z, z-, z+, q, b and lower bounds of the C-nodes are computed from the box corners.
Certificate (I): eps_P^lo = q^lo 8 Ch[z-^lo, z^lo, z+^lo] >= 1 implies (C) directly (G >= 2).
"""
from flint import arb, ctx
from rcore import ch_dd, u_dd_point, shc, fact, _up


def A(x):
    return arb(x)


def _phi1_pt(x):
    xa = abs(float(x.mid())) + float(x.rad())
    if xa < 1e-6:
        return 1 - x / 2 + arb(0, xa * xa / 3 / (1 - xa) * 1.0001)
    return (1 + x).log() / x


def _phi2_pt(y):
    ya = abs(float(y.mid())) + float(y.rad())
    if ya < 1e-6:
        return 1 + y / 2 + arb(0, ya * ya / 3 / (1 - ya) * 1.0001)
    return -(1 - y).log() / y


def _zf(a, c, w):
    return A(a) * A(a) + A(c) * A(c) + 2 * A(a) * A(c) * A(w)


def zmin_at(a0, a1, c0, c1, w):
    """Rigorous lower bound of min over [a0,a1]x[c0,c1] (a, c >= 0) of z = a^2 + c^2 + 2acw at fixed w (float or
    exact arb).  z is convex in (a, c): its minimum is at a vertex or at an edge-interior critical point; on the edge
    a = a_v the unconstrained minimum is a_v^2 (1 - w^2) (at c* = -a_v w), which is <= the constrained one and equals
    it when c* lies in [c0, c1]; it is included whenever c* may lie in [c0, c1]."""
    wf = float(A(w).mid())
    cands = [_zf(a, c, w) for a in (a0, a1) for c in (c0, c1)]
    if wf < 1e-12:
        omw2 = 1 - A(w) * A(w)
        for av in (a0, a1):
            cs = -av * wf
            if c0 - 1e-9 <= cs <= c1 + 1e-9:
                cands.append(A(av) * A(av) * omw2)
        for cv in (c0, c1):
            as_ = -cv * wf
            if a0 - 1e-9 <= as_ <= a1 + 1e-9:
                cands.append(A(cv) * A(cv) * omw2)
    lo = min((x.lower() for x in cands), key=lambda v: float(v))
    for x in cands:
        if x.lower() < lo:
            lo = x.lower()
    if lo < 0:
        lo = A(0)
    return lo


def zmax_at(a0, a1, c0, c1, w):
    """Upper bound of max over the rectangle of z at fixed w (convexity: a vertex)."""
    hi = None
    for a in (a0, a1):
        for c in (c0, c1):
            u = _zf(a, c, w).upper()
            if hi is None or u > hi:
                hi = u
    return hi


def zrange(a0, a1, c0, c1, w0, w1):
    """Rigorous [lower, upper] bounds of z = a^2 + c^2 + 2acw over the box (z increasing in w since ac >= 0)."""
    return zmin_at(a0, a1, c0, c1, w0), zmax_at(a0, a1, c0, c1, w1)


def box_bounds(th0, th1, a0, a1, c0, c1, w0, w1):
    """Returns dict with rigorous lower bound Rlo of R and lower bound epsPlo of eps_P over the box.
    All inputs are exact binary floats with 0 <= th0 < th1 <= 1/2, 0 <= a0 <= a1, 0 <= c0 <= c1, -1 <= w0 <= w1 <= 1."""
    T0, T1 = A(th0), A(th1)
    zlo, zhi = zrange(a0, a1, c0, c1, w0, w1)
    dm = max(0.0, a0 - c1, c0 - a1)
    zm_lo = A(dm) * A(dm)
    zp_lo = (A(a0) + A(c0)) ** 2
    # q = (1-w^2) a^2 c^2
    if w0 <= 0 <= w1:
        omw2_hi = A(1)
    else:
        wm = min(abs(w0), abs(w1))
        omw2_hi = 1 - A(wm) * A(wm)
    wM = max(abs(w0), abs(w1))
    omw2_lo = 1 - A(wM) * A(wM)
    q_hi = (omw2_hi * A(a1) ** 2 * A(c1) ** 2).upper()
    q_lo = (omw2_lo * A(a0) ** 2 * A(c0) ** 2).lower()
    if q_lo < 0:
        q_lo = A(0)
    # E_P lower
    chP_lo = ch_dd([zm_lo, zlo, zp_lo]).lower()
    EP_lo = 8 * chP_lo
    RE_lo = zlo.sqrt().lower() if zlo > 0 else A(0)
    mP_lo = (RE_lo.exp() * EP_lo).lower()
    epsP_lo = (q_lo * EP_lo).lower()
    # b range
    b0 = (T0 * A(c0) / (1 - T0)).lower()
    b1 = (T1 * A(c1) / (1 - T1)).upper()
    if b0 < 0:
        b0 = A(0)
    # C-node lower bounds
    dab_lo = A(a0) - b1
    dab_hi = A(a1) - b0
    if dab_lo.upper() >= 0 or dab_hi.lower() <= 0:
        # interval [a0-b1, a1-b0] may contain 0
        if dab_lo.upper() >= 0 and dab_hi.lower() <= 0:
            mind = A(0)
        elif dab_lo.lower() > 0:
            mind = dab_lo.lower()
        elif dab_hi.upper() < 0:
            mind = (-dab_hi).lower()
        else:
            mind = A(0)
    else:
        mind = A(0)
    if mind < 0:
        mind = A(0)
    Cm_lo = mind.cosh().lower()
    sinh_ab_lo = (A(a0).sinh() * b0.sinh()).lower()
    if sinh_ab_lo < 0:
        sinh_ab_lo = A(0)
    Cw_lo = (Cm_lo + (1 - A(w1)) * sinh_ab_lo).lower()
    Cp_lo = (A(a0) + b0).cosh().lower()
    one = A(1)
    nodes = [x if x > one else one for x in (Cm_lo, Cw_lo, Cp_lo)]
    # U at lo nodes, theta in [th0, th1], centred form
    thm = (T0 + T1) / 2
    thr = ((T1 - T0) / 2).upper()
    TH = T0.union(T1)
    Uth = u_dd_point(thm, nodes) + arb(0, thr) * u_dd_point(TH, nodes, dt=True)
    U1th = u_dd_point(1 - thm, nodes) + arb(0, thr) * u_dd_point(1 - TH, nodes, dt=True)
    Uth_hi = Uth.upper()
    U1th_hi = U1th.upper()
    Sa_hi = (shc(A(a1)) ** 2).upper()
    Sb_hi = (shc(b1) ** 2).upper()
    ca_hi = A(a1).cosh().upper()
    cb_hi = b1.cosh().upper()
    tt_lo = (T0 * (1 - T0)) ** 2
    chR_lo = ch_dd([T0 * T0 * zm_lo, T0 * T0 * zlo, T0 * T0 * zp_lo]).lower()
    EG_hi = (2 * (Sa_hi * Sb_hi * (ca_hi * Uth_hi + cb_hi * U1th_hi) - 4 * tt_lo.lower() * chR_lo)).upper()
    if EG_hi < 0:
        EG_hi = A(0)
    gG_hi = ((-T0 * RE_lo).exp() * T1 / (1 - T1) ** 2 * EG_hi).upper()
    YG_hi = (T1 * q_hi * gG_hi).upper()
    out = dict(epsP_lo=epsP_lo, mP_lo=mP_lo, gG_hi=gG_hi, q_hi=q_hi, YG_hi=YG_hi, EG_hi=EG_hi, EP_lo=EP_lo)
    # certificate F (unnormalised):  F = theta log(1+X_P) + log(1-Y_G) >= theta0 log(1 + X_P^lo) - min(theta1 RE^hi, -log(1-Y_G^hi))
    # (uses 1 - Y_G = e^{-rho}(G - e^{-rho}) >= e^{-rho} since G >= 2, i.e. -log(1-Y_G) <= rho = theta RE)
    RE_hi = zhi.sqrt().upper()
    XP_lo = (RE_lo.exp() * q_lo * EP_lo).lower()
    if XP_lo < 0:
        XP_lo = A(0)
    sub = (T1 * RE_hi).upper()
    if YG_hi < 1:
        lg = (-(1 - YG_hi).log()).upper()
        if lg < sub:
            sub = lg
    out['Flo'] = (T0 * (1 + XP_lo).log() - sub).lower()
    if not (YG_hi < 1):
        out['Rlo'] = A(-1e300)
        return out
    term1 = (mP_lo * _phi1_pt(q_hi * mP_lo)).lower()
    term2 = (gG_hi * _phi2_pt(YG_hi)).upper()
    out['Rlo'] = (term1 - term2).lower()
    return out


def dw_lower(th0, th1, a0, a1, c0, c1, w0, w1):
    """Rigorous lower bound D_lo with  dR/dw >= a c D_lo  on the box (a, c > 0 interior points).
    From R = Psi1(q, m_P) - Psi2(q, g_G):
      dR/dw = Psi1_m m_P,w - Psi2_g g_G,w + (Psi1_q - Psi2_q) q_w,
      m_P,w = e^{RE} [ (ac/RE) E_P + 16 ac Ch[z-,z,z,z+] ] >= ac e^{RE} E_P / RE,
      -Psi2_g g_G,w >= -Psi2_g theta/(1-theta)^2 e^{-theta RE} 2 S_a S_b |V[C-,C,C,C+]| sinh a sinh b,
      |V[4 nodes]| <= cosh a |U_th'''(1)|/6 + cosh b |U_{1-th}'''(1)|/6,  |U_t'''(1)| = t(1-t^2)(4-t^2)(9-t^2)/105,
      (Psi1_q - Psi2_q) q_w >= -[w<0] 2|w| a^2 c^2 (m_P^2/2 + theta g_G^2/(1-Y_G)),
      Psi1_m = 1/(1+X_P), Psi2_g = 1/(1-Y_G)."""
    T0, T1 = A(th0), A(th1)
    zlo, zhi = zrange(a0, a1, c0, c1, w0, w1)
    dm = max(0.0, a0 - c1, c0 - a1)
    dM = max(a1 - c0, c1 - a0)
    zm_lo, zm_hi = A(dm) * A(dm), A(dM) * A(dM)
    zp_lo, zp_hi = (A(a0) + A(c0)) ** 2, (A(a1) + A(c1)) ** 2
    if w0 <= 0 <= w1:
        omw2_hi = A(1)
    else:
        wm = min(abs(w0), abs(w1))
        omw2_hi = 1 - A(wm) * A(wm)
    q_hi = (omw2_hi * A(a1) ** 2 * A(c1) ** 2).upper()
    EP_lo = (8 * ch_dd([zm_lo, zlo, zp_lo])).lower()
    EP_hi = (8 * ch_dd([zm_hi, zhi, zp_hi])).upper()
    RE_lo = zlo.sqrt().lower() if zlo > 0 else A(0)
    RE_hi = zhi.sqrt().upper()
    if not (RE_hi > 0):
        return A(-1e300)
    mP_hi = (RE_hi.exp() * EP_hi).upper()
    XP_hi = (q_hi * mP_hi).upper()
    o = box_bounds(th0, th1, a0, a1, c0, c1, w0, w1)
    gG_hi, YG_hi = o['gG_hi'], o['YG_hi']
    if not (YG_hi < 1):
        return A(-1e300)
    b1 = (T1 * A(c1) / (1 - T1)).upper()
    TH = T0.union(T1)
    def u3(t):
        return (t * (1 - t * t) * (4 - t * t) * (9 - t * t) / 105).upper()
    V4_hi = (A(a1).cosh() * u3(TH) + b1.cosh() * u3(1 - TH)).upper() / 6
    shab_hi = (shc(A(a1)) * shc(b1) * T1 / (1 - T1)).upper()        # sinh a sinh b/(ac) <= this
    Sa_hi = (shc(A(a1)) ** 2).upper()
    Sb_hi = (shc(b1) ** 2).upper()
    main = (RE_lo.exp() * A(EP_lo) / (RE_hi * (1 + XP_hi))).lower()
    negU = ((1 / (1 - YG_hi)) * T1 / (1 - T1) ** 2 * (-T0 * RE_lo).exp() * 2 * Sa_hi * Sb_hi * shab_hi * V4_hi).upper()
    if w0 < 0:
        wabs = max(abs(w0), abs(w1))
        negq = (2 * A(wabs) * A(a1) * A(c1) * (mP_hi * mP_hi / 2 + T1 * gG_hi * gG_hi / (1 - YG_hi))).upper()
    else:
        negq = A(0)
    return (main - negU - negq).lower()


def face_epsP_lo(a0, a1, c0, c1, w):
    """Rigorous lower bound of eps_P = (1-w^2) a^2 c^2 * 8 Ch[z-, z, z+] on the face {w} x box (w exact arb)."""
    W = A(w)
    q_lo = ((1 - W * W) * A(a0) ** 2 * A(c0) ** 2).lower()
    if q_lo < 0:
        q_lo = A(0)
    dm = max(0.0, a0 - c1, c0 - a1)
    nodes = [A(dm) * A(dm), zmin_at(a0, a1, c0, c1, W), (A(a0) + A(c0)) ** 2]
    return (q_lo * 8 * ch_dd(nodes)).lower()


def wcert(th0, th1, a0, a1, c0, c1, kmax=400):
    """Whole-column certificate W for the box Theta x A x C x [-1, 1] (PROOF.md Lemma 3.7).
    Choose t+ = 2^-k+, t- = 2^-k- (thinnest dyadic layers found) with eps_P >= 1 on the faces w = 1 - t+ and
    w = -1 + t- (faces are exact dyadic Arb numbers; working precision raised so that 1 -+ 2^-k is exact).  Then:
    bulk [-1+t-, 1-t+]: eps_P >= 1 by concavity of eps_P in w (Lemma 3.4(I));
    layer [1-t+, 1]:  F >= s [theta log(1+e^{RE*}) - y+/(1-y+)],  y+ = e^{-theta RE*} t+ K+,
                      K+ = 2 |V'(C-)| sinh a sinh b >= sup(-d eps_G/dw);
    layer [-1, -1+t-]: F >= s [theta log(1+e^{|a-c|}) - y-/(1-y-)], y- = e^{-theta |a-c|} t- K-,
                      K- = 4 theta^2 a c Ch'(theta^2 z(-1+t-)) >= sup(d eps_G/dw).
    Returns (True, info) if all checks pass."""
    from rcore import uf_derivs
    old_prec = ctx.prec
    base = max(old_prec, 160)
    ctx.prec = base
    try:
        T0, T1 = A(th0), A(th1)
        TH = T0.union(T1)
        two = A(2)

        def find_k(sign):
            kbest = None
            for k in range(1, kmax):
                ctx.prec = max(base, k + 96)          # 1 -+ 2^-k exact
                w = (1 - two ** (-k)) if sign > 0 else (-1 + two ** (-k))
                ok = face_epsP_lo(a0, a1, c0, c1, w) >= 1
                ctx.prec = base
                if ok:
                    kbest = k
                elif kbest is not None:
                    break
            return kbest
        kp = find_k(+1)
        km = find_k(-1)
        if kp is None or km is None:
            return False, 'no face'
        ctx.prec = max(base, max(kp, km) + 96)
        tp, tm = two ** (-kp), two ** (-km)
        if not (-1 + tm < 1 - tp):
            return False, 'faces'
        b0 = (T0 * A(c0) / (1 - T0)).lower()
        b1 = (T1 * A(c1) / (1 - T1)).upper()
        if b0 < 0:
            b0 = A(0)
        lo_d = A(a0) - b1
        hi_d = A(a1) - b0
        if lo_d.lower() > 0:
            mind = lo_d.lower()
        elif hi_d.upper() < 0:
            mind = (-hi_d).lower()
        else:
            mind = A(0)
        Cm_lo = mind.cosh().lower()
        if Cm_lo < 1:
            Cm_lo = A(1)
        ctx.prec = base
        U1 = uf_derivs(TH, A(Cm_lo), 1)[1]
        U1b = uf_derivs(1 - TH, A(Cm_lo), 1)[1]
        ctx.prec = max(base, max(kp, km) + 96)
        Vp_hi = (abs(U1).upper() * A(a1).cosh() + abs(U1b).upper() * b1.cosh()).upper()
        Kp = (2 * Vp_hi * A(a1).sinh() * b1.sinh()).upper()
        REp = zmin_at(a0, a1, c0, c1, 1 - tp).sqrt().lower()
        yp = ((-T0 * REp).exp() * tp * Kp).upper()
        if not (yp < 1):
            return False, 'y+'
        okp = (T0 * REp * (1 - yp) - yp).lower() >= 0
        zhi_m = zmax_at(a0, a1, c0, c1, -1 + tm)
        Chp = ch_dd([T1 * T1 * zhi_m, T1 * T1 * zhi_m]).upper()
        Km = (4 * T1 * T1 * A(a1) * A(c1) * Chp).upper()
        dm = max(0.0, a0 - c1, c0 - a1)
        ym = ((-T0 * A(dm)).exp() * tm * Km).upper()
        if not (ym < 1):
            return False, 'y-'
        okm = (T0 * (1 + A(dm).exp()).log() * (1 - ym) - ym).lower() >= 0
        if okp and okm:
            return True, (kp, km, float(yp.mid()), float(ym.mid()))
        return False, ('layer', okp, okm, float(yp.mid()), float(ym.mid()))
    finally:
        ctx.prec = old_prec
