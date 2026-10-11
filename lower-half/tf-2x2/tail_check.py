"""NUMERICAL check of every intermediate inequality used in the tail lemma (PROOF.md Section 6) at sample points.
Ansh Mishra, Aryan Senthilkumar.

Region F2: theta in (0, 1/2], m = min(a, c) >= 1, M = max(a, c) >= 40.
Region F1: theta in (0, 1/2], 0 < m < 1, M >= 40.
Points: a fixed list of corner points (theta in {1/2, 1/4, 1e-4}, extreme and balanced (a, c)) followed by n random points.

Reference values (mpmath, 80 digits).  The integrals of Lemma 6.2(c) are evaluated from closed forms: substituting
lambda -> 1/lambda in (M2) shows that int lambda^{-t}/(1 + 2C lambda + lambda^2) is even in t, hence
  s_th I_a = |U_th'(C-)|,  s_th I_b = |U_{1-th}'(C-)|,  s_th II_a = U_th''(C-),  s_th II_b = U_{1-th}''(C-),
with U_t(cosh d) = sinh(td)/sinh d differentiated in closed form (evaluated with 160 digits).  At every qstep-th
point the four integrals are also computed by quadrature in s = log lambda (subintervals of length <= 3) and compared
with the closed forms (relative tolerance 1e-6); the largest relative deviation is printed.
Every explicit bound of the proof is compared with the exact quantity; a violated inequality is printed as VIOLATION.
Inequalities that are equalities in some case (Delta >= M - m) or strict only by a relative e^{-2t}
(the lower bound for RHS_T) are compared with relative tolerance 1e-60.  delta = (a + c) - R1 ~ e^{-(a+c)} is computed
with 120 + 0.45(a + c) digits.  At the end the largest ratio
(left side / right side) of each inequality is printed.
Usage: python tail_check.py seed n [qstep]
"""
import sys, random
import mpmath as mp

mp.mp.dps = 80
seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
n = int(sys.argv[2]) if len(sys.argv) > 2 else 200
qstep = int(sys.argv[3]) if len(sys.argv) > 3 else 5
random.seed(seed)
TOL = mp.mpf(10) ** -60


def shc(x):
    x = mp.mpf(x)
    return mp.sinh(x) / x if x != 0 else mp.mpf(1)


def psi(R):
    return R / (1 - mp.exp(-R)) if R > 0 else mp.mpf(1)


def U1abs(t, d):
    """|U_t'(C)| at C = cosh d (closed form; limit t(1-t^2)/3 at d = 0)."""
    if d < mp.mpf('1e-15'):
        return t * (1 - t * t) / 3
    with mp.workdps(160):
        v = ((1 - t) * mp.sinh((1 + t) * d) - (1 + t) * mp.sinh((1 - t) * d)) / (2 * mp.sinh(d) ** 3)
    return +v


def U2(t, d):
    """U_t''(C) at C = cosh d (closed form; limit t(1-t^2)(4-t^2)/15 at d = 0)."""
    if d < mp.mpf('1e-15'):
        return t * (1 - t * t) * (4 - t * t) / 15
    with mp.workdps(160):
        sd, cd = mp.sinh(d), mp.cosh(d)
        N1 = t * mp.cosh(t * d) * sd - mp.sinh(t * d) * cd
        Ud = N1 / sd ** 2
        Udd = ((t * t - 1) * mp.sinh(t * d) * sd ** 2 - 2 * N1 * cd) / sd ** 3
        v = (Udd * sd - Ud * cd) / sd ** 3
    return +v


def quad_s(g, d):
    """int_0^inf g(lam) dlam via lam = e^s, breakpoints at s = -d, 0, d and subintervals of length <= 3."""
    f = lambda s: g(mp.exp(s)) * mp.exp(s)
    lo, hi = -d - 80, d + 80
    k = max(60, int(mp.ceil((hi - lo) / 3)))
    pts = sorted(set([lo + (hi - lo) * j / k for j in range(k + 1)] + [-d, d, mp.mpf(0)]))
    return mp.quad(f, [-mp.inf] + pts + [mp.inf])


def integrals_quad(th, d):
    ed, emd = mp.exp(d), mp.exp(-d)
    Ia = quad_s(lambda l: 2 * l ** (1 - th) / ((l + ed) ** 2 * (l + emd) ** 2), d)
    Ib = quad_s(lambda l: 2 * l ** (2 - th) / ((l + ed) ** 2 * (l + emd) ** 2), d)
    IIa = quad_s(lambda l: 8 * l ** (2 - th) / ((l + ed) ** 3 * (l + emd) ** 3), d)
    IIb = quad_s(lambda l: 8 * l ** (3 - th) / ((l + ed) ** 3 * (l + emd) ** 3), d)
    rule = mp.mp._tanh_sinh          # drop the per-interval node caches (they grow with every new d)
    rule.transformed_cache.clear()
    rule.interval_count.clear()
    return Ia, Ib, IIa, IIb


bad = []
worst = {}
qdev = [mp.mpf(0)]


def chk(name, ok, info):
    if not ok:
        bad.append((name, info))
        print('VIOLATION', name, info, flush=True)


def le(name, lhs, rhs, info, tol=0):
    """check lhs <= rhs (rhs > 0), up to relative tolerance tol; record the ratio lhs/rhs."""
    r = lhs / rhs if rhs > 0 else (mp.mpf(0) if lhs <= 0 else mp.inf)
    if name not in worst or r > worst[name][0]:
        worst[name] = (r, info)
    chk(name, lhs <= rhs + tol * abs(rhs), (info, mp.nstr(r, 8)))


def point(th, a, c, region, do_quad):
    th, a, c = mp.mpf(th), mp.mpf(a), mp.mpf(c)
    m, M = min(a, c), max(a, c)
    b = th * c / (1 - th)
    s_th = mp.sin(mp.pi * th) / mp.pi
    d = abs(a - b)
    info = (float(th), float(a), float(c))
    # exact integrals (closed forms) and the quadrature cross-check
    Ia, Ib = U1abs(th, d) / s_th, U1abs(1 - th, d) / s_th
    IIa, IIb = U2(th, d) / s_th, U2(1 - th, d) / s_th
    if do_quad:
        for ex, qv, nm in zip((Ia, Ib, IIa, IIb), integrals_quad(th, d), ('I_a', 'I_b', 'II_a', 'II_b')):
            dev = abs(qv - ex) / ex
            qdev[0] = max(qdev[0], dev)
            chk('quadrature = closed form (' + nm + ')', dev <= mp.mpf('1e-6'), (info, mp.nstr(dev, 5)))
    # Lemma 6.2(d), both regions
    Ia_bd1 = 2 * mp.exp(-2 * d) * (mp.exp(th * d) / (2 - th) + 2 * mp.sinh(th * d) / th + mp.exp(-th * d) / (2 + th))
    le('6.2(d) I_a <= first bound', Ia, Ia_bd1, info, TOL)
    le('6.2(d) I_a <= 2e^{-(2-th)d}[1.07 + min(1/th, 2d)]', Ia_bd1,
       2 * mp.exp(-(2 - th) * d) * (mp.mpf('1.07') + min(1 / th, 2 * d)), info, TOL)
    Ib_bd1 = 2 * mp.exp(-(1 + th) * d) * (1 / (1 - th) + 1 / (1 + th) + 1 / (3 - th))
    le('6.2(d) I_b <= first bound', Ib, Ib_bd1, info, TOL)
    le('6.2(d) I_b <= 6.8 e^{-(1+th)d}', Ib_bd1, mp.mpf('6.8') * mp.exp(-(1 + th) * d), info)
    chk('s_theta <= theta', s_th <= th, info)
    Vp = s_th * (mp.cosh(a) * Ia + mp.cosh(b) * Ib)            # |V'(C-)|, Lemma 6.2(c)
    if region == 'F2':
        h = a * c / (a + c)
        # delta = (a + c) - R1 ~ e^{-(a+c)}: E0, R1, R2, delta are computed with 120 + 0.45(a + c) digits so that the
        # subtraction (a + c) - R1 keeps full relative accuracy (at 80 digits it is pure rounding noise for a + c > 170)
        with mp.workdps(int(120 + 0.45 * float(a + c))):
            E0 = 2 * (mp.cosh(a) * mp.cosh(c) - mp.cosh(mp.sqrt(a * a + c * c)))
            R1 = mp.sqrt((a + c) ** 2 - 2 * a * c / E0)
            R2 = mp.sqrt((a - c) ** 2 + 2 * a * c / E0)
            delta = (a + c) - R1
        E0, R1, R2, delta = +E0, +R1, +R2, +delta
        eta0 = mp.mpf(1) / 2 - mp.exp(-mp.mpf(40) / 41)
        chk('h >= 40/41', h >= mp.mpf(40) / 41, info)
        le('E0 >= e^{a+c}(1/2 - e^{-h})', mp.exp(a + c) * (mp.mpf(1) / 2 - mp.exp(-h)), E0, info)
        le('e^{a+c}(1/2 - e^{-h}) >= eta0 e^{a+c}', eta0 * mp.exp(a + c), mp.exp(a + c) * (mp.mpf(1) / 2 - mp.exp(-h)), info, TOL)
        le('eta0 e^{a+c} >= 1 (hence E0 >= 1)', mp.mpf(1), eta0 * mp.exp(a + c), info)
        le('E0 >= 1', mp.mpf(1), E0, info)
        le('delta <= 2h/E0', delta, 2 * h / E0, info, TOL)
        le('2h/E0 <= 2.8e-16', 2 * h / E0, mp.mpf('2.8e-16'), info)
        Pp = 2 * a * c * (shc(R1) - shc(a) * shc(c))
        Pp_lo = mp.exp(a + c) * (h * (1 - mp.mpf('3e-16')) - mp.mpf(1) / 2)
        le('P+ >= e^{a+c}((1-3e-16)h - 1/2)', Pp_lo, Pp, info)
        chk('P+ > 0', Pp > 0, info)
        Kp = 2 * Vp * mp.sinh(a) * mp.sinh(b)
        LHS = mp.exp(-th * R1) * Kp
        Delta = d + (c - b)
        le('Delta >= M - m', M - m, Delta + TOL * M, info)     # equality when a = m <= b
        XA = (1 - th) * a + b - (1 + th) * c - (2 - th) * d
        XB = -th * a + 2 * b - (1 + th) * c - (1 + th) * d
        XA_cf = -Delta if a >= b else -Delta - 2 * (1 - th) * (b - a)
        XB_cf = -Delta - 2 * th * (a - b) if a >= b else -Delta
        chk('X_A, X_B identities', abs(XA - XA_cf) <= TOL * (a + c) and abs(XB - XB_cf) <= TOL * (a + c), info)
        mid = mp.exp(th * delta) * mp.exp(a + c) * ((mp.mpf('1.07') * th + min(1, 2 * th * d)) * mp.exp(XA)
                                                     + mp.mpf('3.4') * th * mp.exp(XB))
        le('e^{-th R1} K+ <= e^{th delta} e^{a+c}[(1.07 th + min(1, 2th d))e^{X_A} + 3.4 th e^{X_B}]', LHS, mid, info, TOL)
        le('... <= e^{th delta} e^{a+c} th (4.47 + 2 Delta) e^{-Delta}', mid,
           mp.exp(th * delta) * mp.exp(a + c) * th * (mp.mpf('4.47') + 2 * Delta) * mp.exp(-Delta), info, TOL)
        RHS = mp.mpf(1) / 2 * min(1, th * psi(R1)) * Pp
        le('(L+)', LHS, RHS, info)
        lhs4 = mp.exp(th * delta) * (mp.mpf('4.47') + 2 * Delta) * mp.exp(-Delta)
        hh = (1 - mp.mpf('3e-16')) * h - mp.mpf(1) / 2
        if th * (a + c - delta) <= 1:
            le('Step 4 (i): lhs <= 4.48', lhs4, mp.mpf('4.48'), info)
            le('Step 4 (i): 9.7 <= (1/2)(a+c-delta)((1-3e-16)h - 1/2)', mp.mpf('9.7'), (a + c - delta) / 2 * hh, info)
        else:
            le('Step 4 (ii): (4.47 + 2 Delta)e^{-Delta}(1 + 1e-15) <= (1-3e-16)h - 1/2',
               (mp.mpf('4.47') + 2 * Delta) * mp.exp(-Delta) * (1 + mp.mpf('1e-15')), hh, info)
            if m >= 20:
                le('Step 4 (ii) m >= 20: 40/3 <= h', mp.mpf(40) / 3, h, info, TOL)
            else:
                le('Step 4 (ii) m < 20: lhs <= 1e-7', (mp.mpf('4.47') + 2 * Delta) * mp.exp(-Delta) * (1 + mp.mpf('1e-15')),
                   mp.mpf('1e-7'), info)
        le('R2 <= |a - c| + 1', R2, abs(a - c) + 1, info)
        gm = mp.exp(m - 1) * (M - m + 1) / M
        lm = shc(a) * shc(c) - shc(R2)
        low5 = shc(M - m + 1) * ((1 - mp.exp(-80)) * shc(m) * gm - 1)
        le('Step 5: shc(a)shc(c) - shc(R2) >= shc(M-m+1)[(1-e^{-80}) shc(m) g(m) - 1]', low5, lm, info, TOL)
        le('Step 5: ... >= 1', mp.mpf(1), low5, info)
        le('(L-)', 2 * th, lm, info)
    else:
        t = M - m
        IIa_bd1 = mp.exp(-(3 - th) * d) * (48 / (9 - th * th) + min(8 / th, 16 * d))
        le('6.2(d) II_a <= first bound', IIa, IIa_bd1, info, TOL)
        le('6.2(d) II_a <= e^{-(3-th)d}[5.49 + min(8/th, 16d)]', IIa_bd1,
           mp.exp(-(3 - th) * d) * (mp.mpf('5.49') + min(8 / th, 16 * d)), info)
        IIb_bd1 = mp.exp(-(2 + th) * d) * (8 / (4 - th) + 8 / (1 - th) + 8 / (2 + th))
        le('6.2(d) II_b <= first bound', IIb, IIb_bd1, info, TOL)
        le('6.2(d) II_b <= 22.3 e^{-(2+th)d}', IIb_bd1, mp.mpf('22.3') * mp.exp(-(2 + th) * d), info)
        Vpp = s_th * (mp.cosh(a) * IIa + mp.cosh(b) * IIb)       # V''(C-), Lemma 6.2(c)
        LHS_T = mp.exp(-th * t) * (th / (1 - th)) ** 2 * shc(a) ** 2 * shc(b) ** 2 * Vpp
        MP = (t * mp.cosh(t) - mp.sinh(t)) / t ** 3
        RHS_T = mp.mpf(1) / 2 * min(1, th * psi(t)) * MP
        le('RHS_T >= min(1, th t)(t-1)e^t/(4t^3)', min(1, th * t) * (t - 1) * mp.exp(t) / (4 * t ** 3), RHS_T, info, TOL)
        if a == M:      # case a = M, c = m
            mid = mp.mpf('5.525') * mp.e ** 3 / 4 * th ** 2 * (th * (mp.mpf('5.49') + mp.mpf('22.3') * mp.cosh(1)) + 8) / a ** 2
            le('case a=M: LHS_T <= (5.525e^3/4)th^2[th(5.49 + 22.3 cosh 1) + 8]/a^2', LHS_T, mid, info)
            le('case a=M: ... <= 776 th^2/a^2', mid, 776 * th ** 2 / a ** 2, info)
        elif b < 1:     # case a = m, b < 1
            le('case a=m, b<1: LHS_T <= 258 th^2', LHS_T, 258 * th ** 2, info)
        else:           # case a = m, b >= 1
            mid = mp.mpf('1.3811') / c ** 2 * (mp.cosh(1) * mp.e ** 3 / 4 * (mp.mpf('5.49') * th + 8)
                                              + mp.mpf('5.575') * th * mp.exp(2 + 2 * th))
            le('case a=m, b>=1: LHS_T <= (1.3811/c^2)[cosh(1)(e^3/4)(5.49 th + 8) + 5.575 th e^{2+2th}]', LHS_T, mid, info)
            le('case a=m, b>=1: ... <= 193/c^2', mid, 193 / c ** 2, info)
            le('case a=m, b>=1: theta t >= 0.951', mp.mpf('0.951'), th * t, info)
        le('(T)', LHS_T, RHS_T, info)


corners = []
for th in ('0.5', '0.25', '1e-4'):
    for (a, c) in ((40, 40), (40, 1), (1, 40), (300, 300), (300, 1), (1, 300), (40, 39), (39, 40), (41, 40)):
        corners.append((th, a, c, 'F2'))
    for (a, c) in ((40, '0.999'), ('0.999', 40), (40, '1e-6'), ('1e-6', 40), (300, '0.5'), ('0.5', 300)):
        corners.append((th, a, c, 'F1'))
nF1 = nF2 = 0
for j, (th, a, c, region) in enumerate(corners):
    point(th, a, c, region, True)
    nF1 += region == 'F1'; nF2 += region == 'F2'
for it in range(n):
    th = random.choice([random.uniform(0.001, 0.5), 0.5, random.uniform(0.45, 0.5), 10 ** random.uniform(-4, -1)])
    M = random.choice([40, random.uniform(40, 80), random.uniform(40, 300)])
    region = random.choice(['F1', 'F2', 'F2'])
    if region == 'F2':
        m = random.choice([1, random.uniform(1, 5), random.uniform(1, M), M])
    else:
        m = random.choice([random.uniform(0.001, 1), 10 ** random.uniform(-6, 0)])
        m = min(m, 0.999999)
    a, c = (M, m) if random.random() < 0.5 else (m, M)
    point(th, a, c, region, it % qstep == 0)
    nF1 += region == 'F1'; nF2 += region == 'F2'
print('largest ratio (left side / right side) of each inequality:')
for name, (r, info) in worst.items():
    print(f'  {mp.nstr(r, 6):>14}  {name}   at (theta, a, c) = {info}')
print('largest relative deviation quadrature vs closed form:', mp.nstr(qdev[0], 5))
print(f'points: F1 {nF1}, F2 {nF2} (corners {len(corners)}); violations: {len(bad)}')
