"""Region A': rigorous Taylor models of H(theta, x, y) on boxes near s = 0, via Cauchy estimates and a DFT.

Box: |theta - th0| <= rt, |x - x0| <= r, |y - y0| <= r.  f(z) = H(th0 + z1, x0 + z2, y0 + z3).
1. Analyticity: on the closed polydisc P' = {|z_i| <= rho'_i} we check by ball arithmetic
      max |Im x| < pi/2 - 0.05,  max |Im Y| < pi/2 - 0.05  (Y = kappa y, kappa = theta/(1-theta)),  min |1-theta| > 0.1.
   Then 1 + u p and 1 + u q (p = e^x - 1, q = e^Y - 1, 0 <= u <= 1) stay in Re > 0, the integral
   J = int_0^1 (1+up)^{-1-theta} (1+uq)^{-2+theta} du is analytic on P', hence so is H (removable singularities on the
   axes, since Phi = xy H vanishes identically on x = 0 and on y = 0).
2. M' >= max_{P'} |f| = max over the torus T' (maximum principle).  On a cell of T' (complex balls) we use
      |g(x,y)| <= g(Re x, Re y) <= g(max Re x, max Re y)            [g = (1/2)E (S-T)^2 D_x D_y, |D_x| <= D_{Re x}]
      |tm| <= |theta| (|phi(-theta s)| + |phi(x)| |phi(Y)| |J|) / (|x| |y|),   |phi(z)| <= phi(Re z),
      |J| <= m_x^{-(1+theta_r)} m_Y^{-(2-theta_r)} exp(|theta_i| (|Im x| + |Im Y|)),  m_z = min(1, e^{Re z} cos(Im z)).
3. Samples on T = {|z_i| = rho_i} (point evaluations of formula (I')), DFT -> chat_alpha,
      |chat_alpha - c_alpha| <= M' prod (1/rho'_i)^{alpha_i} [prod 1/(1 - q_i^{N_i}) - 1],  q_i = rho_i/rho'_i.
4. Polynomial part + aliasing errors + Cauchy tails give rigorous bounds of H and of d/ds H = (H_x + H_y)/2 on
   sub-boxes; a sub-box (with some point s >= 0) is accepted if H > 0 ('P') or d/ds H > 0 ('C') on it.
"""
import sys
import json
import time
import math
from flint import arb, acb, ctx
import ecore as C

ctx.prec = 128
LIM = math.pi / 2 - 0.05


def disc(c, R):
    return acb(arb(c.real.mid(), arb(R).upper() + c.real.rad()), arb(c.imag.mid(), arb(R).upper() + c.imag.rad()))


def arc_ball(c0, R, a_lo, a_hi):
    am = (a_lo + a_hi) / 2
    h = (a_hi - a_lo) / 2
    c = acb(arb(c0) + arb(R) * arb(am).cos(), arb(R) * arb(am).sin())
    return disc(c, R * h * 1.0001)


def analytic_check(th0, x0, y0, rp):
    th = disc(acb(th0), rp[0]); x = disc(acb(x0), rp[1]); y = disc(acb(y0), rp[2])
    k = th / (1 - th)
    Y = k * y
    imx = float(abs(x.imag).upper()); imY = float(abs(Y.imag).upper())
    om = float(abs(1 - th).lower())
    return (imx < LIM and imY < LIM and om > 0.1), {'imx': imx, 'imY': imY, '1-th': om}


def g_upper_real(a, b):
    """upper bound of g(a', b') for a' <= a, b' <= b (g increasing): evaluate at (a, b) (real arb points)."""
    a = arb(a.upper()) + arb('1e-30')
    b = arb(b.upper()) + arb('1e-30')
    if abs(a) <= 1 and abs(b) <= 1:
        return C.g_series(a, b).upper()
    return C.g_point(a, b).upper()


def phi_upper_real(a):
    return C.phi(arb(a.upper())).upper()


def abs_lower(z):
    """Rigorous lower bound of |z| over a rectangular complex ball (Arb's abs() loses the lower bound for
    wide balls): distance from 0 to the rectangle."""
    rl, rh, il, ih = z.real.lower(), z.real.upper(), z.imag.lower(), z.imag.upper()
    # distance from 0 to [rl, rh]: rl if surely rl > 0, -rh if surely rh < 0, else 0 (safe)
    dr = rl if rl > 0 else (-rh if rh < 0 else arb(0))
    di = il if il > 0 else (-ih if ih < 0 else arb(0))
    return (dr * dr + di * di).sqrt().lower()


def H_abs_bound(th, x, y):
    """Rigorous upper bound of |H| over complex balls th, x, y (conditions of the module docstring assumed)."""
    xr_hi = x.real.upper(); yr_hi = y.real.upper()
    gb = g_upper_real(xr_hi, yr_hi)
    k = th / (1 - th)
    Y = k * y
    s = x + y
    ax = abs_lower(x); ay = abs_lower(y)
    if not (ax > 0 and ay > 0):
        return None
    t1 = phi_upper_real((-th * s).real.upper())
    t2 = phi_upper_real(x.real.upper()) * phi_upper_real(Y.real.upper())
    imx = abs(x.imag).upper(); imY = abs(Y.imag).upper()
    if not (imx < LIM and imY < LIM):
        return None
    mx = arb(1).min((x.real.lower()).exp() * imx.cos())
    mY = arb(1).min((Y.real.lower()).exp() * imY.cos())
    mx = mx.lower(); mY = mY.lower()
    if not (mx > 0 and mY > 0):
        return None
    thr_hi = th.real.upper(); thr_lo = th.real.lower(); thi = abs(th.imag).upper()
    # |1+up|^{-(1+theta_r)} <= max(1, m_x^{-(1+theta_r_hi)}) for |1+up| >= m_x (both cases m_x < 1, m_x >= 1)
    fx = arb(1).max(mx ** (-(1 + thr_hi)))
    fY = arb(1).max(mY ** (-(2 - thr_lo)))
    Jb = fx * fY * (thi * (imx + imY)).exp()
    tmb = abs(th).upper() * (t1 + t2 * Jb) / (ax * ay)
    return (gb + tmb).upper()


def M_bound(th0, x0, y0, rp, Np):
    M = arb(0)
    n = 0
    for j1 in range(Np[0]):
        b1 = arc_ball(th0, rp[0], 2 * math.pi * j1 / Np[0], 2 * math.pi * (j1 + 1) / Np[0])
        for j2 in range(Np[1]):
            b2 = arc_ball(x0, rp[1], 2 * math.pi * j2 / Np[1], 2 * math.pi * (j2 + 1) / Np[1])
            for j3 in range(Np[2]):
                b3 = arc_ball(y0, rp[2], 2 * math.pi * j3 / Np[2], 2 * math.pi * (j3 + 1) / Np[2])
                v = H_abs_bound(b1, b2, b3)
                n += 1
                if v is None or not v.is_finite():
                    return None
                M = M.max(v)          # ball containing max(M, v)
    return M.upper()


def samples_dft(th0, x0, y0, rho, N, n1, n):
    roots = [[(acb(0, 1) * arb.pi() * arb(2 * k) / N[i]).exp() for k in range(N[i])] for i in range(3)]
    cen = [th0, x0, y0]
    pts = [[acb(cen[i]) + arb(rho[i]) * roots[i][k] for k in range(N[i])] for i in range(3)]
    F = [[[C.H_point(pts[0][k1], pts[1][k2], pts[2][k3]) for k3 in range(N[2])] for k2 in range(N[1])] for k1 in range(N[0])]
    G1 = [[[None] * N[2] for _ in range(N[1])] for _ in range(n1 + 1)]
    for a in range(n1 + 1):
        w = [roots[0][(-a * k) % N[0]] for k in range(N[0])]
        for k2 in range(N[1]):
            for k3 in range(N[2]):
                acc = acb(0)
                for k1 in range(N[0]):
                    acc += F[k1][k2][k3] * w[k1]
                G1[a][k2][k3] = acc / N[0]
    G2 = [[[None] * N[2] for _ in range(n + 1)] for _ in range(n1 + 1)]
    for b in range(n + 1):
        w = [roots[1][(-b * k) % N[1]] for k in range(N[1])]
        for a in range(n1 + 1):
            for k3 in range(N[2]):
                acc = acb(0)
                for k2 in range(N[1]):
                    acc += G1[a][k2][k3] * w[k2]
                G2[a][b][k3] = acc / N[1]
    coeffs = {}
    for c in range(n + 1):
        w = [roots[2][(-c * k) % N[2]] for k in range(N[2])]
        for a in range(n1 + 1):
            for b in range(n + 1 - c):
                acc = acb(0)
                for k3 in range(N[2]):
                    acc += G2[a][b][k3] * w[k3]
                coeffs[(a, b, c)] = acc / N[2] / (arb(rho[0]) ** a * arb(rho[1]) ** b * arb(rho[2]) ** c)
    return coeffs


def analyse_box(th0, x0, y0, rt, r, rp, N, Np, n1, n, qfac=3.0, nsub=(2, 4, 4)):
    t0 = time.time()
    ok, info = analytic_check(th0, x0, y0, rp)
    if not ok:
        return {'ok': False, 'reason': 'analyticity', 'info': info}
    M = M_bound(th0, x0, y0, rp, Np)
    if M is None:
        return {'ok': False, 'reason': 'M bound failed'}
    rho = [rp[i] / qfac for i in range(3)]
    coeffs = samples_dft(th0, x0, y0, rho, N, n1, n)
    rr = [rt, r, r]
    q = [arb(rho[i]) / arb(rp[i]) for i in range(3)]       # exact ratio of the radii actually used
    t = [arb(rr[i]) / rp[i] for i in range(3)]
    alias = arb(1)
    for i in range(3):
        alias = alias / (1 - q[i] ** N[i])
    alias = alias - 1
    tot = 1 / ((1 - t[0]) * (1 - t[1]) * (1 - t[2]))
    totx = 1 / ((1 - t[0]) * (1 - t[1]) ** 2 * (1 - t[2]))
    toty = 1 / ((1 - t[0]) * (1 - t[1]) * (1 - t[2]) ** 2)
    part = partx = party = arb(0)
    eH = ex = ey = arb(0)
    rpa = [arb(v) for v in rp]
    ra = [arb(v) for v in rr]
    polyH, polyS = {}, {}
    for (a, b, c), v in coeffs.items():
        tp = t[0] ** a * t[1] ** b * t[2] ** c
        part += tp
        e = M * alias / (rpa[0] ** a * rpa[1] ** b * rpa[2] ** c)
        eH += e * ra[0] ** a * ra[1] ** b * ra[2] ** c
        if b >= 1:
            partx += b * t[0] ** a * t[1] ** (b - 1) * t[2] ** c
            ex += b * e * ra[0] ** a * ra[1] ** (b - 1) * ra[2] ** c
        if c >= 1:
            party += c * t[0] ** a * t[1] ** b * t[2] ** (c - 1)
            ey += c * e * ra[0] ** a * ra[1] ** b * ra[2] ** (c - 1)
        h = v.real
        polyH[(a, b, c)] = polyH.get((a, b, c), arb(0)) + h
        if b >= 1:
            polyS[(a, b - 1, c)] = polyS.get((a, b - 1, c), arb(0)) + b * h / 2
        if c >= 1:
            polyS[(a, b, c - 1)] = polyS.get((a, b, c - 1), arb(0)) + c * h / 2
    errH = (eH + M * (tot - part)).upper()
    errx = ex + M / rpa[1] * (totx - partx)
    erry = ey + M / rpa[2] * (toty - party)
    errS = ((errx + erry) / 2).upper()
    nacc = 0
    nP = nC = 0
    worst = None
    for i1 in range(nsub[0]):
        z1 = arb.union(arb(-rt + 2 * rt * i1 / nsub[0]), arb(-rt + 2 * rt * (i1 + 1) / nsub[0]))
        p1 = [arb(1)]
        for k in range(n1 + 1):
            p1.append(p1[-1] * z1)
        for i2 in range(nsub[1]):
            xa, xb = -r + 2 * r * i2 / nsub[1], -r + 2 * r * (i2 + 1) / nsub[1]
            z2 = arb.union(arb(xa), arb(xb))
            p2 = [arb(1)]
            for k in range(n + 1):
                p2.append(p2[-1] * z2)
            for i3 in range(nsub[2]):
                ya, yb = -r + 2 * r * i3 / nsub[2], -r + 2 * r * (i3 + 1) / nsub[2]
                if (x0 + xb) + (y0 + yb) < 0:
                    continue          # sub-box entirely in s < 0: not part of the domain
                z3 = arb.union(arb(ya), arb(yb))
                p3 = [arb(1)]
                for k in range(n + 1):
                    p3.append(p3[-1] * z3)
                vH = arb(0)
                for (a, b, c), h in polyH.items():
                    vH += h * p1[a] * p2[b] * p3[c]
                vS = arb(0)
                for (a, b, c), h in polyS.items():
                    vS += h * p1[a] * p2[b] * p3[c]
                lH = (vH - errH).lower()
                lS = (vS - errS).lower()
                okP = lH > 0
                okC = lS > 0
                if okP:
                    nP += 1
                elif okC:
                    nC += 1
                else:
                    if worst is None:
                        worst = (float(lH), float(lS), xa + x0, xb + x0, ya + y0, yb + y0, float(z1.lower()) + th0)
                nacc += 1
    allok = worst is None
    return {'ok': allok, 'M': float(M), 'errH': float(errH), 'errS': float(errS), 'nP': nP, 'nC': nC,
            'worst': worst, 'secs': round(time.time() - t0, 2), 'info': info}


if __name__ == '__main__':
    args = [json.loads(a) for a in sys.argv[1:]]
    print(analyse_box(*args), flush=True)
