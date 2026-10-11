"""Randomised soundness test of the region-A' Taylor models (independent mpmath evaluation of H for complex args):
 (1) |H| <= M' at random points of the torus T' (maximum-principle bound);
 (2) |H - P| <= errH and |dH/ds - dP/ds| <= errS at random real points of the box (P from the DFT coefficients)."""
import sys, random
sys.path.insert(0, '..')
import mpmath as mp
from flint import arb
import regionA2 as A
import regionA_run as RR
mp.mp.dps = 40

def H_c(th, x, y):
    """H = E/(theta x^2 y^2) from the closed form, complex arguments allowed."""
    r = (1 - th) / th; X, Y = x, y / r; s = x + y
    p, q = mp.expm1(X), mp.expm1(Y)
    EGT = th * (x * y * mp.expm1(s) / s - mp.expm1(x) * mp.expm1(y))
    Em1 = th * x * y * (-mp.expm1(-th * s)) / s + p * q / (p - q) ** 2 * ((1 - th) * p * mp.expm1(th * (Y - X)) + th * q * mp.expm1((1 - th) * (X - Y)))
    return (EGT + Em1) / (th * x * x * y * y)

def pick_rho(th0, x0, y0, rt, r):
    for rpx in RR.choose_rho(x0, r):
        for rpy in RR.choose_rho(y0, r):
            for fac in (3.0, 2.5, 2.0):
                rp = [fac * rt, rpx, rpy]
                ok, info = A.analytic_check(th0, x0, y0, rp)
                if ok:
                    return rp
    return None

def ball_mid(b):
    return mp.mpf(b.mid().str(40, radius=False))

rng = random.Random(3)
for (th0, x0, y0, rt) in [(0.495, 0.0, 0.0, 0.005), (0.4, 1.0, -0.5, 0.0125), (0.15, 0.0, 0.0, 0.025), (0.475, -1.5, 2.0, 0.005)]:
    r = 0.25
    rp = pick_rho(th0, x0, y0, rt, r)
    M = A.M_bound(th0, x0, y0, rp, [8, 24, 24])
    Mf = float(M)
    # (1) torus samples
    worstT = 0
    for _ in range(300):
        z = [rp[i] * mp.expjpi(2 * mp.mpf(rng.random())) for i in range(3)]
        v = abs(H_c(th0 + z[0], x0 + z[1], y0 + z[2]))
        worstT = max(worstT, v / Mf)
    # (2) polynomial vs H on the real box
    rho = [rp[i] / 3.0 for i in range(3)]
    coeffs = A.samples_dft(th0, x0, y0, rho, [12, 16, 16], 11, 15)
    rt_eff = rt * (1 + 2.0 ** -20)
    q = [arb(rho[i]) / arb(rp[i]) for i in range(3)]
    t = [arb([rt_eff, r, r][i]) / rp[i] for i in range(3)]
    alias = arb(1)
    for i in range(3): alias = alias / (1 - q[i] ** [12, 16, 16][i])
    alias -= 1
    tot = 1 / ((1 - t[0]) * (1 - t[1]) * (1 - t[2])); totx = tot / (1 - t[1]); toty = tot / (1 - t[2])
    part = partx = party = arb(0); eH = ex = ey = arb(0)
    P = {}
    ra = [arb(rt_eff), arb(r), arb(r)]
    for (a, b, c), v in coeffs.items():
        e = M * alias / (arb(rp[0]) ** a * arb(rp[1]) ** b * arb(rp[2]) ** c)
        part += t[0] ** a * t[1] ** b * t[2] ** c
        eH += e * ra[0] ** a * ra[1] ** b * ra[2] ** c
        if b: partx += b * t[0] ** a * t[1] ** (b - 1) * t[2] ** c; ex += b * e * ra[0] ** a * ra[1] ** (b - 1) * ra[2] ** c
        if c: party += c * t[0] ** a * t[1] ** b * t[2] ** (c - 1); ey += c * e * ra[0] ** a * ra[1] ** b * ra[2] ** (c - 1)
        P[(a, b, c)] = ball_mid(v.real)
    errH = float((eH + M * (tot - part)).upper())
    errS = float(((ex + M / arb(rp[1]) * (totx - partx) + ey + M / arb(rp[2]) * (toty - party)) / 2).upper())
    worstH = worstS = 0
    for _ in range(200):
        z = [mp.mpf(rng.uniform(-rt_eff, rt_eff)), mp.mpf(rng.uniform(-r, r)), mp.mpf(rng.uniform(-r, r))]
        th, x, y = th0 + z[0], x0 + z[1], y0 + z[2]
        if x + y < 0 or abs(x) < 1e-6 or abs(y) < 1e-6: continue
        Pv = sum(cf * z[0] ** a * z[1] ** b * z[2] ** c for (a, b, c), cf in P.items())
        dPs = sum(cf * (b * z[0] ** a * z[1] ** (b - 1) * z[2] ** c if b else 0) + cf * (c * z[0] ** a * z[1] ** b * z[2] ** (c - 1) if c else 0) for (a, b, c), cf in P.items()) / 2
        Hv = H_c(th, x, y)
        h = mp.mpf('1e-12')
        dHs = (H_c(th, x + h, y + h) - H_c(th, x - h, y - h)) / (4 * h)
        worstH = max(worstH, abs(Hv - Pv) / errH); worstS = max(worstS, abs(dHs - dPs) / errS)
    print(f"box th0={th0} x0={x0} y0={y0} rt={rt}: rho'={[round(v,4) for v in rp]} M'={Mf:.4g}; "
          f"max|H|/M' on torus = {mp.nstr(worstT,4)} (must be <= 1); max|H-P|/errH = {mp.nstr(worstH,4)}; "
          f"max|dH/ds - dP/ds|/errS = {mp.nstr(worstS,4)} (both must be <= 1)", flush=True)
