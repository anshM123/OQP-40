"""Closed-form quantities for the 2x2 TF problem (mpmath, NUMERICAL reference).
Ansh Mishra, Aryan Senthilkumar.

Normal form: A = I + alpha sigma_z, B = I + beta (cos gam sigma_z + sin gam sigma_x),
0 <= alpha, beta < 1, gam in [0, pi], theta in (0, 1/2], N0 = 1/theta, r = (1-theta)/theta.
Quantities:
  zeta_{1,2}  eigenvalues of Z = theta log A + (1-theta) log B,  lam_i = e^{zeta_i}
  P  = Tr(A B^r)
  G  = Tr(A^{-1} #_{1-theta} B^{-1})      (Kubo-Ando weighted geometric mean)
  GT = P - Tr e^{N0 Z},  AH = Tr e^{-Z} - G
  c  = G - e^{-zeta_2},  u_c = -log c
  C(u) = P - e^{N0 zeta_2} - (N0+1) e^{N0 u} + N0 e^{(N0+1) u} c   (= N0(N0+1) T(u) on [zeta_1, v_min])
  v_min, v_max = min / max of the level l = theta log a + (1-theta) log b on the joint numerical range W.
"""
import mpmath as mp


def quantities(th, al, be, ga, dps=40):
    with mp.workdps(dps):
        th, al, be, ga = mp.mpf(th), mp.mpf(al), mp.mpf(be), mp.mpf(ga)
        N0 = 1 / th
        r = (1 - th) / th
        ea, eb = mp.atanh(al), mp.atanh(be)
        cg, sg = mp.cos(ga), mp.sin(ga)
        z0 = th / 2 * mp.log(1 - al ** 2) + (1 - th) / 2 * mp.log(1 - be ** 2)
        zz = th * ea + (1 - th) * eb * cg
        zx = (1 - th) * eb * sg
        zn = mp.sqrt(zz ** 2 + zx ** 2)
        z1, z2 = z0 - zn, z0 + zn
        P = 2 * (1 - be ** 2) ** (r / 2) * (mp.cosh(r * eb) + al * cg * mp.sinh(r * eb))
        # G = Tr(A^{-1} M^t), M = A^{1/2} B^{-1} A^{1/2}, t = 1 - theta
        t = 1 - th
        m0 = (1 - al * be * cg) / (1 - be ** 2)
        mz = (al - be * cg) / (1 - be ** 2)
        mx = -be * sg * mp.sqrt(1 - al ** 2) / (1 - be ** 2)
        mn = mp.sqrt(mz ** 2 + mx ** 2)
        mup, mum = m0 + mn, m0 - mn
        cM = (mup ** t + mum ** t) / 2
        sM = (mup ** t - mum ** t) / 2
        if mn == 0:
            G = 2 / (1 - al ** 2) * cM
        else:
            G = 2 / (1 - al ** 2) * (cM - al * sM * mz / mn)
        GT = P - (mp.exp(N0 * z1) + mp.exp(N0 * z2))
        AH = mp.exp(-z1) + mp.exp(-z2) - G
        c = G - mp.exp(-z2)
        uc = -mp.log(c) if c > 0 else mp.inf
        return dict(th=th, al=al, be=be, ga=ga, N0=N0, r=r, z1=z1, z2=z2, P=P, G=G, GT=GT, AH=AH, c=c, uc=uc)


def C_of_u(q, u):
    N0 = q['N0']
    return q['P'] - mp.exp(N0 * q['z2']) - (N0 + 1) * mp.exp(N0 * u) + N0 * mp.exp((N0 + 1) * u) * q['c']


def Dc(q):
    """C(u_c) = P - e^{N0 zeta_2} - c^{-N0}  (inequality (C) says this is >= 0)."""
    return q['P'] - mp.exp(q['N0'] * q['z2']) - q['c'] ** (-q['N0'])


def level_on_circle(q, phi):
    th, al, be, ga = q['th'], q['al'], q['be'], q['ga']
    return th * mp.log(1 + al * mp.cos(phi)) + (1 - th) * mp.log(1 + be * mp.cos(phi - ga))


def vmin_vmax(q, n=720):
    vals = [(level_on_circle(q, 2 * mp.pi * k / n), 2 * mp.pi * k / n) for k in range(n)]
    lo = min(vals)
    hi = max(vals)
    f = lambda p: level_on_circle(q, p)
    out = []
    for (v, p0), sgn in ((lo, 1), (hi, -1)):
        try:
            p = mp.findroot(lambda p: mp.diff(f, p), p0)
            out.append(f(p))
        except Exception:
            out.append(v)
    vmin = min(out[0], lo[0])
    vmax = max(out[1], hi[0])
    return vmin, vmax
