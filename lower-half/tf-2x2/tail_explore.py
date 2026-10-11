"""NUMERICAL reconnaissance for the far-region tail lemma (max(a, c) >= 40).
Ansh Mishra, Aryan Senthilkumar.

Three explicit 3-parameter sufficient conditions (PROOF.md Section 6, Lemmas 6.1-6.3), each implying F >= 0 for all w:
  Lemma S:  F >= 0 if eps_P >= 1, or if Y_G <= (1/2) min(1, theta psi(R_E)) eps_P,  psi(R) = R/(1-e^{-R}).
  (T)  e^{-theta|a-c|} (theta/(1-theta))^2 M_G <= (1/2) min(1, theta psi(|a-c|)) M_P,
       M_P = 4 Ch''((a-c)^2) (<= E_P),  M_G = S_a S_b V''(C-) (>= E_G).
  (W)  E0 := eps_P(0) >= 1, faces w1 = 1 - 1/E0, w2 = -1 + 1/E0, R1 = RE(w1), R2 = RE(w2);
       (L+)  e^{-theta R1} K+ <= (1/2) min(1, theta psi(R1)) P+(w1),  K+ = 2|V'(C-)| sinh a sinh b,
             P+(v) = 2ac [shc(RE(v)) - shc(a) shc(c)];
       (L-)  shc(a) shc(c) - shc(R2) >= 2 theta.
Prints the worst ratios (<= 1 means the condition holds) on a grid with max(a, c) in [40, 2000].
"""
import sys
import mpmath as mp
mp.mp.dps = 60


def shc(x):
    x = mp.mpf(x)
    return mp.sinh(x) / x if x != 0 else mp.mpf(1)


def Chpp(z):            # Ch''(z), Ch(z) = cosh(sqrt z)
    t = mp.sqrt(z)
    if t < mp.mpf('1e-3'):
        return mp.mpf(1) / 12 + z / 180
    return (t * mp.cosh(t) - mp.sinh(t)) / (4 * t ** 3)


def U1(t, d):           # |U_t'(cosh d)|
    if d < mp.mpf('1e-6'):
        return t * (1 - t * t) / 3
    return ((1 - t) * mp.sinh((1 + t) * d) - (1 + t) * mp.sinh((1 - t) * d)) / (2 * mp.sinh(d) ** 3)


def U2(t, C):           # U_t''(C) > 0, closed form in d = acosh C (evaluated with 160 digits)
    if C - 1 < mp.mpf('1e-30'):
        return t * (1 - t * t) * (4 - t * t) / 15
    with mp.workdps(160):
        d = mp.acosh(C)
        sd, cd = mp.sinh(d), mp.cosh(d)
        N1 = t * mp.cosh(t * d) * sd - mp.sinh(t * d) * cd
        Ud = N1 / sd ** 2
        Udd = ((t * t - 1) * mp.sinh(t * d) * sd ** 2 - 2 * N1 * cd) / sd ** 3
        v = (Udd * sd - Ud * cd) / sd ** 3
    return +v


def psi(R):
    R = mp.mpf(R)
    return R / (1 - mp.exp(-R)) if R > 0 else mp.mpf(1)


def conds(th, a, c):
    th, a, c = mp.mpf(th), mp.mpf(a), mp.mpf(c)
    b = th * c / (1 - th)
    out = {}
    # (T)
    d = abs(a - c)
    Cm = mp.cosh(a - b)
    MP = 4 * Chpp(d * d)
    Vpp = U2(th, Cm) * mp.cosh(a) + U2(1 - th, Cm) * mp.cosh(b)
    MG = shc(a) ** 2 * shc(b) ** 2 * Vpp
    lhs = mp.exp(-th * d) * (th / (1 - th)) ** 2 * MG
    rhs = mp.mpf(1) / 2 * min(1, th * psi(d)) * MP
    out['T'] = lhs / rhs
    # (W)
    E0 = 2 * (mp.cosh(a) * mp.cosh(c) - mp.cosh(mp.sqrt(a * a + c * c)))
    out['E0'] = E0
    if E0 >= 1:
        R1 = mp.sqrt((a + c) ** 2 - 2 * a * c / E0)
        R2 = mp.sqrt((a - c) ** 2 + 2 * a * c / E0)
        Pp = 2 * a * c * (shc(R1) - shc(a) * shc(c))
        Kp = 2 * (U1(th, abs(a - b)) * mp.cosh(a) + U1(1 - th, abs(a - b)) * mp.cosh(b)) * mp.sinh(a) * mp.sinh(b)
        out['L+'] = (mp.exp(-th * R1) * Kp) / (mp.mpf(1) / 2 * min(1, th * psi(R1)) * Pp) if Pp > 0 else mp.inf
        den = shc(a) * shc(c) - shc(R2)
        out['L-'] = 2 * th / den if den > 0 else mp.inf
    else:
        out['L+'] = mp.inf; out['L-'] = mp.inf
    return out


if __name__ == '__main__':
    ths = [mp.mpf(x) for x in ('0.5', '0.45', '0.4', '0.3', '0.2', '0.1', '0.05', '0.01', '0.001')]
    bigs = [40, 60, 100, 200, 500, 1000, 2000]
    fracs = [0, 1e-4, 1e-3, 0.01, 0.05, 0.1, 0.15, 0.2, 0.25, 0.3, 0.4, 0.5, 0.7, 0.8, 0.9, 1.0]
    worst_cover = (mp.inf, None)
    rows = []
    for th in ths:
        for B in bigs:
            for side in ('a', 'c'):
                for f in fracs:
                    small = B * f
                    a, c = (B, small) if side == 'a' else (small, B)
                    if a == 0 or c == 0:
                        continue
                    o = conds(th, a, c)
                    W = max(o['L+'], o['L-']) if o['E0'] >= 1 else mp.inf
                    best = min(o['T'], W)
                    rows.append((float(th), a, c, float(o['T']), float(W)))
                    if best > worst_cover[0] or worst_cover[1] is None:
                        pass
                    if worst_cover[1] is None or best > worst_cover[0]:
                        worst_cover = (best, (float(th), a, c, float(o['T']), float(W)))
    print('worst over grid of min(ratio_T, ratio_W) (must be <= 1):', mp.nstr(worst_cover[0], 6), worst_cover[1])
    wF2 = max((r for r in rows if min(r[1], r[2]) >= 1), key=lambda r: r[4])
    tF1 = max((r for r in rows if min(r[1], r[2]) < 1), key=lambda r: r[3])
    print('largest (W) ratio max(L+, L-) over grid points with min(a, c) >= 1 (F2):', wF2)
    print('largest (T) ratio over grid points with min(a, c) < 1 (F1):', tF1)
    # report where T fails and W fails
    for r in rows:
        if min(r[3], r[4]) > 0.5:
            print('tight:', r)
