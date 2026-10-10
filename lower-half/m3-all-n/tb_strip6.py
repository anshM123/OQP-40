"""Theorem B, the strip a -> 0 (s -> 1): verification with the exact factorisation of (s-1)^2 (RESULTS.md 8.4).

With phi = K_n(1,s,t), k = K_n(t,1,1) = kappa(b), psi = K_n(t,s,s) = e^a kappa(d):
  phi - k = a [phi1(a eps) H1 - e^{b/3} phi1(a/3)/3],   2 phi - psi - k = a^2 [e^{b/3} phi1(a/3)^2/9 - phi1(a eps)^2 H2],
  H1 = eps h_{n-1}(1,1,s,t)/C = [M(a,b) - M(0,a)]/(b phi1(b eps)),  M(al, be) = h_n(1, e^{al eps}, e^{be eps})/C,
  H2 = eps^2 h_{n-2}(1,1,s,s,t)/C = (Y1 - Y2)/(b phi1(b eps)),
  Y1 = eps h_{n-1}(1,s,s,t)/C = [e^a (kappa(d) + e^{d/3}) - W(a) - e^{2a/3}]/(b phi1(b eps)),
  Y2 = eps h_{n-1}(1,1,s,s)/C = [a (e^a S(-a) - S(a)) + e^{a/3} phi1(a/3)/3]/phi1(a eps),
  phi^2 - k psi = a^2 Bq,  Bq = (phi1(a eps) H1 - e^{b/3} phi1(a/3)/3)^2 + kappa(b) (e^{b/3} phi1(a/3)^2/9 - phi1(a eps)^2 H2),
  E^R = a^2 Xh,  Xh = Bq/(phi + sqrt(k psi)) + sqrt(k psi) dPhi^2 phi1(-a^2 dPhi^2),  dPhi = (Phi(b) - Phi(d))/a,
  F = E^R/sqrt(W(a) W(b)) = a H,  H = Xh e^{-a/2}/sqrt(S(-a) W(b))   (W(a) = a^2 e^a S(-a)).
The conditions are N1 = 1 + a G_a, N2 = -G_b, N3 = -G_b - a (G_ab + G_a G_b) (G = log H), all > 0.
Everything is smooth at a = 0 without cancellation except dPhi (a difference quotient): at the thin centre (a_c > 0)
dPhi is computed directly, on a box with a in [0, a1] its Taylor coefficients are enclosed through
d_a^i d_b^j dPhi = int_0^1 (-(1-u))^i Phi^{(1+i+j)}(b - (1-u) a) du, i.e. by Phi^{(1+i+j)} on [b0 - a1, b1] / (i+1).
Usage: python tb_strip6.py a_max d_min d_max na nd > log
"""
import sys
import time
from fractions import Fraction as Fr
from math import factorial
from flint import arb, fmpq, arb_series
import flint
import tb_arb as T
from tb_arb import J, DJ, MT, ZERO, ONE, MU, LAM

SMALLZ = 2.5
# jets with second-order eps terms so that the eps-coefficients are tightened too
MT2 = T.Mode(list(MT.monos) + [(i, j, 2) for i in range(3) for j in range(3) if i + j <= 2])
MODE = MT2
USE_NORMALISED = True


def q_(x):
    return arb(fmpq(x.numerator, x.denominator))


def P_(Z, cx):
    return (Z * cx.e2).phi1() / (Z * cx.eps).phi1()


def Q_(Z, cx):
    return Z * (Z * cx.eps).phi1()


def small(Z):
    z0 = Z.bj.c[0] if hasattr(Z, 'bj') else Z.c[0]
    return z0.upper() <= SMALLZ


def kappa_of(Z, cx):
    if small(Z):
        return Z * Z * T.S_of(Z, cx)
    return cx.c * (P_(Z, cx) - 1) / Q_(Z, cx) - (Z / 3).exp()


def logW_of(Z, cx):
    """log W(z), W(z) = K_n(1, e^{z eps}, e^{z eps})."""
    if small(Z):
        return 2 * Z.log() + Z + T.S_of(-Z, cx).log()
    nz = T.nu_of(Z, cx)
    om = 1 - nz * (1 - (-(Z * cx.e2)).exp()) / cx.e2 - (-(Z / 3)).exp() / (cx.c * nz)
    return cx.c.log() + Z + nz.log() + om.log()


def Phi_coeffs(z0, K):
    """Taylor coefficients (orders 0..K) of Phi = Phihat e^{-mu z} enclosing all points of the ball z0."""
    ph = T.g_Phihat(z0, K)
    flint.ctx.cap = K + 1
    x = arb_series([z0, 1], prec=K + 1)
    s = arb_series(ph, prec=K + 1) * (-(MU * x)).exp()
    c = s.coeffs()
    return [c[k] if k < len(c) else ZERO for k in range(K + 1)]


def dPhi_box(z_lo, z_hi, mode):
    """jet (mode) of dPhi(a, b) = (Phi(b) - Phi(b - a))/a valid at every point of a box on which the points
    b - (1-u) a (0 <= u <= 1), i.e. [d, b], stay in [z_lo, z_hi] (z_lo = d0 >= 0, z_hi = a1 + d1)."""
    Kmax = max(i + j for (i, j, k) in mode.monos) + 1
    hull = arb.union(z_lo, z_hi)
    ph = Phi_coeffs(hull, Kmax)          # ph[m] = Phi^{(m)}/m! on the hull
    c = []
    for (i, j, k) in mode.monos:
        if k > 0:
            c.append(ZERO)
            continue
        m = 1 + i + j
        # coefficient = (1/(i! j!)) (-1)^i Phi^{(m)} / (i+1) = (-1)^i m! ph[m] / ((i+1) i! j!)
        c.append(ph[m] * ((-1) ** i * factorial(m)) / ((i + 1) * factorial(i) * factorial(j)))
    return J(c, mode)


def logH(A, B, cx, Dd, dPhi):
    eps, e1, e2, c = cx.eps, cx.e1, cx.e2, cx.c
    Mab = c * ((A * e1).exp() * P_(Dd, cx) - P_(A, cx)) / Q_(B, cx)
    Sa, Sma = T.S_of(A, cx), T.S_of(-A, cx)
    M0a = A * A * Sa + (A / 3).exp()
    bq = B * (B * eps).phi1()
    H1 = (Mab - M0a) / bq
    kapb = kappa_of(B, cx)
    kapd = kappa_of(Dd, cx)
    ea = A.exp()
    Wa = A * A * ea * Sma
    Y1 = (ea * (kapd + (Dd / 3).exp()) - Wa - (2 * A / 3).exp()) / bq
    p1 = (A * eps).phi1()
    p3 = (A / 3).phi1()
    Y2 = (A * (ea * Sma - Sa) + (A / 3).exp() * p3 / 3) / p1
    H2 = (Y1 - Y2) / bq
    eb3 = (B / 3).exp()
    t1 = p1 * H1 - eb3 * p3 / 3
    Bq = t1 * t1 + kapb * (eb3 * p3 * p3 / 9 - p1 * p1 * H2)
    phi = Mab - ((A + B) / 3).exp()
    sq = (kapb * ea * kapd).sqrt()
    x = A * A * dPhi * dPhi
    Xh = Bq / (phi + sq) + sq * dPhi * dPhi * (-x).phi1()
    return Xh.log() - A / 2 - Sma.log() / 2 - logW_of(B, cx) / 2


def logH_normalised(A, B, cx, Dd, dPhi):
    """the same log H with every e^b-scale removed symbolically (for d >= 5/2 and b >= 5/2, nu-forms):
    Mt = M e^{-b} = c2 nu_b nu_d (1 - e^{-d(1+2eps)}) - c nu_b e^{-b(1+eps)} P(a),
    H1t = H1 e^{-b(1-eps)} = nu_b (Mt - M0a e^{-b}),  kb = kappa(b) e^{-b} = c2 nu_b^2 gam_b,  kd = kappa(d) e^{-d},
    Y1t = Y1 e^{-b(1-eps)} = nu_b [kd + e^{-2d/3} - (W(a) + e^{2a/3}) e^{-b}],  H2t = H2 e^{-b(1-2eps)} = nu_b (Y1t - Y2 e^{-b(1-eps)}),
    t1t = p1 H1t - e^{-b(2/3 - eps)} p3/3,  Bqt = t1t^2 + kb (e^{-b(2/3 - 2eps)} p3^2/9 - p1^2 H2t),
    phit = Mt - e^{(a - 2b)/3},  sqt = sqrt(kb kd),  Xht = e^{-2b eps} Bqt/(phit + sqt) + sqt dPhi^2 phi1(-a^2 dPhi^2),
    log H = b/2 + log Xht - a/2 - log S(-a)/2 - log(c nu_b om_b)/2."""
    eps, e1, e2, c, cp = cx.eps, cx.e1, cx.e2, cx.c, cx.cp
    nb, nd = T.nu_of(B, cx), T.nu_of(Dd, cx)
    emb = (-B).exp()
    Pa = P_(A, cx)
    Mt = cp * nb * nd * (1 - (-(Dd * e2)).exp()) - c * nb * (-(B * e1)).exp() * Pa
    Sa, Sma = T.S_of(A, cx), T.S_of(-A, cx)
    M0a = A * A * Sa + (A / 3).exp()
    H1t = nb * (Mt - M0a * emb)
    kb = T.cpgam(B, cx) * nb * nb
    kd = T.cpgam(Dd, cx) * nd * nd
    ea = A.exp()
    Wa = A * A * ea * Sma
    Y1t = nb * (kd + (-(2 * Dd / 3)).exp() - (Wa + (2 * A / 3).exp()) * emb)
    p1 = (A * eps).phi1()
    p3 = (A / 3).phi1()
    Y2 = (A * (ea * Sma - Sa) + (A / 3).exp() * p3 / 3) / p1
    H2t = nb * (Y1t - Y2 * (-(B * (1 - eps))).exp())
    t1t = p1 * H1t - (-(B * (arb(2) / 3 - eps))).exp() * p3 / 3
    Bqt = t1t * t1t + kb * ((-(B * (arb(2) / 3 - 2 * eps))).exp() * p3 * p3 / 9 - p1 * p1 * H2t)
    phit = Mt - ((A - 2 * B) / 3).exp()
    sqt = (kb * kd).sqrt()
    x = A * A * dPhi * dPhi
    Xht = (-(2 * eps) * B).exp() * Bqt / (phit + sqt) + sqt * dPhi * dPhi * (-x).phi1()
    omb = 1 - nb * (1 - (-(B * e2)).exp()) / e2 - (-(B / 3)).exp() / (c * nb)
    return B / 2 + Xht.log() - A / 2 - Sma.log() / 2 - (c * nb * omb).log() / 2


def norm_conditions(G, a):
    Ga, Gb, Gab = G.coef(1, 0), G.coef(0, 1), G.coef(1, 1)
    return [1 + a * Ga, -Gb, -Gb - a * (Gab + Ga * Gb)]


def norm_gradients(G, a):
    c100, c010, c110 = G.coef(1, 0), G.coef(0, 1), G.coef(1, 1)
    c200, c020, c210, c120 = G.coef(2, 0), G.coef(0, 2), G.coef(2, 1), G.coef(1, 2)
    c101, c011, c111 = G.coef(1, 0, 1), G.coef(0, 1, 1), G.coef(1, 1, 1)
    g1 = (c100 + 2 * a * c200, a * c110, a * c101)
    g2 = (-c110, -2 * c020, -c011)
    g3 = (-2 * c110 - 2 * a * c210 - c100 * c010 - 2 * a * c200 * c010 - a * c100 * c110,
          -2 * c020 - 2 * a * c120 - a * c110 * c010 - 2 * a * c100 * c020,
          -c011 - a * c111 - a * c101 * c010 - a * c100 * c011)
    return g1, g2, g3


def check_box(a0, a1, d0, d1, e0, e1):
    ac, dc, ec = (a0 + a1) / 2, (d0 + d1) / 2, (e0 + e1) / 2
    ra, rd, re = (a1 - a0) / 2, (d1 - d0) / 2, (e1 - e0) / 2
    T.TIGHT['r'] = (arb(0, q_(ra)), arb(0, q_(rd)), arb(0, q_(re)))
    Ac = J.var(q_(ac), 0, MODE)
    Dc = T.dvar(q_(dc), MODE)
    Ec = J.var(q_(ec), 2, MODE)
    Bc = Ac + Dc
    Ab = J.var(arb.union(q_(a0), q_(a1)), 0, MODE)
    Db = T.dvar(arb.union(q_(d0), q_(d1)), MODE)
    Eb = J.var(arb.union(q_(e0), q_(e1)), 2, MODE)
    Bb = Ab + Db
    # dPhi: centre directly, box by the hull of Phi's derivatives
    dPc = (T._Phihat_of_J(Bc) * (-MU * Bc).exp() - T._Phihat_of_J(Dc) * (-MU * Dc).exp()) / Ac
    dPb = dPhi_box(q_(d0), q_(a1) + q_(d1), MODE)
    A = DJ(Ac, Ab)
    D = DJ(Dc, Db)
    B = DJ(Bc, Bb)
    cx = T.DCtx(Ec, Eb)
    G = (logH_normalised if USE_NORMALISED else logH)(A, B, cx, D, DJ(dPc, dPb))
    Nc = norm_conditions(G.cj, q_(ac))
    grads = norm_gradients(T.tighten(G.bj, G.cj), Ab.c[0])
    lows, contrib = [], []
    for k in range(3):
        ga, gb, ge = grads[k]
        ca, cd, ce = (ga + gb) * arb(0, q_(ra)), gb * arb(0, q_(rd)), ge * arb(0, q_(re))
        lows.append(Nc[k] + ca + cd + ce)
        contrib.append((float(ca.rad()), float(cd.rad()), float(ce.rad())))
    return lows, contrib, Nc


def run(a_max, d_min, d_max, na, nd, log=print):
    t0 = time.time()
    stack = []
    for i in range(na):
        for j in range(nd):
            stack.append((a_max * i / na, a_max * (i + 1) / na, d_min + (d_max - d_min) * j / nd,
                          d_min + (d_max - d_min) * (j + 1) / nd, Fr(0), Fr(1, 37)))
    nbox, nfail = 0, 0
    worst = [None] * 3
    while stack:
        box = stack.pop()
        a0, a1, d0, d1, e0, e1 = box
        try:
            lows, contrib, Nc = check_box(*box)
            ok = all(l > 0 for l in lows)
        except (T.NotPositive, ValueError, ZeroDivisionError):
            ok, lows, contrib = False, None, None
        if ok:
            nbox += 1
            if nbox % 1000 == 0:
                log(f"  progress: {nbox} boxes, stack {len(stack)}, {time.time() - t0:.0f} s, last a=[{float(a0):.4g},{float(a1):.4g}] d=[{float(d0):.4g},{float(d1):.4g}]")
            for k in range(3):
                v = float(lows[k].lower())
                if worst[k] is None or v < worst[k][0]:
                    worst[k] = (v, tuple(float(x) for x in box))
            continue
        wa, wd, we = a1 - a0, d1 - d0, e1 - e0
        if contrib is None:
            dim = 0 if float(wa) >= float(wd) / max(1.0, float(d0)) else 1
        else:
            k = min(range(3), key=lambda i: float(lows[i].lower()))
            dim = max(range(3), key=lambda i: contrib[k][i])
        if (dim == 0 and wa < Fr(1, 2 ** 14)) or (dim == 1 and wd < Fr(1, 2 ** 14)) or (dim == 2 and we < Fr(1, 2 ** 22)):
            nfail += 1
            log(f"FAIL box {tuple(float(x) for x in box)} lows={lows}")
            if nfail > 10:
                break
            continue
        if dim == 0:
            m = (a0 + a1) / 2
            stack += [(a0, m, d0, d1, e0, e1), (m, a1, d0, d1, e0, e1)]
        elif dim == 1:
            m = (d0 + d1) / 2
            stack += [(a0, a1, d0, m, e0, e1), (a0, a1, m, d1, e0, e1)]
        else:
            m = (e0 + e1) / 2
            stack += [(a0, a1, d0, d1, e0, m), (a0, a1, d0, d1, m, e1)]
    return nbox, nfail, worst, time.time() - t0


if __name__ == '__main__':
    a_max, d_min, d_max = Fr(sys.argv[1]), Fr(sys.argv[2]), Fr(sys.argv[3])
    na, nd = int(sys.argv[4]), int(sys.argv[5])
    print(f"strip (factorised form): 0 <= a <= {a_max}, d in [{d_min}, {d_max}], eps in [0, 1/37]", flush=True)
    nbox, nfail, worst, dt = run(a_max, d_min, d_max, na, nd, log=lambda s: print(s, flush=True))
    print(f"boxes accepted: {nbox}, failures: {nfail}, time {dt:.1f} s")
    for k in range(3):
        if worst[k]:
            print(f"  certified min lower bound of N{k + 1}: {worst[k][0]:.6g} on box {worst[k][1]}")
    print("RESULT: REGION VERIFIED" if nfail == 0 else "RESULT: FAILED")
