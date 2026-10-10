"""Tests of the a-tail chart with the eps jet variable (iv_tail3_run / iv_far.logF_atail2 with eps a jet):
(1) consistency: the jet's d/deps and d/dd of L1, L2, L3 at thin (m, d, eps) agree with central finite differences of
    thin evaluations (every eps-dependence of the formula must be carried by the eps jet);
(2) soundness: on random boxes of the eps cells k = 0, 1 (eps in [0, 2/296]) the certified lower bounds do not exceed
    the true values from the definitions (ref_defs.margins) at points a = a(m, 1/n) of the box, and at eps = 0."""
import random
from fractions import Fraction as Fr
import mpmath as mp
from flint import arb
import iv_far as T
import iv_forms as FF
import iv_atoms as AT
import iv_tail_run as R
import iv_tail3_run as R3
from iv_jet import Jet, SP3
from ref_defs import margins

q = T.q
rnd = random.Random(2027)
E = Fr(1, 37)


def thinL(m, d, e, form, X, Xe):
    G = T.logF_atail2(Jet.const(q(m), SP3), Jet.var(q(e), 2, SP3), Jet.var(q(d), 1, SP3), X, Xe, form)
    return FF.conditions(G), FF.gradients(G)


worst = 0.0
for it in range(12):
    k = rnd.randrange(2)
    e = E * k / 8 + E / 8 * Fr(rnd.randrange(1, 100), 100)
    mt = R.m250(e)
    m = mt * Fr(rnd.randrange(1, 100), 100)
    d = Fr(rnd.choice([rnd.randrange(1, 60), rnd.randrange(60, 512)]), 1) + Fr(rnd.randrange(0, 100), 100)
    if rnd.random() < 0.3:
        d = Fr(rnd.randrange(5, 370), 100)
    form = 'mix' if d <= Fr(15, 4) else 'nu'
    (L, gr) = thinL(m, d, e, form, 0, 0)
    h = Fr(1, 10 ** 18)
    Lp, _ = thinL(m, d, e + h, form, 0, 0)
    Lm, _ = thinL(m, d, e - h, form, 0, 0)
    Ldp, _ = thinL(m, d + h, e, form, 0, 0)
    Ldm, _ = thinL(m, d - h, e, form, 0, 0)
    for kk in range(3):
        fde = (Lp[kk] - Lm[kk]) / (2 * q(h))
        fdd = (Ldp[kk] - Ldm[kk]) / (2 * q(h))
        re = float(abs(fde - gr[kk][2]).upper()) / max(1e-30, float(abs(gr[kk][2]).upper()))
        rd = float(abs(fdd - gr[kk][1]).upper()) / max(1e-30, float(abs(gr[kk][1]).upper()))
        worst = max(worst, re, rd)
        if re > 1e-6 or rd > 1e-6:
            print('DERIVATIVE MISMATCH', float(m), float(d), float(e), kk, fde, gr[kk][2], fdd, gr[kk][1])
    print(f'derivative check m={float(m):.3e} d={float(d):.4g} eps={float(e):.5f} {form}: L={[float(x.mid()) for x in L]}, '
          f'dL/deps={[float(gr[kk][2].mid()) for kk in range(3)]}', flush=True)
print('worst relative derivative mismatch', worst)

viol = chk = 0
for it in range(10):
    k = rnd.randrange(2)
    e0, e1 = E * k / 8, E * (k + 1) / 8
    sub = rnd.randrange(8)
    e0, e1 = e0 + (e1 - e0) * sub / 8, e0 + (e1 - e0) * (sub + 1) / 8
    mtop = R.m250(e0)
    i = rnd.randrange(8)
    m0, m1 = mtop * i / 8, mtop * (i + 1) / 8
    d0 = Fr(rnd.choice([rnd.randrange(4, 40), rnd.randrange(40, 500)]))
    d1 = d0 + Fr(1, 32)
    lows, _ = R3.check(m0, m1, d0, d1, e0, e1, 'nu')
    ns = [n for n in range(148, 200000) if e0 <= Fr(1, n) <= e1][:2] + ([None] if e0 == 0 else [])
    for n in ns:
        mt = float(m0 + (m1 - m0) * Fr(rnd.randrange(1, 100), 100))
        if n is None:
            a = Fr(1 / mt).limit_denominator(10 ** 6)
            nn = None
        else:
            lo_a, hi_a = 50.0, 1e7
            f = lambda aa: 1 / (aa * mp.expm1(aa / n) / (aa / n)) - mt
            for _ in range(200):
                mid = (lo_a + hi_a) / 2
                if f(mid) > 0:
                    lo_a = mid
                else:
                    hi_a = mid
            a = Fr(lo_a).limit_denominator(10 ** 6)
            nn = n
            if Fr(1, n) < e0 or Fr(1, n) > e1:
                continue
        if a > 5000:
            continue
        d = d0 + Fr(1, 64)
        F0, L1, L2, L3 = margins(nn, float(a), float(d), dps=int(200 + 0.3 * float(a + d)),
                                 h=mp.mpf(10) ** -35 * min(1, float(a), float(d)))
        for kk, Lt in enumerate((L1, L2, L3)):
            chk += 1
            if Lt < mp.mpf(lows[kk].lower().str(40, radius=False)):
                viol += 1
                print('A-TAIL (eps jet) VIOLATION', float(a), float(d), n, kk, Lt, lows[kk])
        print(f'  box m=[{float(m0):.3e},{float(m1):.3e}] d=[{float(d0)},{float(d1)}] eps=[{float(e0):.5f},{float(e1):.5f}] '
              f'n={n} a={float(a):.1f}: true {[mp.nstr(x, 6) for x in (L1, L2, L3)]} >= certified '
              f'{[float(l.lower()) for l in lows]}', flush=True)
print(f'tail3 soundness test: {chk} comparisons, {viol} violations')
