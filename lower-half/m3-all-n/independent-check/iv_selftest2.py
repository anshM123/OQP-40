"""Self-test of the strip code (iv_as) and the tail charts (iv_far): on random boxes the certified enclosures must
contain / lie below the true values (definitions, ref_defs.margins) at points of the box with eps = 1/n.
Strip: Ghat_a, Ghat_b, Ghat_ab enclosures (coef_with_contrib) must contain the true values; tails: the certified lower
bounds of L1, L2, L3 (resp. a L1, L2, a L3) must not exceed the true values."""
import random
from fractions import Fraction as Fr
import mpmath as mp
mp.mp.dps = 50
from flint import arb, fmpq
import iv_as as AS
import iv_far as T
import iv_atoms as AT
from iv_jet import Jet
from ref_defs import margins

rnd = random.Random(33)
E = Fr(1, 37)
q = lambda x: arb(fmpq(x.numerator, x.denominator))
viol = chk = 0


def ref(n, a, d):
    F0, L1, L2, L3 = margins(n, float(a), float(d), dps=int(200 + 0.3 * float(a + d)),
                             h=mp.mpf(10) ** -35 * min(1, float(a), float(d)))
    return L1, L2, L3


def ns_in(e0, e1):
    out = [n for n in range(37, 5000) if e0 <= Fr(1, n) <= e1][:2]
    if e0 == 0:
        out.append(None)
    return out


# strip boxes (direct form, b <= x0 + 4)
for it in range(10):
    a0 = Fr(rnd.randrange(0, 12), 4) if rnd.random() < 0.7 else Fr(0)
    a1 = a0 + Fr(1, 16)
    b0 = max(a1, Fr(1, 4)) + Fr(rnd.randrange(0, 20), 8)
    b1 = b0 + Fr(1, 16)
    k = rnd.randrange(16)
    e0, e1 = E * k / 16, E * (k + 1) / 16
    try:
        r = AS.evaluate('direct', a0, a1, b0, b1, e0, e1)
        enc = [AS.coef_with_contrib(r, 1, 0)[0], AS.coef_with_contrib(r, 0, 1)[0], AS.coef_with_contrib(r, 1, 1)[0]]
    except Exception as ex:
        print('strip box failed to evaluate', [float(x) for x in (a0, a1, b0, b1)], ex)
        continue
    for n in ns_in(e0, e1):
        for _ in range(2):
            a = a0 + (a1 - a0) * Fr(rnd.randrange(1, 100), 100)
            b = b0 + (b1 - b0) * Fr(rnd.randrange(0, 101), 100)
            L1, L2, L3 = ref(n, a, b - a)
            true = (L1 - 1 / mp.mpf(float(a)), 1 / mp.mpf(float(b)) - L2, L1 * L2 - L3)
            for kk in range(3):
                chk += 1
                lo, hi = mp.mpf(enc[kk].lower().str(40, radius=False)), mp.mpf(enc[kk].upper().str(40, radius=False))
                if not (lo - mp.mpf('1e-25') <= true[kk] <= hi + mp.mpf('1e-25')):
                    viol += 1
                    print('STRIP VIOLATION', [float(x) for x in (a0, a1, b0, b1, e0, e1)], n, float(a), float(b), kk, true[kk], lo, hi)
    print('strip box ok', [float(x) for x in (a0, a1, b0, b1)], flush=True)

# far-d boxes (a in [3, 250])
X = 10 * AT.far_d_atom_bound(512, 250)[0]
for it in range(6):
    a0 = Fr(rnd.randrange(3, 249)); a1 = a0 + 1
    j = rnd.randrange(4); w0, w1 = Fr(j, 2048), Fr(j + 1, 2048)
    k = rnd.randrange(8); e0, e1 = E * k / 8, E * (k + 1) / 8
    Lc, _, _ = T.conds_ad(T.logF_far_reg(Jet.var(q((a0 + a1) / 2), 0, T.SPT), w0, w1, e0, e1, X))
    _, La, _ = T.conds_ad(T.logF_far_reg(Jet.var(arb.union(q(a0), q(a1)), 0, T.SPT), w0, w1, e0, e1, X))
    lows = [Lc[kk] - abs(La[kk]) * q((a1 - a0) / 2) for kk in range(3)]
    for n in ns_in(e0, e1)[:2]:
        a = a0 + Fr(rnd.randrange(0, 101), 100)
        d = 1 / (w0 + (w1 - w0) * Fr(rnd.randrange(1, 101), 100))
        if float(d) > 3000:
            d = Fr(3000)
        L = ref(n, a, d)
        for kk in range(3):
            chk += 1
            if L[kk] < mp.mpf(lows[kk].lower().str(40, radius=False)):
                viol += 1
                print('FAR VIOLATION', float(a), float(d), n, kk, L[kk], lows[kk])
    print('far-d box ok', float(a0), [float(x) for x in (w0, w1, e0, e1)], flush=True)

# a-tail boxes (m-cells), checked at a = a(m, eps) for a few points
for it in range(6):
    k = rnd.randrange(8); e0, e1 = E * k / 8, E * (k + 1) / 8
    import iv_tail_run as R
    mtop = R.m250(e0)
    m0, m1 = mtop / 2, mtop
    d0 = Fr(rnd.randrange(4, 60)); d1 = d0 + Fr(1, 4)
    amin = R.amin_of(m1, e1)
    Xa = 10 * AT.a_tail_atom_bound(float(amin), float(d1))[0]
    ma = arb.union(q(m0), q(m1)); eps = arb.union(q(e0), q(e1))
    Lc, _, _ = T.conds_ad(T.logF_atail(ma, eps, Jet.var(q((d0 + d1) / 2), 1, T.SPT), Xa, 'nu'))
    _, _, Ld = T.conds_ad(T.logF_atail(ma, eps, Jet.var(arb.union(q(d0), q(d1)), 1, T.SPT), Xa, 'nu'))
    lows = [Lc[kk] - abs(Ld[kk]) * q((d1 - d0) / 2) for kk in range(3)]
    for n in ns_in(e0, e1)[:2]:
        if n is None:
            continue
        # a with m_a(a, 1/n) in [m0, m1]: m = 1/(a phi(a/n)) -> solve numerically by bisection
        lo_a, hi_a = 50.0, 5000.0
        mt = float(m0 + m1) / 2
        f = lambda aa: 1 / (aa * mp.expm1(aa / n) / (aa / n)) - mt
        for _ in range(80):
            mid = (lo_a + hi_a) / 2
            if f(mid) > 0:
                lo_a = mid
            else:
                hi_a = mid
        a = Fr(lo_a).limit_denominator(10 ** 6)
        d = d0 + Fr(1, 8)
        L = ref(n, a, d)
        for kk in range(3):
            chk += 1
            if L[kk] < mp.mpf(lows[kk].lower().str(40, radius=False)):
                viol += 1
                print('A-TAIL VIOLATION', float(a), float(d), n, kk, L[kk], lows[kk])
    print('a-tail box ok', [float(x) for x in (m0, m1, d0, d1, e0, e1)], flush=True)
print(f"self-test 2: {chk} comparisons, {viol} violations")
