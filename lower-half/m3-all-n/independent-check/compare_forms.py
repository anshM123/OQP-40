"""Their forms at thin points (tb_arb.logF_nu2, tb_arb.logF_mixed3, tb_sx direct / nu via Ghat coefficients) versus my
reference straight from the definitions (ref_defs.margins, 150+ digits, central differences).  Numerical check."""
import os
import sys
import random
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
from fractions import Fraction as Fr
import mpmath as mp
from flint import arb, fmpq
import tb_arb as T
import tb_sx as S
from ref_defs import margins

mp.mp.dps = 60
rnd = random.Random(11)
q = lambda x: arb(fmpq(x.numerator, x.denominator))


def to_mp(x):
    return mp.mpf(x.mid().str(50, radius=False))


def ref(n, a, d):
    with mp.workdps(60):
        F, L1, L2, L3 = margins(n, mp.mpf(a.numerator) / a.denominator, mp.mpf(d.numerator) / d.denominator,
                                dps=int(160 + 0.3 * float(a + d)), h=mp.mpf(10) ** -35 * min(1, float(a), float(d)))
    return L1, L2, L3


def theirs_tbarb(form, n, a, d):
    eps = q(Fr(0)) if n is None else q(Fr(1, n))
    cx = T.Ctx(eps)
    A = T.J.var(q(a), 0, T.MP)
    B = T.J.var(q(a + d), 1, T.MP)
    L, _ = T.margins_from_logF(form(A, B, cx))
    return L


def theirs_sx(form, n, a, d):
    """Ghat coefficients at a thin point from tb_sx.evaluate (box of zero width) -> L1, L2, L3."""
    e = Fr(0) if n is None else Fr(1, n)
    b = a + d
    r = S.evaluate(form, 'ab', a, a, b, b, e, e, ke=0)
    ga = S.coef_box(r, 1, 0)[0]
    gb = S.coef_box(r, 0, 1)[0]
    gab = S.coef_box(r, 1, 1)[0]
    L1 = 1 / q(a) + ga
    L2 = 1 / q(b) - gb
    L3 = L1 * L2 - gab
    return (L1, L2, L3)


worst = {}
for it in range(60):
    n = rnd.choice([37, 41, 50, 100, 1000, None])
    kind = rnd.choice(['nu2', 'mixed3', 'sx_direct', 'sx_nu'])
    if kind == 'nu2':
        a = Fr(rnd.randrange(3 * 64, 64 * 64), 64); d = Fr(rnd.randrange(3 * 16, 512 * 16), 16)
        L = theirs_tbarb(T.logF_nu2, n, a, d)
    elif kind == 'mixed3':
        a = Fr(rnd.randrange(3 * 64, 64 * 64), 64); d = Fr(rnd.randrange(1, 4 * 64), 64)
        L = theirs_tbarb(T.logF_mixed3, n, a, d)
    elif kind == 'sx_direct':
        a = Fr(rnd.randrange(1, 3 * 64), 64); d = Fr(rnd.randrange(1, 4 * 64), 64)
        L = theirs_sx('direct', n, a, d)
    else:
        a = Fr(rnd.randrange(1, 3 * 64), 64); d = Fr(rnd.randrange(4 * 8, 500 * 8), 8)
        L = theirs_sx('nu', n, a, d)
    R = ref(n, a, d)
    dev = max(abs(to_mp(L[k]) - R[k]) / abs(R[k]) for k in range(3))
    worst[kind] = max(worst.get(kind, 0), dev)
    print(f"{kind:9s} n={n} a={float(a):.5f} d={float(d):.5f}: theirs L3={L[2].mid().str(12, radius=False)} "
          f"ref L3={mp.nstr(R[2], 12)}  max rel.dev(L1..L3) {mp.nstr(dev, 3)}", flush=True)
print("worst relative deviation per form:", {k: mp.nstr(v, 3) for k, v in worst.items()})
