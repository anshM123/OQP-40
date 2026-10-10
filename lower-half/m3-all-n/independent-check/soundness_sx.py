"""Soundness spot-check of tb_sx.py (their strip code, unchanged): enclosures of Ghat_a, Ghat_b, Ghat_ab
(coef_box) on random boxes of the strip charts versus true values at random points of the box with b > a, computed
by my own thin jets (iv_forms.logF_nus, an exact rearrangement of (F1); 200 bits).
Ghat = log F - log a + log b:  Ghat_a = L1 - 1/a,  Ghat_b = 1/b - L2,  Ghat_ab = L1 L2 - L3   (partials at fixed b / a).
Usage: python soundness_sx.py NBOX NPT SEED
"""
import os
import sys
import random
from fractions import Fraction as Fr
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
from flint import arb, fmpq
import tb_sx as S
import iv_jet as JJ
from iv_jet import Jet
import iv_dual as DU
import iv_forms as FF

NBOX, NPT, SEED = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
rnd = random.Random(SEED)
q = lambda x: arb(fmpq(x.numerator, x.denominator))
E37 = Fr(1, 37)


def truth(a, b, e):
    d = b - a
    G = FF.logF_nus(Jet.var(q(a), 0, DU.SP4), Jet.var(q(d), 1, DU.SP4), Jet.var(q(e), 2, DU.SP4))
    L1, L2, L3 = FF.conditions(G)
    return (L1 - 1 / q(a), 1 / q(b) - L2, L1 * L2 - L3)


nchk = nviol = nbox_ok = 0
for ib in range(NBOX):
    kind = rnd.choice(['direct', 'direct', 'nu', 'nubox', 'nu_far', 'corner'])
    S.Tight.BOX = (kind == 'nubox')
    if kind == 'corner':
        form, corner = 'direct', True
        a0, a1, b0, b1 = Fr(0), Fr(1, 4), Fr(0), Fr(1, 4)
        e0, e1 = Fr(0), E37
    else:
        corner = False
        wa = Fr(1, rnd.choice([8, 16, 32])) if kind != 'nu_far' else Fr(1, 2)
        a0 = Fr(rnd.randrange(0, int(3 / wa))) * wa
        if rnd.random() < 0.3:
            a0 = Fr(0)
        a1 = a0 + wa
        if kind == 'direct':
            form = 'direct'
            b0 = max(Fr(1, 4), a0) + Fr(rnd.randrange(0, 24), 8)
            wb = Fr(1, rnd.choice([8, 16, 32]))
        elif kind == 'nu_far':
            form = 'nu'
            b0 = a1 + Fr(15, 2) + Fr(rnd.randrange(0, 400))
            wb = Fr(rnd.choice([1, 2, 4]), 2)
        else:
            form = 'nu'
            b0 = a1 + Fr(15, 4) + Fr(rnd.randrange(0, 24), 8)
            wb = Fr(1, rnd.choice([16, 32]))
        b1 = b0 + wb
        ne = rnd.choice([8, 16, 32, 64])
        k = rnd.randrange(ne)
        e0, e1 = E37 * k / ne, E37 * (k + 1) / ne
    try:
        r = S.evaluate(form, 'ab', a0, a1, b0, b1, e0, e1, ke=2, corner=corner, J=10)
        enc = [S.coef_box(r, 1, 0)[0], S.coef_box(r, 0, 1)[0], S.coef_box(r, 1, 1)[0]]
    except Exception as ex:
        print(f"{kind} box {[float(x) for x in (a0, a1, b0, b1, e0, e1)]}: evaluation failed ({str(ex)[:50]})")
        continue
    nbox_ok += 1
    for ip in range(NPT):
        for _ in range(100):
            a = a0 + (a1 - a0) * Fr(rnd.randrange(1, 1000), 1000)
            b = b0 + (b1 - b0) * Fr(rnd.randrange(0, 1001), 1000)
            if b - a > Fr(1, 1000):
                break
        else:
            continue
        e = e0 + (e1 - e0) * Fr(rnd.randrange(0, 1001), 1000)
        tv = truth(a, b, e)
        for kk, name in enumerate(('Ghat_a', 'Ghat_b', 'Ghat_ab')):
            nchk += 1
            if not enc[kk].overlaps(tv[kk]):
                nviol += 1
                print(f"VIOLATION {kind} box {[float(x) for x in (a0, a1, b0, b1, e0, e1)]} point "
                      f"({float(a)}, {float(b)}, {float(e)}) {name}: true {tv[kk].mid().str(12, radius=False)} "
                      f"enclosure [{enc[kk].lower().str(10, radius=False)}, {enc[kk].upper().str(10, radius=False)}]", flush=True)
    if ib % 10 == 0:
        print(f"  {ib + 1} boxes, {nchk} checks, {nviol} violations", flush=True)
print(f"tb_sx soundness spot-check: {nbox_ok} boxes evaluated, {nchk} checks, {nviol} violations")
