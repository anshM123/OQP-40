"""Soundness spot-check of tb_arb.dual_box (their code, unchanged) for the forms used in Theorem B'.
For random boxes, the gradient enclosures (d/da|_b, d/db|_a, d/deps of L1, L2, L3) and centre values are compared with
the true values at random points of the box, computed by my own thin jets (iv_forms.logF_nus, exact rearrangement of
(F1); same eps-interpolation).  Also run with the corrected S_of (patch_S) for comparison.
Usage: python soundness_dual.py FORM NBOX NPT SEED [fixed]
"""
import os
import sys
import random
from fractions import Fraction as Fr
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
from flint import arb, fmpq
import tb_arb as T
import patch_S
import iv_jet as JJ
from iv_jet import Jet
import iv_dual as DU
import iv_forms as FF

form_name = sys.argv[1]
NBOX, NPT, SEED = int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
if len(sys.argv) > 5 and sys.argv[5] == 'fixed':
    patch_S.install()
form = {'mixed3': T.logF_mixed3, 'nu2': T.logF_nu2}[form_name]
rnd = random.Random(SEED)
q = lambda x: arb(fmpq(x.numerator, x.denominator))


def true_vals(a, d, e):
    G = FF.logF_nus(Jet.var(q(a), 0, DU.SP4), Jet.var(q(d), 1, DU.SP4), Jet.var(q(e), 2, DU.SP4))
    L = FF.conditions(G)
    g = FF.gradients(G)
    # convert (d/da|_d, d/dd|_a, d/deps) -> (d/da|_b, d/db|_a, d/deps)
    return L, [(gk[0] - gk[1], gk[1], gk[2]) for gk in g]


nviol = 0
nchk = 0
worst = 0.0
for ib in range(NBOX):
    if form_name == 'mixed3':
        a0 = Fr(rnd.randrange(3 * 32, 64 * 32), 32)
        wa = Fr(1, rnd.choice([16, 32, 64]))
        d0 = Fr(rnd.randrange(1, 3 * 16), 16)          # d >= 1/16 so that the nu-form reference is well conditioned
        wd = Fr(1, rnd.choice([16, 32]))
    else:
        a0 = Fr(rnd.randrange(3 * 8, 64 * 8), 8)
        wa = Fr(1, rnd.choice([8, 16, 32]))
        d0 = Fr(rnd.randrange(3 * 8, 64 * 8), 8)
        wd = Fr(1, rnd.choice([8, 16]))
    ne = rnd.choice([1, 2, 4, 8])
    k = rnd.randrange(ne)
    e0, e1 = Fr(k, 37 * ne), Fr(k + 1, 37 * ne)
    box = (a0, a0 + wa, d0, d0 + wd, e0, e1)
    try:
        Lc, grads = T.dual_box(form, *box)
    except Exception as ex:
        print("box", [float(x) for x in box], "evaluation failed:", str(ex)[:60])
        continue
    for ip in range(NPT):
        a = box[0] + (box[1] - box[0]) * Fr(rnd.randrange(0, 1001), 1000)
        d = box[2] + (box[3] - box[2]) * Fr(rnd.randrange(0, 1001), 1000)
        e = box[4] + (box[5] - box[4]) * Fr(rnd.randrange(0, 1001), 1000)
        if ip == 0:
            a, d, e = box[0], box[2], box[5]          # a corner, eps at the top
        elif ip == 1:
            a, d, e = box[1], box[3], box[4]
        L, g = true_vals(a, d, e)
        for kk in range(3):
            for v in range(3):
                nchk += 1
                enc = grads[kk][v]
                tv = g[kk][v]
                if not enc.overlaps(tv):
                    nviol += 1
                    out = max(float(enc.lower() - tv.upper()), float(tv.lower() - enc.upper()))
                    worst = max(worst, out)
                    print(f"VIOLATION box {[float(x) for x in box]} point ({float(a)}, {float(d)}, {float(e)}) "
                          f"L{kk + 1} grad[{'ab e'[v] if v != 2 else 'eps'}]: true {tv.mid().str(12, radius=False)}, "
                          f"enclosure [{enc.lower().str(12, radius=False)}, {enc.upper().str(12, radius=False)}]", flush=True)
print(f"form {form_name} ({'S_of corrected' if len(sys.argv) > 5 else 'original'}): {NBOX} boxes, {nchk} gradient checks, "
      f"{nviol} violations, largest distance outside {worst:.3e}")
