"""Thin-point check of iv_forms.logF_mix (mixed form + series pieces) against the definitions."""
import random
import mpmath as mp
mp.mp.dps = 60
from flint import arb, fmpq
from iv_jet import Jet
import iv_dual as DU
import iv_forms as FF
from ref_defs import margins
rnd = random.Random(8)
worst = 0
for it in range(30):
    n = rnd.choice([37, 38, 50, 100, 1000, None])
    a = rnd.choice([0.5, 1.0, 2.0, 3.0, 5.0, 16.0, 40.0, 64.0, rnd.uniform(0.5, 64)])
    d = rnd.choice([0.001, 0.01, 0.1, 0.5, 1.0, 1.9, 2.5, 3.0, 3.75, rnd.uniform(0.001, 3.9)])
    eps = arb(0) if n is None else arb(fmpq(1, n))
    G = FF.logF_mix(Jet.var(arb(a), 0, DU.SP4), Jet.var(arb(d), 1, DU.SP4), Jet.var(eps, 2, DU.SP4))
    L = FF.conditions(G)
    F0, R1, R2, R3 = margins(n, a, d, dps=int(160 + 0.3 * (a + d)), h=mp.mpf(10) ** -35 * min(1, a, d))
    dev = max(abs(mp.mpf(L[k].mid().str(50, radius=False)) - R) / abs(R) for k, R in enumerate((R1, R2, R3)))
    worst = max(worst, dev)
    print(f"n={n} a={a:.4f} d={d:.4f}: L3={L[2].mid().str(10, radius=False)} ref {mp.nstr(R3, 10)} rel.dev {mp.nstr(dev, 3)}", flush=True)
print("max relative deviation:", mp.nstr(worst, 3))
