"""Thin-point check of iv_forms.logF_nu against the definitions (ref_defs.margins)."""
import random
import mpmath as mp
mp.mp.dps = 60
from flint import arb, fmpq
import iv_jet as JJ
from iv_jet import Jet, SP3
import iv_forms as FF
from ref_defs import margins

rnd = random.Random(5)
worst = 0
for it in range(40):
    n = rnd.choice([37, 38, 50, 100, 1000, 10 ** 5, None])
    a = rnd.choice([3.0, 5.0, 16.0, 50.0, 64.0, 100.0, 120.0, rnd.uniform(3, 130)])
    d = rnd.choice([3.0, 4.0, 5.5, 7.9, 8.36, 25.0, 64.0, 511.0, rnd.uniform(3, 100)])
    eps = arb(0) if n is None else arb(fmpq(1, n))
    A = Jet.var(arb(a), 0, SP3)
    D = Jet.var(arb(d), 1, SP3)
    E = Jet.var(eps, 2, SP3)
    G = FF.logF_nus2(A, D, E)
    L = FF.conditions(G)
    F0, R1, R2, R3 = margins(n, a, d, dps=int(150 + 0.3 * (a + d)), h=mp.mpf(10) ** -30)
    dev = max(abs(mp.mpf(L[0].mid().str(40, radius=False)) - R1) / abs(R1), abs(mp.mpf(L[1].mid().str(40, radius=False)) - R2) / abs(R2),
              abs(mp.mpf(L[2].mid().str(40, radius=False)) - R3) / abs(R3))
    worst = max(worst, dev)
    print(f"n={n} a={a:.4f} d={d:.4f}: L = {L[0].mid().str(10)}, {L[1].mid().str(10)}, {L[2].mid().str(10)}  "
          f"radii {float(L[2].rad()):.1e}  rel.dev vs definitions {mp.nstr(dev, 3)}")
print("max relative deviation:", mp.nstr(worst, 3))
