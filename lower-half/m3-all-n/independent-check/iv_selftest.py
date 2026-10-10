"""Self-test of my verifier: on random boxes, the certified lower bounds lows_k must be <= the true L_k (definitions,
ref_defs.margins) at points of the box with eps = 1/n (n integer) or eps = 0."""
import random
from fractions import Fraction as Fr
import mpmath as mp
mp.mp.dps = 50
import iv_bb2 as BB
import iv_forms as FF
from ref_defs import margins
rnd = random.Random(21)
E = Fr(1, 37)
viol = chk = 0
for it in range(24):
    form, (alo, ahi, dlo, dhi) = rnd.choice([(FF.logF_nus, (50, 119, 25, 59)), (FF.logF_nus, (16, 49, 16, 63)),
                                              (FF.logF_mix, (14, 31, 1.75, 2.4))])
    if form is FF.logF_mix:
        a0 = Fr(rnd.randrange(int(alo * 8), int(ahi * 8)), 8); a1 = a0 + Fr(1, 8)
        d0 = Fr(rnd.randrange(int(dlo * 16), int(dhi * 16)), 16); d1 = d0 + Fr(1, 16)
    else:
        a0 = Fr(rnd.randrange(alo, ahi)); a1 = a0 + 1
        d0 = Fr(rnd.randrange(dlo, dhi)); d1 = d0 + 1
    k = rnd.randrange(8)
    e0, e1 = E * k / 8, E * (k + 1) / 8
    try:
        lows, contrib, Lc = BB.check(form, a0, a1, d0, d1, e0, e1)
    except Exception as ex:
        print('box failed to evaluate', ex); continue
    ns = [n for n in range(37, 3000) if e0 <= Fr(1, n) <= e1][:3] + ([None] if e0 == 0 else [])
    for n in ns:
        for _ in range(2):
            a = float(a0 + (a1 - a0) * Fr(rnd.randrange(0, 101), 100)); d = float(d0 + (d1 - d0) * Fr(rnd.randrange(0, 101), 100))
            F, L1, L2, L3 = margins(n, a, d, dps=int(150 + 0.3 * (a + d)), h=mp.mpf(10) ** -30)
            for kk, L in enumerate((L1, L2, L3)):
                chk += 1
                if L < mp.mpf(lows[kk].lower().str(30, radius=False)):
                    viol += 1
                    print('VIOLATION', [float(x) for x in (a0, a1, d0, d1, e0, e1)], n, a, d, kk + 1, L, lows[kk])
    print(f"box {[round(float(x), 4) for x in (a0, a1, d0, d1, e0, e1)]}: lows {[round(float(l.lower()), 5) for l in lows]}, checked n = {ns}", flush=True)
print(f"self-test: {chk} comparisons, {viol} violations")
