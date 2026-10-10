"""Random-point check of the four Lemma 4 conditions straight from the definitions (ref_defs.py), for n in
[37, 10^6] (log-uniform, plus fixed n) and the limit kernel.  Numerical evidence only.
Usage: python sample_defs.py SEED NPTS > log
Each line: n a d F L1 L2 L3 (aL1, aL3 also reported); a summary of minima per regime at the end.
"""
import sys
import random
import math
import mpmath as mp
from ref_defs import margins

seed = int(sys.argv[1])
npts = int(sys.argv[2])
rnd = random.Random(seed)

# special values hit with positive probability: chart boundaries and critical regions
A_SPECIAL = [1e-3, 0.01, 0.25, 0.5, 1.0, 1.5, 2.999, 3.0, 3.001, 8.0, 16.0, 40.0, 63.99, 64.0, 64.01, 100.0, 500.0]
D_SPECIAL = [1e-4, 1e-3, 0.01, 0.1, 1.0, 2.999, 3.0, 3.001, 3.75, 4.0, 8.36, 15.999, 16.0, 40.0, 63.99, 64.0, 64.01,
             511.9, 512.0, 512.1, 515.0, 700.0]


def draw():
    u = rnd.random()
    if u < 0.15:
        n = None
    elif u < 0.35:
        n = rnd.choice([37, 38, 40, 41, 50, 64, 100])
    else:
        n = int(math.exp(rnd.uniform(math.log(37), math.log(1e6))))
    v = rnd.random()
    if v < 0.25:
        a = rnd.choice(A_SPECIAL)
    elif v < 0.45:
        a = rnd.uniform(0.0005, 3.0)
    elif v < 0.65:
        a = rnd.uniform(40, 130)
    else:
        a = math.exp(rnd.uniform(math.log(1e-3), math.log(3000)))
    w = rnd.random()
    if w < 0.25:
        d = rnd.choice(D_SPECIAL)
    elif w < 0.45:
        d = rnd.uniform(20, 70)
    elif w < 0.55:
        d = rnd.uniform(0.0001, 0.3)
    else:
        d = math.exp(rnd.uniform(math.log(1e-4), math.log(1500)))
    return n, a, d


def regime(a, d):
    if a < 3:
        return 'strip a<3'
    if d >= 512:
        return 'far d>=512'
    if a >= 64:
        return 'tail a>=64'
    if d <= 3:
        return 'd-strip'
    return 'core'


mins = {}
bad = 0
for k in range(npts):
    n, a, d = draw()
    mn = min(1.0, a, d)
    dps = int(150 + 0.27 * (a + d) + 4 * math.log10((n or 1) + 1) + 3 * max(0.0, math.log10((n or 1) / min(a, d))) + 3 * max(0.0, -math.log10(mn)))
    H = mp.mpf(10) ** (-30) * mn
    try:
        F, L1, L2, L3 = margins(n, a, d, dps=dps, h=H)
        if not all(isinstance(x, mp.mpf) for x in (F, L1, L2, L3)):
            raise TypeError('complex')
    except (TypeError, ValueError, ZeroDivisionError) as ex:
        print(f"# precision problem at n={n} a={a} d={d} dps={dps}: {ex}; retrying with 3x digits", flush=True)
        dps = 3 * dps
        F, L1, L2, L3 = margins(n, a, d, dps=dps, h=H)
    # accuracy check on every 10th point: repeat with more digits and a different step
    acc = None
    if k % 10 == 0:
        F2, M1, M2, M3 = margins(n, a, d, dps=dps + 40, h=H / 1000)
        acc = max(abs(L1 - M1) / abs(M1), abs(L2 - M2) / abs(M2), abs(L3 - M3) / abs(M3))
    ok = F > 0 and L1 > 0 and L2 > 0 and L3 > 0
    if not ok:
        bad += 1
    reg = regime(a, d)
    key = (reg, 'inf' if n is None else ('37-100' if n <= 100 else ('101-10^4' if n <= 10 ** 4 else '>10^4')))
    vals = {'L1': L1, 'L2': L2, 'L3': L3, 'aL1': a * L1, 'aL3': a * L3}
    m = mins.setdefault(key, {})
    for kk, v in vals.items():
        if kk not in m or v < m[kk][0]:
            m[kk] = (v, n, a, d)
    print(f"{'inf' if n is None else n} {a:.6g} {d:.6g} F={mp.nstr(F, 8)} L1={mp.nstr(L1, 8)} L2={mp.nstr(L2, 8)} "
          f"L3={mp.nstr(L3, 8)}{'' if acc is None else ' acc=' + mp.nstr(acc, 2)}{'' if ok else '  VIOLATION'}", flush=True)

print(f"\nsamples: {npts}, violations: {bad}")
for key in sorted(mins):
    m = mins[key]
    print(key, '  '.join(f"{kk}>={mp.nstr(v[0], 5)} (n={v[1]}, a={v[2]:.4g}, d={v[3]:.4g})" for kk, v in sorted(m.items())))
