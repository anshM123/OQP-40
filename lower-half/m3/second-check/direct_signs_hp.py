"""Re-evaluate the direct sign check at the points where 60 digits gave negative values, at several precisions.
Same definitions as direct_signs.py. Usage: python direct_signs_hp.py n points seed"""
import random
import sys
from math import comb

import mpmath as mp

n = int(sys.argv[1])
NP = int(sys.argv[2])
rng = random.Random(int(sys.argv[3]))
C = comb(n + 2, 2)


def hn(x, y, z):
    tot = mp.mpf(0)
    for i in range(n + 1):
        k = n - i
        hk = (k + 1) * y**k if y == z else (y**(k + 1) - z**(k + 1)) / (y - z)
        tot += x**i * hk
    return tot


def K(x, y, z):
    return hn(x, y, z) / C - (x * y * z)**(mp.mpf(n) / 3)


def F(s, t):
    E = K(1, s, t) - mp.sqrt(K(t, 1, 1) * K(t, s, s))
    return E / mp.sqrt(K(1, s, s) * K(1, t, t))


def vals(s, t):
    return {'F': F(s, t), 'F_s': mp.diff(lambda x: F(x, t), s), '-F_t': -mp.diff(lambda y: F(s, y), t),
            '-F_st': -mp.diff(lambda x, y: F(x, y), (s, t), (1, 1))}


# regenerate exactly the same points as direct_signs.py (same RNG calls, as strings so that precision can change)
mp.mp.dps = 60
pts = []
for _ in range(NP):
    a, b = sorted(rng.uniform(0, 4) for _ in range(2))
    pts.append((a, b, 'A'))
for _ in range(NP // 4):
    x = rng.uniform(0, 3); y = rng.uniform(-6, -1)
    pts.append((x, y, 'B'))
for _ in range(NP // 4):
    x = rng.uniform(-5, -1); y = rng.uniform(-1, 2)
    pts.append((x, y, 'C'))


def make(p):
    a, b, kind = p
    if kind == 'A':
        return mp.mpf(10)**a + mp.mpf('1e-3'), mp.mpf(10)**b + mp.mpf('2e-3')
    if kind == 'B':
        s = mp.mpf(10)**a + mp.mpf('1e-3')
        return s, s * (1 + mp.mpf(10)**b)
    return 1 + mp.mpf(10)**a, 1 + mp.mpf(10)**b


flagged = []
for p in pts:
    s, t = make(p)
    if not (1 < s < t):
        continue
    v = vals(s, t)
    if any(val < -mp.mpf('1e-40') for val in v.values()):
        flagged.append(p)
print(f"n = {n}: {len(flagged)} flagged points at 60 digits", flush=True)
for p in flagged[:12]:
    out = []
    for dps in (60, 150, 300):
        mp.mp.dps = dps
        s, t = make(p)
        v = vals(s, t)
        out.append(f"dps {dps}: " + ", ".join(f"{k} {mp.nstr(val, 4)}" for k, val in v.items()))
    mp.mp.dps = 60
    s, t = make(p)
    print(f"  s = {mp.nstr(s, 8)}, t = {mp.nstr(t, 8)}\n    " + "\n    ".join(out), flush=True)
