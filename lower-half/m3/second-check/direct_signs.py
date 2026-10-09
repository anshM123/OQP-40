"""Check the four Lemma 7 conditions for the min-apex kernel straight from the definitions, with no polynomial
algebra: K_n(x,y,z) = h_n(x,y,z)/C(n+2,2) - (xyz)^(n/3), E(s,t) = K_n(1,s,t) - sqrt(K_n(t,1,1) K_n(t,s,s)) for s < t,
w(s) = sqrt(K_n(1,s,s)), F = E/(w(s) w(t)). Derivatives by mpmath numerical differentiation at 60 digits.
Sample points: log-uniform s < t in (1, 1e4), points near the diagonal, and points near s = 1.
Usage: python direct_signs.py n [points] [seed] [digits]   (60 digits by default; use 250 for n >= 30)"""
import random
import sys
from math import comb

import mpmath as mp

mp.mp.dps = int(sys.argv[4]) if len(sys.argv) > 4 else 60
n = int(sys.argv[1])
NP = int(sys.argv[2]) if len(sys.argv) > 2 else 300
rng = random.Random(int(sys.argv[3]) if len(sys.argv) > 3 else 1)
C = comb(n + 2, 2)


def hn(x, y, z):
    # complete homogeneous symmetric polynomial of degree n, via h_n = sum_i x^i h_{n-i}(y,z)
    tot = mp.mpf(0)
    for i in range(n + 1):
        k = n - i
        # h_k(y, z) = (y^{k+1} - z^{k+1})/(y - z), or (k+1) y^k if y == z
        hk = (k + 1) * y**k if y == z else (y**(k + 1) - z**(k + 1)) / (y - z)
        tot += x**i * hk
    return tot


def K(x, y, z):
    return hn(x, y, z) / C - (x * y * z)**(mp.mpf(n) / 3)


def F(s, t):
    E = K(1, s, t) - mp.sqrt(K(t, 1, 1) * K(t, s, s))
    return E / mp.sqrt(K(1, s, s) * K(1, t, t))


worst = {'F': mp.inf, 'F_s': mp.inf, '-F_t': mp.inf, '-F_st': mp.inf}
pts = []
for _ in range(NP):
    a, b = sorted(rng.uniform(0, 4) for _ in range(2))
    pts.append((mp.mpf(10)**a + mp.mpf('1e-3'), mp.mpf(10)**b + mp.mpf('2e-3')))
for _ in range(NP // 4):
    s = mp.mpf(10)**rng.uniform(0, 3) + mp.mpf('1e-3')
    pts.append((s, s * (1 + mp.mpf(10)**rng.uniform(-6, -1))))
for _ in range(NP // 4):
    pts.append((1 + mp.mpf(10)**rng.uniform(-5, -1), 1 + mp.mpf(10)**rng.uniform(-1, 2)))
bad = 0
for s, t in pts:
    if not (1 < s < t):
        continue
    vals = {'F': F(s, t),
            'F_s': mp.diff(lambda x: F(x, t), s),
            '-F_t': -mp.diff(lambda y: F(s, y), t),
            '-F_st': -mp.diff(lambda x, y: F(x, y), (s, t), (1, 1))}
    for k, val in vals.items():
        scale = 1 if k == 'F' else 1 / s if k == 'F_s' else 1 / t if k == '-F_t' else 1 / (s * t)
        r = val / scale
        if r < worst[k]:
            worst[k] = r
        if val < -mp.mpf('1e-40'):
            bad += 1
print(f"n = {n}: {len(pts)} points; minima (scaled): " +
      ", ".join(f"{k} {mp.nstr(val, 5)}" for k, val in worst.items()) + f"; negative values: {bad}", flush=True)
