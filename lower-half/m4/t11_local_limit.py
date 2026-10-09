"""Consistency check of the local analysis: near x=y=e=f=1 every smooth rule must be, at second order,
    k(xy;ef) ~ (lambda/8) [ (2 s_e - s_x - s_y)(2 s_f - s_x - s_y) + 5 (s_x - s_y)^2 ],  lambda = n(n+4)/20,
s = log(eigenvalue).  Compare with the exact polynomial rules (high precision).  Usage: python t11_local_limit.py rule.json"""
import json, sys
from fractions import Fraction
from math import comb
import mpmath as mp
mp.mp.dps = 60
d = json.load(open(sys.argv[1])); n, qd = d["n"], d["qd"]; N = n * qd
z = [Fraction(x) for x in d["z"]]; var = [(tuple(p), tuple(q)) for p, q in d["var"]]
vidx = {k: t for t, k in enumerate(var)}; live = set(d["exponents_units"]); C3 = comb(n + 3, 3)
def kappa(p, q):
    a, b = p; i, j = q; v = Fraction(0)
    if all(t % qd == 0 for t in (a, b, i, j)): v += Fraction(1, C3)
    if 4 * a == N and a == b == i == j: v -= 1
    return v
def gamma(p, q):
    if p == q: return kappa(p, q)
    if (p, q) in vidx: return z[vidx[(p, q)]]
    if (q, p) in vidx: return 2 * kappa(p, q) - z[vidx[(q, p)]]
    if q[1] not in live: return Fraction(0)
    return 2 * kappa(p, q)
terms = []
for a in range(N + 1):
    for b in range(N + 1 - a):
        for i in range(N + 1 - a - b):
            j = N - a - b - i
            g = gamma((min(a, b), max(a, b)), (min(i, j), max(i, j)))
            if g: terms.append((a, b, i, j, mp.mpf(g.numerator) / g.denominator))
def k(sx, sy, se, sf):
    return mp.fsum(g * mp.exp((a * sx + b * sy + i * se + j * sf) / qd) for a, b, i, j, g in terms)
lam = mp.mpf(n * (n + 4)) / 20
import random
random.seed(1)
worst = 0
for t in range(20):
    v = [random.uniform(-1, 1) for _ in range(4)]
    eps = mp.mpf(10) ** -12
    sx, sy, se, sf = [eps * x for x in v]
    val = k(sx, sy, se, sf) / eps ** 2
    pred = lam / 8 * ((2 * v[2] - v[0] - v[1]) * (2 * v[3] - v[0] - v[1]) + 5 * (v[0] - v[1]) ** 2)
    worst = max(worst, abs(val - pred) / max(abs(pred), 1e-3))
print(f"n={n}: max relative deviation of k/eps^2 from the predicted local quadratic form: {mp.nstr(worst, 5)}")
