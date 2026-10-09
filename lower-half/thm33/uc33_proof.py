"""Symbolic set-up of the three conditions for F = N1/sqrt(BC) (interval-mixture criterion):
 (I)  G + 2B G_B >= 0,   (II) G - 2C G_C >= 0,   (III) G + 2B G_B - 2C G_C - 4BC G_BC >= 0,
 G = 3 + (B+5)/C + 8(C-B)/(p+q)^2,  p = sqrt(C+5), q = sqrt(C+4B+5),  0 < B <= C.
Rational parametrisation: C = p^2 - 5, B = (q^2 - p^2)/4, region sqrt5 < p < q <= sqrt(5p^2-20).
Derivatives: d/dB = (2/q) d/dq ; d/dC = (1/(2p)) d/dp + (1/(2q)) d/dq."""
import sympy as sp
p, q = sp.symbols('p q', positive=True)
C = p**2 - 5
B = (q**2 - p**2) / 4
G = 3 + (B + 5) / C + 8 * (C - B) / (p + q)**2
dB = lambda f: sp.simplify(2 / q * sp.diff(f, q))
dC = lambda f: sp.simplify(sp.diff(f, p) / (2 * p) + sp.diff(f, q) / (2 * q))
GB, GC = dB(G), dC(G)
GBC = dC(GB)
I1 = sp.together(G + 2 * B * GB)
I2 = sp.together(G - 2 * C * GC)
I3 = sp.together(G + 2 * B * GB - 2 * C * GC - 4 * B * C * GBC)
for name, expr in [("I", I1), ("II", I2), ("III", I3)]:
    num, den = sp.fraction(sp.factor(expr))
    print(name, ": denominator =", sp.factor(den))
    print("    numerator degree:", sp.Poly(sp.expand(num), p, q).total_degree(), " #terms", len(sp.Poly(sp.expand(num), p, q).terms()))
    globals()["num_" + name] = sp.expand(num); globals()["den_" + name] = den
import pickle
pickle.dump({"I": (num_I, den_I), "II": (num_II, den_II), "III": (num_III, den_III)}, open("uc33_conditions.pkl", "wb"))
# numeric sanity on the region
import random
random.seed(1)
bad = {k: 0 for k in ("I", "II", "III")}
for _ in range(20000):
    pv = sp.sqrt(5) + 10 ** random.uniform(-4, 3)
    pv = float(pv)
    qmax = (5 * pv * pv - 20) ** 0.5
    qv = pv + (qmax - pv) * random.random()
    for k, (nm, dn) in {"I": (num_I, den_I), "II": (num_II, den_II), "III": (num_III, den_III)}.items():
        val = float(nm.subs({p: pv, q: qv})) / float(dn.subs({p: pv, q: qv}))
        if val < 0: bad[k] += 1
print("numeric violations on region:", bad)
