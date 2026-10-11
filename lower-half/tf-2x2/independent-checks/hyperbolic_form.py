"""Check the hyperbolic-triangle form of inequality (C) for 2x2 pairs (det A = det B = 1):
  (C)  <=>  (2 cosh D1 - e^{E1})^theta * (2 cosh D2 - e^{-theta E1}) >= 1,
where, in the hyperbolic plane (curvature -1) with base point O = I and unit directions x, y (x.y = w):
  P1 = A^{-1} = exp_O(-a x), R1 = B^{-1} = exp_O(-b y), Q1 = B^r = exp_O(c y), c = r b,
  D1 = d(P1, Q1), E1 = |a x + c y| (tangent-space distance at O), D2 = d(O, M),
  M = point of the geodesic P1 R1 at fraction theta from R1 (= A^{-1} #_{1-theta} B^{-1}).
D1, D2 are computed here from matrices (traces of det-1 positive matrices), E1 from vectors."""
import random
import mpmath as mp
mp.mp.dps = 60
sx = mp.matrix([[0, 1], [1, 0]]); sz = mp.matrix([[1, 0], [0, -1]])
def fun(M, f):
    ev, U = mp.eighe((M + M.H) / 2)
    return U * mp.diag([f(ev[i]) for i in range(M.rows)]) * U.H
def tr(M): return mp.re(M[0, 0] + M[1, 1])
rng = random.Random(5)
worst = 0
for trial in range(400):
    th = mp.mpf(rng.uniform(0.02, 0.5)); a = mp.mpf(rng.uniform(0, 6)); c = mp.mpf(rng.uniform(0, 6))
    w = mp.mpf(rng.uniform(-1, 1)); r = (1 - th) / th; b = c / r
    xh = sz; yh = w * sz + mp.sqrt(1 - w * w) * sx
    A, B = fun(a * xh, mp.exp), fun(b * yh, mp.exp)
    Z = th * a * xh + (1 - th) * b * yh
    z2 = max(mp.eighe(Z)[0]); N0 = 1 / th
    P = tr(A * fun(r * b * yh, mp.exp))
    Ai, Bi = fun(-a * xh, mp.exp), fun(-b * yh, mp.exp)
    Ah, Amh = fun(-a * xh / 2, mp.exp), fun(a * xh / 2, mp.exp)
    G = tr(Ah * fun(Amh * Bi * Amh, lambda x: x ** (1 - th)) * Ah)
    margC = (P - mp.exp(N0 * z2)) - (G - mp.exp(-z2)) ** (-N0)          # (C) as stated (lhs - rhs)
    D1 = mp.acosh(P / 2); D2 = mp.acosh(G / 2); E1 = mp.sqrt(a * a + c * c + 2 * a * c * w)
    hyp = (2 * mp.cosh(D1) - mp.exp(E1)) ** th * (2 * mp.cosh(D2) - mp.exp(-th * E1)) - 1
    # same sign and the exact relation: (C) <=> hyp >= 0; check via the identity lhs/rhs = (1+hyp)^{N0}
    lhs = P - mp.exp(N0 * z2); rhs = (G - mp.exp(-z2)) ** (-N0)
    rel = abs(lhs / rhs - (1 + hyp) ** N0) / ((1 + hyp) ** N0)
    worst = max(worst, rel)
    assert (margC >= 0) == (hyp >= 0) or abs(hyp) < mp.mpf(10) ** -40
    # also check E1*theta = |theta a x + (1-theta) b y| = largest eigenvalue of Z, and D2 <= theta E1 <= ..., D1 >= E1
    assert abs(th * E1 - z2) < mp.mpf(10) ** -40 and D1 >= E1 - mp.mpf(10) ** -40 and D2 <= th * E1 + mp.mpf(10) ** -40
print('400 random (theta,a,c,w): (C) <=> hyperbolic form; max rel. deviation of lhs/rhs = (1+hyp)^N0:', mp.nstr(worst, 5))
