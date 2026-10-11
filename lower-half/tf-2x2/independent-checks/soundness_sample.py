"""Independent soundness check of the TF(2x2) certificates: sample random certified leaves of the final L=40 runs,
random points inside them (incl. thin layers near w = +-1), and evaluate inequality (C) directly from 2x2 matrices
(mpmath, 80 digits; no hyperbolic closed forms): Tr(A B^r) - e^{N0 zeta_2} >= (G - e^{-zeta_2})^{-N0}."""
import sys, random
import mpmath as mp
mp.mp.dps = 80
sx = mp.matrix([[0, 1], [1, 0]]); sy = mp.matrix([[0, -1j], [1j, 0]]); sz = mp.matrix([[1, 0], [0, -1]])
def fun(M, f):
    ev, U = mp.eighe((M + M.H) / 2)
    return U * mp.diag([f(ev[i]) for i in range(M.rows)]) * U.H
def tr(M): return mp.re(M[0, 0] + M[1, 1])
def margin(th, a, c, w):
    th, a, c, w = mp.mpf(th), mp.mpf(a), mp.mpf(c), mp.mpf(w)
    N0 = 1 / th; r = (1 - th) / th; b = th * c / (1 - th)
    xh = sz; yh = w * sz + mp.sqrt(max(0, 1 - w * w)) * sx
    LA, LB = a * xh, b * yh
    A, B = fun(LA, mp.exp), fun(LB, mp.exp)
    Z = th * LA + (1 - th) * LB
    z2 = max(mp.eighe((Z + Z.H) / 2)[0])
    P = tr(A * fun(LB * r, mp.exp))
    Ai, Bi = fun(-LA, mp.exp), fun(-LB, mp.exp)
    Ah, Amh = fun(-LA / 2, mp.exp), fun(LA / 2, mp.exp)
    G = tr(Ah * fun(Amh * Bi * Amh, lambda x: x ** (1 - th)) * Ah)
    lhs = P - mp.exp(N0 * z2); rhs = (G - mp.exp(-z2)) ** (-N0)
    return lhs - rhs, lhs, rhs
files = ['../runs/final_L40_lo.txt', '../runs/final_L40_hi.txt']
leaves = []
for f in files:
    for line in open(f):
        parts = line.split()
        if len(parts) >= 9 and parts[0] in ('W', 'P', 'I', 'D', 'F'):
            leaves.append(parts)
rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
print('leaves loaded', len(leaves), 'format example', leaves[0][:9])
bad = 0; worst = None; n = 0
for _ in range(int(sys.argv[2]) if len(sys.argv) > 2 else 150):
    L = rng.choice(leaves)
    vals = [mp.mpf(mp.mpq(*map(int, v.split('/')))) if '/' in v else mp.mpf(v) for v in L[1:9]]
    th0, th1, a0, a1, c0, c1, w0, w1 = vals
    for k in range(2):
        th = th0 + (th1 - th0) * mp.mpf(rng.random()); a = a0 + (a1 - a0) * mp.mpf(rng.random())
        c = c0 + (c1 - c0) * mp.mpf(rng.random())
        u = rng.random()
        if rng.random() < 0.3:   # thin layer near an endpoint of the w-range
            w = (w1 - (w1 - w0) * mp.mpf(10) ** (-rng.randint(1, 30))) if rng.random() < 0.5 else (w0 + (w1 - w0) * mp.mpf(10) ** (-rng.randint(1, 30)))
        else:
            w = w0 + (w1 - w0) * mp.mpf(u)
        if th <= 0: continue
        m, lhs, rhs = margin(th, a, c, w)
        n += 1
        scale = abs(lhs) + abs(rhs)
        if m < -mp.mpf(10) ** (-60) * scale:
            bad += 1; print('VIOLATION', L[0], mp.nstr(th, 8), mp.nstr(a, 8), mp.nstr(c, 8), mp.nstr(w, 20), mp.nstr(m, 8))
        rel = m / scale if scale > 0 else 0
        if worst is None or rel < worst[0]: worst = (rel, L[0])
print(f'points {n}, violations {bad}, min relative margin {mp.nstr(worst[0], 6)} (leaf type {worst[1]})')
