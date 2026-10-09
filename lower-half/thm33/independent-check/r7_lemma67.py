"""Referee check, task 1 (d)-(e): Lemma 6 (E_s is a PSD kernel on (s, inf)) and Lemma 7 (interval mixtures), numerically
at 120 digits (50 digits showed 1e-16 cancellation artefacts in kappa - cap for B tiny, C huge), on random /
clustered / widely spread point sets, including the edge cases k = 1, 2 and points close to s.

E_s(b,c) = kappa(s,b,c) - (c-s)(c-b) sqrt((c+4s)(c+4b))  for s < b <= c   (diagonal: kappa(s,b,b) = (b-s)^2 (s+4b)).
Lemma 7 decomposition: with x_i = b_i/s - 1 sorted, F(B,C) = sqrt(B/C) G(B,C),  mu_pq as in the paper, K = sum mu v v^T.
"""
import random
import mpmath as mp

mp.mp.dps = 120
out = []
def say(*a):
    s = ' '.join(str(x) for x in a)
    print(s, flush=True)
    out.append(s)

def kap(x, y, z): return (x + y + z) * (x * x + y * y + z * z) - 9 * x * y * z

def E(s, b, c):
    b, c = min(b, c), max(b, c)
    return kap(s, b, c) - (c - s) * (c - b) * mp.sqrt((c + 4 * s) * (c + 4 * b))

def Gf(B, C):
    p, q = mp.sqrt(C + 5), mp.sqrt(C + 4 * B + 5)
    return 3 + (B + 5) / C + 8 * (C - B) / (p + q)**2

def Ff(B, C): return mp.sqrt(B / C) * Gf(B, C)

random.seed(3)
min_eig = mp.inf; worst_set = None
min_mu = mp.inf; max_recon = mp.mpf(0); max_homog = mp.mpf(0); max_wF = mp.mpf(0)
nsets = 0
for trial in range(400):
    s = mp.mpf(10) ** random.uniform(-6, 6)
    k = random.choice([1, 2, 3, 5, 8, 12, 20, 30])
    mode = trial % 4
    if mode == 0:     # log-uniform spread up to 1e12 above s
        xs = [mp.mpf(10) ** random.uniform(-6, 12) for _ in range(k)]
    elif mode == 1:   # clustered near s
        xs = [mp.mpf(10) ** random.uniform(-12, -6) for _ in range(k)]
    elif mode == 2:   # clustered at a common point
        c0 = mp.mpf(10) ** random.uniform(-3, 3)
        xs = [c0 * (1 + mp.mpf(10) ** random.uniform(-10, -2) * random.random()) for _ in range(k)]
    else:             # moderate
        xs = [mp.mpf(random.uniform(0.01, 10)) for _ in range(k)]
    xs = sorted(set(xs))
    k = len(xs)
    pts = [s * (1 + x) for x in xs]
    M = mp.matrix(k, k)
    for i in range(k):
        for j in range(k):
            M[i, j] = E(s, pts[i], pts[j])
    # homogeneity E_s(b,c) = s^3 E_1(b/s, c/s) and E_1 = w w F
    for i in range(k):
        for j in range(i, k):
            e1 = E(1, 1 + xs[i], 1 + xs[j])
            max_homog = max(max_homog, abs(M[i, j] - s**3 * e1) / abs(M[i, j]) if M[i, j] != 0 else 0)
            wF = xs[i]**mp.mpf(1.5) * xs[j]**mp.mpf(1.5) * Ff(xs[i], xs[j])
            max_wF = max(max_wF, abs(e1 - wF) / abs(e1) if e1 != 0 else 0)
    dg = [mp.sqrt(M[i, i]) for i in range(k)]
    N = mp.matrix(k, k)
    for i in range(k):
        for j in range(k):
            N[i, j] = M[i, j] / (dg[i] * dg[j])
    ev = min(mp.eigsy(N)[0]) if k > 1 else N[0, 0]
    if ev < min_eig:
        min_eig = ev; worst_set = (mode, k)
    # Lemma 7: mu_pq
    def FF(i, j):   # 1-based indices, with the conventions F(x_0, .) = 0, F(., x_{k+1}) = 0
        if i == 0 or j == k + 1: return mp.mpf(0)
        return Ff(xs[i - 1], xs[j - 1])
    mu = {}
    for pp in range(1, k + 1):
        for qq in range(pp, k + 1):
            mu[(pp, qq)] = FF(pp, qq) - FF(pp - 1, qq) - FF(pp, qq + 1) + FF(pp - 1, qq + 1)
            scale = abs(FF(pp, qq)) + 1
            min_mu = min(min_mu, mu[(pp, qq)] / scale)
    for i in range(1, k + 1):
        for j in range(i, k + 1):
            rec = sum(mu[(pp, qq)] for pp in range(1, i + 1) for qq in range(j, k + 1))
            max_recon = max(max_recon, abs(rec - FF(i, j)) / abs(FF(i, j)))
    nsets += 1
say(f'{nsets} point sets (k = 1..30; s = 1e-6..1e6; spreads up to 1e12 s; clusters down to 1e-12 s above s)')
say(f'  homogeneity E_s = s^3 E_1(./s, ./s): max rel err {mp.nstr(max_homog, 3)}')
say(f'  E_1(b,c) = B^1.5 C^1.5 F(B,C): max rel err {mp.nstr(max_wF, 3)}')
say(f'  min normalised eigenvalue of [E_s(b_i,b_j)]: {mp.nstr(min_eig, 5)}  (worst: mode {worst_set[0]}, k = {worst_set[1]})')
say(f'  Lemma 7: min mu_pq / (|F(x_p,x_q)|+1) = {mp.nstr(min_mu, 5)}  (>= 0 expected);  telescoping reconstruction max rel err {mp.nstr(max_recon, 3)}')
open('r7_lemma67.log', 'w').write('\n'.join(out) + '\n')
