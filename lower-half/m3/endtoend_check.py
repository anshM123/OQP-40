"""End-to-end numerical check of Theorem M3 (min-apex certificate) for general n, m = 3, in 40-digit arithmetic.
(a) random A (r distinct eigenvalues, multiplicities 1-2) and random complex PD B:
    p_{n,3}(A,B) - tr((A^{n/3} B)^3)  ==  Phi_B(K_n)  ==  3 sum_l <R^(l), G^(l)>,
    with R^(l)_ab = Re tr(W_l W_a W_b), W_l = B^{1/2} Q_l B^{1/2}, and G^(l) the min-apex certificate:
    below block u_l(a) u_l(b), u_l(a) = sqrt(K(l,a,a)); above block E_l(b,b') = K(l,b,b') - sqrt(K(b'',l,l)K(b'',b,b))
    (b'' = max(b,b'), b, b' > l), diagonal K(l,b,b); cross block 0.  Every G^(l) must be PSD.
(b) min of p_{n,3}(A,B) / tr((A^{n/3}B)^3) over random pairs.
Usage: python endtoend_check.py n [trials]"""
import sys, itertools
from math import comb
import mpmath as mp
import numpy as np

mp.mp.dps = 40
n = int(sys.argv[1]); trials = int(sys.argv[2]) if len(sys.argv) > 2 else 20
rng = np.random.default_rng(1000 + n)
Cn = comb(n + 2, 2)
def K(x, y, z):
    e = [mp.mpf(1)] + [mp.mpf(0)] * n
    for xi in (x, y, z):
        for k in range(1, n + 1):
            e[k] += xi * e[k - 1]
    return e[n] / Cn - (x * y * z) ** (mp.mpf(n) / 3)
def herm_sqrt(M):
    w, V = mp.eighe(M)
    D = mp.diag([mp.sqrt(max(x, 0)) for x in w])
    return V * D * V.H
def herm_pow(M, p):
    w, V = mp.eighe(M)
    D = mp.diag([x ** p for x in w])
    return V * D * V.H
def rand_unitary(d):
    Z = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))
    M = mp.matrix([[mp.mpc(Z[i, j].real, Z[i, j].imag) for j in range(d)] for i in range(d)])
    cols = []
    for j in range(d):          # Gram-Schmidt in working precision (exactly unitary to 40 digits)
        vcol = M[:, j]
        for c in cols:
            vcol = vcol - c * (c.H * vcol)[0, 0]
        vcol = vcol / mp.sqrt(mp.re((vcol.H * vcol)[0, 0]))
        cols.append(vcol)
    Uq = mp.matrix(d, d)
    for j, c in enumerate(cols):
        for i in range(d): Uq[i, j] = c[i]
    return Uq
def rand_pd(d, scale):
    Z = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))
    H = (Z + Z.conj().T) / 2
    w = rng.uniform(-scale, scale, size=d)
    V = rand_unitary(d)
    return V * mp.diag([mp.e ** mp.mpf(float(x)) for x in w]) * V.H
def tr(M):
    return sum(M[i, i] for i in range(M.rows))
def p_n3(A, B):
    d = A.rows
    c = {(0, 0): mp.eye(d)}
    for j in range(n + 1):
        for k in range(4):
            if (j, k) == (0, 0): continue
            acc = mp.zeros(d, d)
            if j > 0: acc += c[(j - 1, k)] * A
            if k > 0: acc += c[(j, k - 1)] * B
            c[(j, k)] = acc
    return mp.re(tr(c[(n, 3)])) / comb(n + 3, 3)
worst_id = mp.mpf(0); worst_eig = mp.inf; worst_ratio = mp.inf
for trial in range(trials):
    r = int(rng.integers(3, 7)); mult = [int(x) for x in rng.integers(1, 3, size=r)]; d = sum(mult)
    al = sorted([mp.e ** mp.mpf(float(x)) for x in rng.uniform(-2, 2, size=r)])
    U = rand_unitary(d)
    diag = []
    for a, m_ in zip(al, mult): diag += [a] * m_
    A = U * mp.diag(diag) * U.H
    B = rand_pd(d, float(rng.choice([0.5, 1.5, 3.0])))
    Bh = herm_sqrt(B)
    Q = []; start = 0
    for m_ in mult:
        cols = U[:, start:start + m_]; Q.append(cols * cols.H); start += m_
    W = [Bh * Qk * Bh for Qk in Q]
    T = {}
    for w in itertools.product(range(r), repeat=3):
        T[w] = tr(W[w[0]] * W[w[1]] * W[w[2]])
    Phi = mp.re(sum(T[w] * K(al[w[0]], al[w[1]], al[w[2]]) for w in T))
    lhs = p_n3(A, B) - mp.re(tr((herm_pow(A, mp.mpf(n) / 3) * B) ** 3))
    tot = mp.mpf(0)
    for l in range(r):
        idx = [a for a in range(r) if a != l]
        G = mp.zeros(r - 1, r - 1)
        for i, a in enumerate(idx):
            for j, b in enumerate(idx):
                if i == j:
                    G[i, j] = K(al[l], al[a], al[a]); continue
                lo, hi = (a, b) if al[a] < al[b] else (b, a)
                if al[l] > al[hi]:      # l is the max apex: rank one
                    G[i, j] = mp.sqrt(K(al[l], al[a], al[a]) * K(al[l], al[b], al[b]))
                elif al[l] < al[lo]:    # l is the min apex: the rest
                    G[i, j] = K(al[l], al[a], al[b]) - mp.sqrt(K(al[hi], al[l], al[l]) * K(al[hi], al[lo], al[lo]))
                else:
                    G[i, j] = 0
        R = mp.matrix(r - 1, r - 1)
        for i, a in enumerate(idx):
            for j, b in enumerate(idx):
                R[i, j] = mp.re(T[(l, a, b)])
        tot += sum(R[i, j] * G[i, j] for i in range(r - 1) for j in range(r - 1))
        dg = [1 / mp.sqrt(G[i, i]) for i in range(r - 1)]
        Gn = mp.matrix(r - 1, r - 1)
        for i in range(r - 1):
            for j in range(r - 1): Gn[i, j] = G[i, j] * dg[i] * dg[j]
        worst_eig = min(worst_eig, min(mp.eigsy(Gn)[0]))
    worst_id = max(worst_id, abs(Phi - lhs) / abs(lhs), abs(3 * tot - Phi) / abs(Phi))
    worst_ratio = min(worst_ratio, p_n3(A, B) / mp.re(tr((herm_pow(A, mp.mpf(n) / 3) * B) ** 3)))
print(f"n = {n}: {trials} random (A,B), r = 3..6, d <= 12: max rel. error of p - frac = Phi_B(K) = 3 sum<R,G>: "
      f"{mp.nstr(worst_id, 3)};  min normalised eigenvalue of all G^(l): {mp.nstr(worst_eig, 3)};  "
      f"min p_n3/tr((A^(n/3)B)^3): {mp.nstr(worst_ratio, 8)}", flush=True)
