"""Core tools for the m = 4 diagonal-share certificate of Conjecture F at (n, 4).

Notation.  A = sum_k alpha_k Q_k (distinct eigenvalues), W_k = B^{1/2} Q_k B^{1/2}.
    p_{n,4} - Tr((A^{n/4} B)^4) = Re sum_{w in [r]^4} T(w) K_n(alpha_w),  T(w) = Tr(W_w1 W_w2 W_w3 W_w4),
    K_n(x) = h_n(x1..x4)/C(n+3,3) - (x1 x2 x3 x4)^{n/4}.
A "diagonal" of a cyclic word (i,j,k,l) is D = {i,k} or E = {j,l}.  S^{D}_{cd} = Tr(W_a W_c W_b W_d) (D = {a,b}) is
Hermitian PSD.  Real symmetric G^D (r x r) with
    G^D[E] + G^E[D] = 2 K(D u E)   for every unordered pair {D, E} of unordered pairs (D = E allowed),
and every G^D PSD give  p - Tr(...) = sum_{ordered (a,b)} <S^{ab}, G^{ab}> >= 0.
"""
import itertools
from math import comb

import numpy as np


def hn_vec(n, X):
    """complete homogeneous symmetric polynomial h_n of the rows of X (shape (N, k)), vectorised."""
    X = np.asarray(X, dtype=float)
    N, k = X.shape
    H = np.zeros((N, n + 1))
    H[:, 0] = 1.0
    # first variable
    for j in range(1, n + 1):
        H[:, j] = H[:, j - 1] * X[:, 0]
    for v in range(1, k):
        for j in range(1, n + 1):
            H[:, j] = H[:, j] + X[:, v] * H[:, j - 1]
    return H[:, n]


def K_vec(n, X):
    X = np.asarray(X, dtype=float)
    return hn_vec(n, X) / comb(n + 3, 3) - np.prod(X, axis=1) ** (n / 4)


def K1(n, x):
    return float(K_vec(n, np.array([x], dtype=float))[0])


def pairs_of(r):
    return [(a, b) for a in range(r) for b in range(a, r)]


def class_list(r):
    """all unordered pairs {D, E} of pairs (D <= E in list order)."""
    P = pairs_of(r)
    return [(P[i], P[j]) for i in range(len(P)) for j in range(i, len(P))]


def Ktable(n, alpha):
    """K(D u E) for all classes, as dict keyed by (D, E)."""
    r = len(alpha)
    cl = class_list(r)
    X = np.array([[alpha[D[0]], alpha[D[1]], alpha[E[0]], alpha[E[1]]] for D, E in cl])
    vals = K_vec(n, X)
    return {c: v for c, v in zip(cl, vals)}


def assemble(r, share):
    """share(D, E) -> value of G^D[E].  Returns dict D -> r x r matrix."""
    P = pairs_of(r)
    G = {D: np.zeros((r, r)) for D in P}
    for D in P:
        for c in range(r):
            for d in range(c, r):
                v = share(D, (c, d))
                G[D][c, d] = v
                G[D][d, c] = v
    return G


def check_identity(n, alpha, G, tol=1e-9):
    r = len(alpha)
    Kt = Ktable(n, alpha)
    worst = 0.0
    for (D, E), k in Kt.items():
        lhs = G[D][E[0], E[1]] + G[E][D[0], D[1]]
        worst = max(worst, abs(lhs - 2 * k) / max(1e-300, abs(k) + 1e-300))
    return worst


def min_rel_eig(G):
    out = {}
    for D, M in G.items():
        ev = np.linalg.eigvalsh((M + M.T) / 2)
        sc = max(np.abs(M).max(), 1e-300)
        out[D] = ev.min() / sc
    return out


# ---------------- direct matrix check of the reduction ----------------

def random_psd(d, rng, cplx=True):
    Z = rng.standard_normal((d, d)) + (1j * rng.standard_normal((d, d)) if cplx else 0)
    return Z @ Z.conj().T


def word_average(n, m, A, B):
    """p_{n,m}(A,B): average of Tr over all words with n letters A and m letters B (via compositions)."""
    # cyclic expansion: average over weak compositions c of n into m parts of Tr(B A^c1 B A^c2 ... B A^cm)
    w, V = np.linalg.eigh(A)
    tot = 0.0
    cnt = 0
    pw = {}
    for c in itertools.product(range(n + 1), repeat=m - 1):
        s = sum(c)
        if s > n:
            continue
        cc = list(c) + [n - s]
        M = np.eye(A.shape[0], dtype=complex)
        for ci in cc:
            if ci not in pw:
                pw[ci] = (V * w ** ci) @ V.conj().T
            M = M @ B @ pw[ci]
        tot += np.trace(M)
        cnt += 1
    assert cnt == comb(n + m - 1, m - 1)
    return (tot / cnt).real


def F_rhs(n, m, A, B):
    w, V = np.linalg.eigh(A)
    An = (V * w ** (n / m)) @ V.conj().T
    M = np.linalg.matrix_power(An @ B, m)
    return np.trace(M).real


def certificate_value(n, A, B, G):
    """sum over ordered pairs (a,b) of <S^{ab}, G^{ab}> with S^{ab}_{cd} = Tr(W_a W_c W_b W_d)."""
    w, V = np.linalg.eigh(A)
    # group eigenvalues (assume distinct here)
    r = len(w)
    wB, VB = np.linalg.eigh(B)
    Bh = (VB * np.sqrt(np.maximum(wB, 0))) @ VB.conj().T
    Wl = [Bh @ np.outer(V[:, k], V[:, k].conj()) @ Bh for k in range(r)]
    tot = 0.0
    for a in range(r):
        for b in range(r):
            D = (min(a, b), max(a, b))
            S = np.array([[np.trace(Wl[a] @ Wl[c] @ Wl[b] @ Wl[d]) for d in range(r)] for c in range(r)])
            tot += np.sum(S * G[D]).real
    return tot, w
