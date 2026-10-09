"""Independent end-to-end check of an exact polynomial rule (JSON from exact_rule.py) against direct matrix
computations: for random positive definite A, B (complex), with A's spectrum alpha:
  (i)   share identity G^D[E] + G^E[D] = 2 K_n(D u E) for all classes,
  (ii)  every G^D is PSD,
  (iii) sum_{ordered (a,b)} <S^{ab}, G^{ab}> equals p_{n,4}(A,B) - Tr((A^{n/4}B)^4).
High precision (mpmath, 50 digits) for the rule and K_n; the word average is computed directly from A and B.
Usage: python check_rule.py rule.json trials [maxdim]"""
import itertools
import json
import sys
from fractions import Fraction
from math import comb

import mpmath as mp
import numpy as np

mp.mp.dps = 50
d = json.load(open(sys.argv[1]))
trials = int(sys.argv[2])
maxdim = int(sys.argv[3]) if len(sys.argv) > 3 else 5
n, qd = d["n"], d["qd"]
N = n * qd
z = [Fraction(x) for x in d["z"]]
var = [(tuple(p), tuple(q)) for p, q in d["var"]]
vidx = {k: t for t, k in enumerate(var)}
live = set(d["exponents_units"])
Cn3 = comb(n + 3, 3)


def kappa(p, q):
    a, b = p
    i, j = q
    v = Fraction(0)
    if all(t % qd == 0 and t >= 0 for t in (a, b, i, j)):
        v += Fraction(1, Cn3)
    if 4 * a == N and a == b == i == j:
        v -= 1
    return v


def gamma(p, q):
    if p == q:
        return kappa(p, q)
    if (p, q) in vidx:
        return z[vidx[(p, q)]]
    if (q, p) in vidx:
        return 2 * kappa(p, q) - z[vidx[(q, p)]]
    # fixed by deadness: q dead as kernel index -> 0 ; p dead -> 2 kappa
    if q[1] not in live:
        return Fraction(0)
    if p[1] not in live:
        return 2 * kappa(p, q)
    raise KeyError((p, q))


# precompute monomial table
terms = []
for a in range(N + 1):
    for b in range(N + 1 - a):
        for i in range(N + 1 - a - b):
            j = N - a - b - i
            g = gamma((min(a, b), max(a, b)), (min(i, j), max(i, j)))
            if g != 0:
                terms.append((a, b, i, j, mp.mpf(g.numerator) / g.denominator))
print(f"n={n} qd={qd}: {len(terms)} nonzero ordered monomials in the rule", flush=True)


def k_rule(x, y, e, f):
    X = [mp.power(x, mp.mpf(t) / qd) for t in range(N + 1)]
    Y = [mp.power(y, mp.mpf(t) / qd) for t in range(N + 1)]
    Ee = [mp.power(e, mp.mpf(t) / qd) for t in range(N + 1)]
    F = [mp.power(f, mp.mpf(t) / qd) for t in range(N + 1)]
    return mp.fsum(g * X[a] * Y[b] * Ee[i] * F[j] for a, b, i, j, g in terms)


def K_n(xs):
    # h_n via recursion
    H = [mp.mpf(1)] + [mp.mpf(0)] * n
    for v in xs:
        for t in range(1, n + 1):
            H[t] = H[t] + v * H[t - 1]
    return H[n] / Cn3 - mp.power(xs[0] * xs[1] * xs[2] * xs[3], mp.mpf(n) / 4)


rng = np.random.default_rng(12345)
worst_eig, worst_id, worst_cert = mp.inf, 0, 0
for tr in range(trials):
    dim = int(rng.integers(2, maxdim + 1))
    spread = float(rng.choice([0.2, 1.0, 3.0, 6.0]))
    alpha = np.sort(np.exp(rng.uniform(-spread, spread, size=dim)))
    U, _ = np.linalg.qr(rng.standard_normal((dim, dim)) + 1j * rng.standard_normal((dim, dim)))
    Z = rng.standard_normal((dim, dim)) + 1j * rng.standard_normal((dim, dim))
    B = Z @ Z.conj().T + 0.1 * np.eye(dim)
    A = (U * alpha) @ U.conj().T
    al = [mp.mpf(float(a)) for a in alpha]
    r = dim
    G = {}
    for a in range(r):
        for b in range(a, r):
            M = mp.matrix(r, r)
            for c in range(r):
                for dd in range(c, r):
                    v = k_rule(al[a], al[b], al[c], al[dd])
                    M[c, dd] = v
                    M[dd, c] = v
            G[(a, b)] = M
    # (i) identity
    for a in range(r):
        for b in range(a, r):
            for c in range(r):
                for dd in range(c, r):
                    lhs = G[(a, b)][c, dd] + G[(c, dd)][a, b]
                    rhs = 2 * K_n([al[a], al[b], al[c], al[dd]])
                    sc = max(abs(rhs), mp.mpf(10) ** -40 * max(al) ** n)
                    worst_id = max(worst_id, abs(lhs - rhs) / (max(al) ** n))
    # (ii) PSD
    for D_, M in G.items():
        ev = mp.eigsy(M)[0]
        mx = max(abs(M[i, j]) for i in range(r) for j in range(r))
        worst_eig = min(worst_eig, min(ev) / mx)
    # (iii) certificate value vs direct gap (double precision matrices)
    w, V = np.linalg.eigh(A)
    wB, VB = np.linalg.eigh(B)
    Bh = (VB * np.sqrt(wB)) @ VB.conj().T
    Wl = [Bh @ np.outer(V[:, k], V[:, k].conj()) @ Bh for k in range(r)]
    cert = 0.0
    for a in range(r):
        for b in range(r):
            Dk = (min(a, b), max(a, b))
            Gn = np.array([[float(G[Dk][c, dd]) for dd in range(r)] for c in range(r)])
            Sab = np.array([[np.trace(Wl[a] @ Wl[c] @ Wl[b] @ Wl[dd]) for dd in range(r)] for c in range(r)])
            cert += np.sum(Sab * Gn).real
    # direct gap
    tot = 0.0
    cnt = 0
    pw = {}
    for c in itertools.product(range(n + 1), repeat=3):
        if sum(c) > n:
            continue
        cc = list(c) + [n - sum(c)]
        M = np.eye(dim, dtype=complex)
        for ci in cc:
            if ci not in pw:
                pw[ci] = (V * w ** ci) @ V.conj().T
            M = M @ B @ pw[ci]
        tot += np.trace(M).real
        cnt += 1
    pavg = tot / cnt
    An = (V * w ** (n / 4)) @ V.conj().T
    rhs = np.trace(np.linalg.matrix_power(An @ B, 4)).real
    gap = pavg - rhs
    rel = abs(cert - gap) / max(abs(gap), 1e-300)
    worst_cert = max(worst_cert, rel if abs(gap) > 1e-9 * abs(pavg) else 0)
    print(f"trial {tr}: d={dim} spread={spread} gap={gap:.6e} cert={cert:.6e} rel.diff={rel:.1e}", flush=True)
print(f"SUMMARY n={n}: worst min eig/max|G| = {mp.nstr(worst_eig, 5)}, worst identity err (rel. to max alpha^n) = "
      f"{mp.nstr(worst_id, 5)}, worst certificate rel. diff = {worst_cert:.2e}")
