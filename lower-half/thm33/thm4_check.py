"""Independent numerical check of Theorem 4 ((3,3) in all dimensions) and of its certificate:
(a) for random A (r distinct eigenvalues with multiplicities) and B: Phi_B(kappa) == 3 sum_l <R^(l), G^(l)> with
    the universal apex matrices, and every G^(l) is PSD;  (b) p_{3,3}(A,B) >= tr((AB)^3) for random d = 4..24."""
import itertools
import numpy as np
from math import comb
rng = np.random.default_rng(2026)
def kap(x, y, z): return (x + y + z) * (x * x + y * y + z * z) - 9 * x * y * z
def rand_unitary(d):
    Q, R = np.linalg.qr(rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))); return Q * (np.diag(R) / abs(np.diag(R)))
def rpd(d, s):
    X = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d)); H = (X + X.conj().T) / 2
    w, V = np.linalg.eigh(H * s / np.linalg.norm(H, 2)); return (V * np.exp(w)) @ V.conj().T
worst_id, worst_psd = 0.0, np.inf
for trial in range(300):
    r = int(rng.integers(3, 9)); mult = rng.integers(1, 3, size=r); d = int(mult.sum())
    al = np.sort(np.exp(rng.uniform(-3, 3, size=r)))
    U = rand_unitary(d); diag = np.repeat(al, mult); A = (U * diag) @ U.conj().T
    B = rpd(d, rng.choice([0.5, 2, 4]))
    w, V = np.linalg.eigh(B); Bh = (V * np.sqrt(w)) @ V.conj().T
    Q = []; start = 0
    for k in range(r):
        cols = U[:, start:start + mult[k]]; Q.append(cols @ cols.conj().T); start += mult[k]
    W = [Bh @ Qk @ Bh for Qk in Q]
    # Phi_B(kappa) directly
    Phi = 0.0
    for wd in itertools.product(range(r), repeat=3):
        Phi += np.trace(W[wd[0]] @ W[wd[1]] @ W[wd[2]]).real * kap(al[wd[0]], al[wd[1]], al[wd[2]])
    # certificate
    tot = 0.0
    for l in range(r):
        idx = [a for a in range(r) if a != l]
        G = np.zeros((r - 1, r - 1)); R = np.zeros((r - 1, r - 1))
        for i, a in enumerate(idx):
            for j, b in enumerate(idx):
                R[i, j] = np.trace(W[l] @ W[a] @ W[b]).real
                if i == j:
                    G[i, i] = kap(al[l], al[a], al[a]); continue
                x, y = sorted((al[a], al[b]))
                if al[l] > y:      # l is the max apex: rank one
                    G[i, j] = (al[l] - x) * (al[l] - y) * np.sqrt((al[l] + 4 * x) * (al[l] + 4 * y))
                elif al[l] < x:    # l is the min apex: the rest
                    G[i, j] = kap(al[l], x, y) - (y - al[l]) * (y - x) * np.sqrt((y + 4 * al[l]) * (y + 4 * x))
                else:              # l is the middle: 0
                    G[i, j] = 0.0
        tot += np.sum(R * G)
        dg = 1 / np.sqrt(np.diag(G)); worst_psd = min(worst_psd, np.linalg.eigvalsh(G * np.outer(dg, dg))[0])
    worst_id = max(worst_id, abs(Phi - 3 * tot) / max(abs(Phi), 1e-300))
print(f"(a) identity Phi = 3 sum <R,G>: max rel error {worst_id:.2e};  min normalised eigenvalue of apex matrices {worst_psd:.3e}")
def p33(A, B):
    d = A.shape[0]; coeffs = [np.eye(d, dtype=complex)] + [np.zeros((d, d), dtype=complex)] * 3
    for _ in range(6):
        new = [coeffs[0] @ A] + [coeffs[j] @ A + coeffs[j - 1] @ B for j in range(1, 4)]
        coeffs = new
    return np.trace(coeffs[3]).real / 20
worst = np.inf
for trial in range(2000):
    d = int(rng.integers(4, 25)); A, B = rpd(d, rng.choice([0.3, 1, 3, 6])), rpd(d, rng.choice([0.3, 1, 3, 6]))
    worst = min(worst, p33(A, B) / np.trace(np.linalg.matrix_power(A @ B, 3)).real)
print(f"(b) min p_33 / tr((AB)^3) over 2000 random pairs, d = 4..24: {worst:.6f}")
