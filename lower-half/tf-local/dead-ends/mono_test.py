"""Is lambda -> p_{n,m}(A_lam, B_lam) monotone, where log A_lam = Z + (1-th) T_lam, log B_lam = Z - th T_lam,
T_lam = T_d + lam (T - T_d), T_d = pinching of T onto the eigenspaces of Z, th = n/(n+m)?
At lam = 0 the pair commutes and p = L = Tr e^{NZ}; along the family Z_theta stays equal to Z."""
import numpy as np
from scipy.linalg import expm, eigh

def word_avg(A, B, n, m):
    d = A.shape[0]
    S = {(0, 0): np.eye(d, dtype=complex)}
    for i in range(n + 1):
        for j in range(m + 1):
            if i == 0 and j == 0: continue
            T = np.zeros((d, d), complex)
            if i > 0: T += A @ S[(i - 1, j)]
            if j > 0: T += B @ S[(i, j - 1)]
            S[(i, j)] = T
    from math import comb
    return np.trace(S[(n, m)]).real / comb(n + m, n)

def herm(d, rng, s=1.0):
    M = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))
    return s * (M + M.conj().T) / 2

rng = np.random.default_rng(0)
lams = np.linspace(0, 2.5, 51)
viol = 0; tests = 0; worst = 0
for trial in range(300):
    d = rng.choice([2, 3, 4])
    Z = herm(d, rng, rng.choice([0.3, 1.0, 2.0]))
    T = herm(d, rng, rng.choice([0.3, 1.0, 2.0]))
    z, U = eigh(Z)
    Tz = U.conj().T @ T @ U
    Td = U @ np.diag(np.diag(Tz)) @ U.conj().T
    n, m = [(1, 1), (2, 1), (1, 2), (2, 2), (3, 2), (2, 3), (3, 3), (4, 2), (3, 4)][trial % 9]
    th = n / (n + m)
    vals = []
    for lam in lams:
        Tl = Td + lam * (T - Td)
        A, B = expm(Z + (1 - th) * Tl), expm(Z - th * Tl)
        vals.append(word_avg(A, B, n, m))
    vals = np.array(vals)
    L = np.trace(expm((n + m) * Z)).real
    dv = np.diff(vals)
    tests += 1
    rel = dv.min() / max(abs(vals - L).max(), 1e-300)
    if dv.min() < -1e-10 * abs(vals).max():
        viol += 1
        worst = min(worst, rel)
        if viol <= 6:
            k = int(np.argmin(dv))
            print(f"non-monotone: d={d} (n,m)=({n},{m}) at lam~{lams[k]:.2f}; p-L along lam:",
                  np.array2string((vals - L)[max(0, k - 3):k + 4], precision=4))
print(f"tests {tests}, non-monotone {viol}, worst relative drop {worst:.3g}")
