"""TF-F on the ray through (1, r): omega (moments p_{k+1, r(k+1)}/(N(N+1))) FOSD-dominates omega_F
(moments Tr((A^{1/r} B)^{r(k+1)})/(N(N+1))).  rho* = min int h d omega / int h d omega_F over increasing h, h(0)=0."""
import sys
import numpy as np
from scipy.linalg import expm
from tf_moment_sdp import word_avg, logm_h
from tf_ratio_sdp import rho_star

def fpow(X, p):
    w, V = np.linalg.eigh(X)
    return (V * w ** p) @ V.conj().T

def moments_F(A, B, r, K):
    Ar = fpow(A, 1.0 / (2 * r))
    C = Ar @ B @ Ar
    lam = np.linalg.eigvalsh(C)
    LA, LB = logm_h(A), logm_h(B)
    M, MF, ML = [], [], []
    for k in range(K + 1):
        n, m = k + 1, r * (k + 1); N = n + m
        M.append(word_avg(A, B, n, m) / (N * (N + 1)))
        MF.append(np.sum(lam ** m) / (N * (N + 1)))
        ML.append(np.sum(np.exp(np.linalg.eigvalsh(n * LA + m * LB))) / (N * (N + 1)))
    return np.array(M), np.array(MF), np.array(ML)

if __name__ == '__main__':
    rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 0)
    r = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    K = int(sys.argv[3]) if len(sys.argv) > 3 else 10
    swap = len(sys.argv) > 4 and sys.argv[4] == 'swap'
    cases = []
    for d in (3, 4):
        for eps in (0.3, 0.1, 0.03):
            a = np.exp(rng.normal(size=d)); b = np.exp(rng.normal(size=d))
            H = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d)); H = (H + H.conj().T) / 2
            U = expm(1j * eps * H)
            cases.append((f"near-comm d={d} eps={eps}", np.diag(a).astype(complex), U @ np.diag(b) @ U.conj().T))
    for x, dl in [(0.3, 1e-2), (0.1, 1e-2), (0.1, 1e-3)]:
        A = np.array([[1 + dl, 0, 0], [0, x + dl, -x], [0, -x, x + dl]], dtype=complex)
        B = np.array([[x + dl, -x, 0], [-x, x + dl, 0], [0, 0, 1 + dl]], dtype=complex)
        cases.append((f"Cha-Lee x={x} delta={dl}", A, B))
    for t in range(8):
        d = [3, 3, 4, 4, 5, 5, 6, 6][t]; sp = [1, 2, 1, 2, 1, 2, 1, 2][t]
        X = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d)); Q, _ = np.linalg.qr(X)
        A = (Q * np.exp(sp * rng.normal(size=d))) @ Q.conj().T
        X = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d)); Q, _ = np.linalg.qr(X)
        B = (Q * np.exp(sp * rng.normal(size=d))) @ Q.conj().T
        cases.append((f"random d={d} sp={sp}", A, B))
    for label, A, B in cases:
        if swap:
            A, B = B, A
        M, MF, ML = moments_F(A, B, r, K)
        S = np.linalg.eigvalsh(A)[-1] * np.linalg.eigvalsh(B)[-1] ** r
        rF = rho_star(M, MF, S, K)
        rL = rho_star(M, ML, S, K)
        print(f"{label}{' (swapped)' if swap else ''}: r={r} K={K}: rho*_F = {rF:.6f}, rho*_L = {rL:.6f}; F ratios min {np.min(M/MF):.6f}", flush=True)
