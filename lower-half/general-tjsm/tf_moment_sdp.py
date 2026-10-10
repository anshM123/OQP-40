"""Exact-data test of TF on the ray through (1, r) (r = 1: diagonal).
omega has moments M_k = p_{k+1, r(k+1)} / (N_k (N_k+1)), N_k = (1+r)(k+1);  omega_kappa has L in place of p.
TF on this ray  <=>  omega FOSD-dominates omega_kappa (with mass(omega) >= mass(omega_kappa) = GT).
Search: minimize int h d(omega - omega_kappa) over h with h(0) = 0, h' >= 0 on [0, S], h(S) = 1, deg h <= K.
A negative optimum is a violation certificate (h increasing)."""
import sys
import numpy as np
import cvxpy as cp
from math import comb
from scipy.linalg import expm

def word_avg(A, B, n, m):
    d = A.shape[0]
    P = [np.eye(d, dtype=complex)]
    for _ in range(n + m):
        Q = [np.zeros((d, d), dtype=complex) for _ in range(len(P) + 1)]
        for j, C in enumerate(P):
            Q[j] = Q[j] + C @ A
            Q[j + 1] = Q[j + 1] + C @ B
        P = Q
    return np.trace(P[m]).real / comb(n + m, m)

def logm_h(X):
    w, V = np.linalg.eigh(X)
    return (V * np.log(w)) @ V.conj().T

def moments(A, B, r, K):
    LA, LB = logm_h(A), logm_h(B)
    M, Mk = [], []
    for k in range(K + 1):
        n, m = k + 1, r * (k + 1)
        N = n + m
        M.append(word_avg(A, B, n, m) / (N * (N + 1)))
        Mk.append(np.sum(np.exp(np.linalg.eigvalsh(n * LA + m * LB))) / (N * (N + 1)))
    return np.array(M), np.array(Mk)

def fosd_test(M, Mk, S, K):
    # scale s -> s/S: moments m_k = M_k / S^k
    sc = np.array([S ** k for k in range(K + 1)])
    D = (M - Mk) / sc
    c = cp.Variable(K + 1)
    # h(t) = sum c_k t^k on [0,1]; h(0)=0 -> c0 = 0; h(1) = 1; h'(t) = sum k c_k t^{k-1} >= 0 on [0,1]
    deg = K - 1  # degree of h'
    cons = [c[0] == 0, cp.sum(c) == 1]
    # Markov-Lukacs: if deg even = 2q: h' = s0(t) + t(1-t) s1(t), s0 deg 2q, s1 deg 2q-2
    #                if deg odd = 2q+1: h' = t s0(t) + (1-t) s1(t), s0, s1 deg 2q
    coeffs = [k * c[k] for k in range(1, K + 1)]  # coefficient of t^{k-1}
    if deg % 2 == 0:
        q = deg // 2
        G0 = cp.Variable((q + 1, q + 1), PSD=True)
        G1 = cp.Variable((q, q), PSD=True) if q >= 1 else None
        for j in range(deg + 1):
            e = sum(G0[a, j - a] for a in range(max(0, j - q), min(q, j) + 1))
            if G1 is not None:
                # t(1-t) s1: t^{a+b+1} - t^{a+b+2}
                e = e + sum(G1[a, j - 1 - a] for a in range(max(0, j - 1 - (q - 1)), min(q - 1, j - 1) + 1)) if j >= 1 else e
                e = e - sum(G1[a, j - 2 - a] for a in range(max(0, j - 2 - (q - 1)), min(q - 1, j - 2) + 1)) if j >= 2 else e
            cons.append(coeffs[j] == e)
    else:
        q = (deg - 1) // 2
        G0 = cp.Variable((q + 1, q + 1), PSD=True)
        G1 = cp.Variable((q + 1, q + 1), PSD=True)
        for j in range(deg + 1):
            e = 0
            if j >= 1:
                e = e + sum(G0[a, j - 1 - a] for a in range(max(0, j - 1 - q), min(q, j - 1) + 1))
            e = e + sum(G1[a, j - a] for a in range(max(0, j - q), min(q, j) + 1))
            if j >= 1:
                e = e - sum(G1[a, j - 1 - a] for a in range(max(0, j - 1 - q), min(q, j - 1) + 1))
            cons.append(coeffs[j] == e)
    prob = cp.Problem(cp.Minimize(D @ c), cons)
    prob.solve(solver=cp.CLARABEL)
    return prob.value, c.value

if __name__ == '__main__':
    rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 0)
    r = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    K = int(sys.argv[3]) if len(sys.argv) > 3 else 8
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
    for t in range(6):
        d = [3, 3, 4, 4, 5, 5][t]; sp = [1, 2, 1, 2, 1, 2][t]
        X = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d)); Q, _ = np.linalg.qr(X)
        A = (Q * np.exp(sp * rng.normal(size=d))) @ Q.conj().T
        X = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d)); Q, _ = np.linalg.qr(X)
        B = (Q * np.exp(sp * rng.normal(size=d))) @ Q.conj().T
        cases.append((f"random d={d} sp={sp}", A, B))
    for label, A, B in cases:
        M, Mk = moments(A, B, r, K)
        S = np.linalg.eigvalsh(A)[-1] * np.linalg.eigvalsh(B)[-1] ** r
        val, c = fosd_test(M, Mk, S, K)
        gt = (M[0] - Mk[0]) / Mk[0]
        print(f"{label}: r={r} K={K}: min int h d(omega-omega_kappa) = {val: .3e}  (GT rel gap {gt:.2e}; LH rel gaps k<=K min {np.min((M-Mk)/Mk):.2e})", flush=True)
