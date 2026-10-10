"""Sharper exact-moment test of TF on the ray through (1, r):
   rho* = min { int h d omega : int h d omega_kappa = 1, h(0) = 0, h' >= 0 on [0,1] (scaled), deg h <= K }.
   TF on the ray  =>  rho* >= 1 for every K.  rho* < 1 is a violation (h is the certificate)."""
import sys
import numpy as np
import cvxpy as cp
from scipy.linalg import expm
from tf_moment_sdp import moments

def increasing_poly_cone(K):
    c = cp.Variable(K + 1)
    deg = K - 1
    cons = [c[0] == 0]
    coeffs = [k * c[k] for k in range(1, K + 1)]
    if deg % 2 == 0:
        q = deg // 2
        G0 = cp.Variable((q + 1, q + 1), PSD=True)
        G1 = cp.Variable((q, q), PSD=True) if q >= 1 else None
        for j in range(deg + 1):
            e = sum(G0[a, j - a] for a in range(max(0, j - q), min(q, j) + 1))
            if G1 is not None and j >= 1:
                e = e + sum(G1[a, j - 1 - a] for a in range(max(0, j - 1 - (q - 1)), min(q - 1, j - 1) + 1))
            if G1 is not None and j >= 2:
                e = e - sum(G1[a, j - 2 - a] for a in range(max(0, j - 2 - (q - 1)), min(q - 1, j - 2) + 1))
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
    return c, cons

def rho_star(M, Mk, S, K):
    sc = np.array([S ** k for k in range(K + 1)])
    m, mk = M / sc, Mk / sc
    m, mk = m / mk[0], mk / mk[0]      # normalize by reference mass
    c, cons = increasing_poly_cone(K)
    cons.append(mk @ c == 1)
    prob = cp.Problem(cp.Minimize(m @ c), cons)
    prob.solve(solver=cp.CLARABEL)
    return prob.value

if __name__ == '__main__':
    rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 0)
    r = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    Ks = [int(x) for x in (sys.argv[3] if len(sys.argv) > 3 else "6,10").split(',')]
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
    Kmax = max(Ks)
    for label, A, B in cases:
        M, Mk = moments(A, B, r, Kmax)
        S = np.linalg.eigvalsh(A)[-1] * np.linalg.eigvalsh(B)[-1] ** r
        vals = [rho_star(M[:K + 1], Mk[:K + 1], S, K) for K in Ks]
        print(f"{label}: r={r} rho* for K={Ks}: " + ", ".join(f"{v:.6f}" for v in vals) + f"   (LH ratios min {np.min(M/Mk):.6f})", flush=True)
