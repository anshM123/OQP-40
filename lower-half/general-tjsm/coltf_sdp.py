"""Column-TF(m): the measure sigma*pi_m (moments p_{k+1,m}, k >= 0, on spec A) FOSD-dominates sigma*nu_m (moments L_{k+1,m}).
k = 0 is Golden-Thompson Tr(A B^m) >= Tr exp(log A + m log B).  Column-TF(m) => LH at (n, m) for all n >= 1."""
import sys
import numpy as np
from scipy.linalg import expm
from tf_moment_sdp import logm_h
from tf_ratio_sdp import rho_star
from latmono import word_avgs_all

def col_moments(A, B, m, K):
    p = word_avgs_all(A, B, K + 1 + m)
    LA, LB = logm_h(A), logm_h(B)
    M = np.array([p[(k + 1, m)] for k in range(K + 1)])
    ML = np.array([np.sum(np.exp(np.linalg.eigvalsh((k + 1) * LA + m * LB))) for k in range(K + 1)])
    return M, ML

if __name__ == '__main__':
    rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 0)
    K = int(sys.argv[2]) if len(sys.argv) > 2 else 10
    ms = [int(x) for x in (sys.argv[3] if len(sys.argv) > 3 else "2,3,4,5").split(',')]
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
        cases.append((f"Cha-Lee x={x} delta={dl} swapped", B, A))
    for t in range(8):
        d = [3, 3, 4, 4, 5, 5, 6, 6][t]; sp = [1, 2, 1, 2, 1, 2, 1, 2][t]
        X = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d)); Q, _ = np.linalg.qr(X)
        A = (Q * np.exp(sp * rng.normal(size=d))) @ Q.conj().T
        X = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d)); Q, _ = np.linalg.qr(X)
        B = (Q * np.exp(sp * rng.normal(size=d))) @ Q.conj().T
        cases.append((f"random d={d} sp={sp}", A, B))
    worst = {}
    for label, A, B in cases:
        S = np.linalg.eigvalsh(A)[-1]
        out = []
        for m in ms:
            M, ML = col_moments(A, B, m, K)
            v = rho_star(M, ML, S, K)
            out.append(f"m={m}: {v:.6f}")
            if m not in worst or v < worst[m][0]:
                worst[m] = (v, label)
        print(f"{label}: column rho* " + ", ".join(out), flush=True)
    print("WORST:", worst)
