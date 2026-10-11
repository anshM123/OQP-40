"""Second-order TF at a commuting 2x2 pair.  A = diag(1, a), B = R(eps) diag(1, b) R(eps)^T.
D_k = lim_{eps->0} [p - L]_{(k+1)(1,r)} / (eps^2 N_k (N_k+1)), N_k = (1+r)(k+1).
Second-order TF on the ray through (1, r)  <=>  (D_k) is the moment sequence of a signed measure sigma on [0, S] with
nonnegative tails  <=>  min { sum_k c_k D_k : h(s) = sum c_k s^k increasing on [0,1] (scaled), h(0) = 0, h(1) = 1 } >= 0
(D_0 >= 0 is the second-order Golden-Thompson gap; the k = 0 constant part is handled by h(0) = 0)."""
import sys
import numpy as np
import mpmath as mp
import cvxpy as cp
from tf_ratio_sdp import increasing_poly_cone
mp.mp.dps = 60

def wavg(A, B, n, m):
    P = {0: mp.eye(2)}
    for step in range(n + m):
        Q = {}
        for j, C in P.items():
            Q[j] = Q.get(j, mp.zeros(2, 2)) + C * A
            Q[j + 1] = Q.get(j + 1, mp.zeros(2, 2)) + C * B
        P = {j: C for j, C in Q.items() if j <= m and (step + 1 - j) <= n}
    return (P[m][0, 0] + P[m][1, 1]) / mp.binomial(n + m, m)

def L(A_log, B_log, n, m):
    W = n * A_log + m * B_log
    tr, det = W[0, 0] + W[1, 1], W[0, 0] * W[1, 1] - W[0, 1] * W[1, 0]
    disc = mp.sqrt(tr ** 2 / 4 - det)
    return mp.e ** (tr / 2 + disc) + mp.e ** (tr / 2 - disc)

def D_seq(a, b, r, K, eps=mp.mpf('1e-12')):
    c, s = mp.cos(eps), mp.sin(eps)
    R = mp.matrix([[c, -s], [s, c]])
    A = mp.diag([1, a]); Alog = mp.diag([0, mp.log(a)])
    B = R * mp.diag([1, b]) * R.T; Blog = R * mp.diag([0, mp.log(b)]) * R.T
    out = []
    for k in range(K + 1):
        n, m = k + 1, r * (k + 1); N = n + m
        out.append((wavg(A, B, n, m) - L(Alog, Blog, n, m)) / (eps ** 2 * N * (N + 1)))
    return out

def min_increasing(D, S, K):
    sc = np.array([float(S) ** k for k in range(K + 1)])
    d = np.array([float(x) for x in D]) / sc
    cvec, cons = increasing_poly_cone(K)
    cons.append(cp.sum(cvec) == 1)
    prob = cp.Problem(cp.Minimize(d @ cvec), cons)
    prob.solve(solver=cp.CLARABEL)
    return prob.value, d

if __name__ == '__main__':
    r = int(sys.argv[1]); K = int(sys.argv[2])
    grid = [mp.mpf(x) for x in ['0.02', '0.1', '0.3', '0.6', '0.9', '1.1', '1.7', '3', '10', '50']]
    worst = (np.inf, None)
    for a in grid:
        for b in grid:
            if abs(a - 1) < 1e-9 and abs(b - 1) < 1e-9:
                continue
            D = D_seq(a, b, r, K)
            S = max(mp.mpf(1), a) * max(mp.mpf(1), b) ** r
            val, d = min_increasing(D, S, K)
            rel = val / max(abs(float(D[0])), 1e-300)
            if rel < worst[0]:
                worst = (rel, (float(a), float(b)), float(D[0]))
    print(f"r={r} K={K}: min over grid of (min increasing h of int h dsigma2) / D0 = {worst[0]: .3e} at (a,b)={worst[1]}, D0={worst[2]:.3e}", flush=True)
