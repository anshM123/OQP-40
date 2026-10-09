"""Is there a trivial route to Dinh's conjecture?  If B -> A_{n,m}(A,B) were convex on PSD matrices (A >= 0 fixed),
then, since E_A(B) is an average of unitary conjugations U B U* with U commuting with A and A_{n,m}(A, U B U*) =
A_{n,m}(A,B), Jensen would give the conjecture at once. Test the Hessian
    h = d^2/de^2 A_{n,m}(A, B + e H) at e = 0
for PSD A, B and Hermitian H, and along the pinching path B(e) = E + e (B - E) (where it would suffice).
Exact rational arithmetic for the reported witnesses.
usage: python c7_convexity_route.py SEED
"""
import sys
from math import comb

import numpy as np
from flint import fmpq, fmpq_mat

rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 11)


def coeff_e2(A, B, H, n, m):
    """coefficient of e^2 in A_{n,m}(A, B + eH): words with n A's, (m-2) B's, 2 H's, normalised"""
    d = A.shape[0]
    # polynomial in (t, u): track coefficients of t^j u^k in (A + tB + uH)^N, j + k <= m, k <= 2
    N = n + m
    C = {(0, 0): np.eye(d)}
    for _ in range(N):
        new = {}
        for (j, k), M in C.items():
            for (dj, dk, X) in ((0, 0, A), (1, 0, B), (0, 1, H)):
                jj, kk = j + dj, k + dk
                if kk > 2 or jj + kk > m:
                    continue
                new[(jj, kk)] = new.get((jj, kk), 0) + M @ X
        C = new
    return np.trace(C[(m - 2, 2)]) / comb(N, n)


def coeff_e2_exact(A, B, H, n, m):
    d = A.nrows()
    I = fmpq_mat(d, d, [1 if i == j else 0 for i in range(d) for j in range(d)])
    C = {(0, 0): I}
    for _ in range(n + m):
        new = {}
        for (j, k), M in C.items():
            for (dj, dk, X) in ((0, 0, A), (1, 0, B), (0, 1, H)):
                jj, kk = j + dj, k + dk
                if kk > 2 or jj + kk > m:
                    continue
                P = M * X
                new[(jj, kk)] = P if (jj, kk) not in new else new[(jj, kk)] + P
        C = new
    T = C[(m - 2, 2)]
    return sum((T[i, i] for i in range(d)), fmpq(0)) / comb(n + m, n)


def q(M):
    return fmpq_mat(M.shape[0], M.shape[1], [int(x) for x in M.flatten()])


def main():
    for (n, m) in [(1, 3), (2, 3), (3, 3), (2, 4), (4, 4), (5, 5)]:
        neg_free, neg_path, tot = 0, 0, 0
        witness = None
        for trial in range(2000):
            d = int(rng.integers(2, 4))
            X = rng.integers(-3, 4, size=(d, d)); A = (X @ X.T).astype(float)
            Y = rng.integers(-3, 4, size=(d, d)); B = (Y @ Y.T).astype(float)
            Z = rng.integers(-3, 4, size=(d, d)); H = (Z + Z.T).astype(float)
            tot += 1
            h = coeff_e2(A, B, H, n, m)
            if h < -1e-9 * (1 + abs(h)):
                neg_free += 1
                if witness is None:
                    witness = (A.astype(int), B.astype(int), H.astype(int))
            # pinching path: base point E_A(B), direction B - E_A(B), at e in (0,1)
            w, U = np.linalg.eigh(A)
            Bp = U.T @ B @ U
            groups = np.abs(w[:, None] - w[None, :]) < 1e-9
            Ep = np.where(groups, Bp, 0.0)
            for e in (0.0, 0.5, 0.9):
                Pe = U @ (Ep + e * (Bp - Ep)) @ U.T
                Hd = U @ (Bp - Ep) @ U.T
                if coeff_e2(A, Pe, Hd, n, m) < -1e-9:
                    neg_path += 1
                    break
        line = (f"(n,m)=({n},{m}): Hessian of B -> A_nm(A,B) negative in {neg_free}/{tot} random (A,B>=0, H Hermitian); "
                f"negative somewhere on the pinching path in {neg_path}/{tot}")
        if witness is not None:
            A, B, H = witness
            ex = coeff_e2_exact(q(A), q(B), q(H), n, m)
            line += f"; exact witness value {float(ex):.6e} for A={A.tolist()}, B={B.tolist()}, H={H.tolist()}"
        print(line)
        sys.stdout.flush()


if __name__ == "__main__":
    main()
