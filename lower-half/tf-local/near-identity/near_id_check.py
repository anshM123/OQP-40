"""Near the identity: A = e^{hX}, B = e^{hY}. Check p_{n,m} - L_{n,m} ~ n m (n+m-1)/24 * h^4 ||[X,Y]||_F^2."""
import mpmath as mp
import random
mp.mp.dps = 60

def herm(d, rng):
    M = mp.matrix(d, d)
    for i in range(d):
        M[i, i] = mp.mpf(rng.gauss(0, 1))
        for j in range(i + 1, d):
            z = mp.mpc(rng.gauss(0, 1), rng.gauss(0, 1)) / mp.sqrt(2)
            M[i, j] = z; M[j, i] = mp.conj(z)
    return M

def word_avg(A, B, n, m):
    d = A.rows
    S = {(0, 0): mp.eye(d)}
    for i in range(n + 1):
        for j in range(m + 1):
            if i == 0 and j == 0:
                continue
            T = mp.zeros(d, d)
            if i > 0: T += A * S[(i - 1, j)]
            if j > 0: T += B * S[(i, j - 1)]
            S[(i, j)] = T
    tr = sum(S[(n, m)][k, k] for k in range(d))
    return mp.re(tr) / mp.binomial(n + m, n)

rng = random.Random(7)
for d in (2, 3, 4):
    X, Y = herm(d, rng), herm(d, rng)
    C = X * Y - Y * X
    cf = mp.re(sum(abs(C[i, j]) ** 2 for i in range(d) for j in range(d)))
    for h in (mp.mpf('1e-2'), mp.mpf('1e-3')):
        A, B = mp.expm(h * X), mp.expm(h * Y)
        row = []
        for (n, m) in [(1, 1), (2, 1), (2, 2), (3, 2), (3, 3), (4, 2), (5, 3)]:
            p = word_avg(A, B, n, m)
            L = mp.re(sum(mp.expm(h * (n * X + m * Y))[k, k] for k in range(d)))
            ratio = (p - L) / (h ** 4 * cf) / (mp.mpf(n * m * (n + m - 1)) / 24)
            row.append(f"({n},{m}):{mp.nstr(ratio, 8)}")
        print(f"d={d} h={mp.nstr(h,2)}  " + "  ".join(row))
