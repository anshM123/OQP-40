"""Check the first-order deviation measure sigma1 near the identity beyond M_3.
Prediction (theta = 1/2 ray, A = e^{hX}, B = e^{hY}, S = (X+Y)/2, T = X - Y in the eigenbasis s_j of S):
  int w^j d sigma1 = (th(1-th)/2) sum_{j,k} |T_jk|^2 [ j (s_j^{j-1} + s_k^{j-1})/2 - j * avg_{[s_j,s_k]} w^{j-1} ].
Phi(N) = p - L on the ray has h-expansion c4(N) h^4 + c5(N) h^5 + ...; the N^4 part of c5 is m4/24.
We extract c4, c5 from exact word averages at N = 2,4,6,8 (n = m = N/2) and several h, then fit in N."""
import mpmath as mp
import random
mp.mp.dps = 80

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
            if i == 0 and j == 0: continue
            T = mp.zeros(d, d)
            if i > 0: T += A * S[(i - 1, j)]
            if j > 0: T += B * S[(i, j - 1)]
            S[(i, j)] = T
    return mp.re(sum(S[(n, m)][k, k] for k in range(d))) / mp.binomial(n + m, n)

rng = random.Random(3)
d = 3
X, Y = herm(d, rng), herm(d, rng)
th = mp.mpf(1) / 2
S = th * X + (1 - th) * Y
Tm = X - Y
ev, U = mp.eighe(S)
Tb = U.H * Tm * U
s = [ev[i] for i in range(d)]

def avg_pow(a, b, p):  # average of w^p over [a,b]
    if abs(a - b) < mp.mpf('1e-40'):
        return a ** p
    return (b ** (p + 1) - a ** (p + 1)) / ((p + 1) * (b - a))

def m_pred(jj):
    tot = 0
    for j in range(d):
        for k in range(d):
            w = abs(Tb[j, k]) ** 2
            tot += w * (jj * (s[j] ** (jj - 1) + s[k] ** (jj - 1)) / 2 - jj * avg_pow(s[j], s[k], jj - 1))
    return th * (1 - th) / 2 * tot

C = X * Y - Y * X
kap = mp.re(sum(abs(C[i, j]) ** 2 for i in range(d) for j in range(d)))
print('m3 pred', mp.nstr(m_pred(3), 12), ' vs th(1-th)kappa/4 =', mp.nstr(th * (1 - th) * kap / 4, 12))
print('m4 pred', mp.nstr(m_pred(4), 12))

hs = [mp.mpf(1) / 2 ** k for k in range(7, 12)]
Ns = [2, 4, 6, 8]
c4, c5 = {}, {}
for N in Ns:
    n = N // 2
    vals = []
    for h in hs:
        A, B = mp.expm(h * X), mp.expm(h * Y)
        p = word_avg(A, B, n, n)
        L = mp.re(sum(mp.expm(h * N * S)[k, k] for k in range(d)))
        vals.append((p - L) / h ** 4)
    # fit vals = c4 + c5 h + c6 h^2 + c7 h^3 + c8 h^4 (Vandermonde, exact at 80 digits)
    V = mp.matrix([[h ** e for e in range(len(hs))] for h in hs])
    coef = mp.lu_solve(V, mp.matrix(vals))
    c4[N], c5[N] = coef[0], coef[1]
    print(f"N={N}: c4={mp.nstr(c4[N],14)}  pred={mp.nstr(th*(1-th)*kap/24*N**2*(N-1),14)}   c5={mp.nstr(c5[N],14)}")
# c5(N) = a4 N^4 + a3 N^3 + a2 N^2 (no N^1, N^0: Phi has a double zero at N=0 at every order)
V = mp.matrix([[mp.mpf(N) ** 4, mp.mpf(N) ** 3, mp.mpf(N) ** 2] for N in Ns[:3]])
a = mp.lu_solve(V, mp.matrix([c5[N] for N in Ns[:3]]))
print('fit a4 (N^4 coef of c5) =', mp.nstr(a[0], 12), '  predicted m4/24 =', mp.nstr(m_pred(4) / 24, 12))
print('consistency at N=8: fit', mp.nstr(a[0]*8**4 + a[1]*8**3 + a[2]*8**2, 12), ' actual', mp.nstr(c5[8], 12))
