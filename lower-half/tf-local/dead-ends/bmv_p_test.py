"""BMV-type test along the pinching family: f(lam) = p_{n,m}(e^{Z+(1-th) lam T}, e^{Z - th lam T}), T off-diagonal
w.r.t. Z (T_d = 0), th = n/(n+m). If f is the Laplace transform of a positive measure nu, the moments
m_k = f^{(k)}(0) form a positive semidefinite Hankel sequence. Taylor coefficients by Cauchy integrals (mpmath)."""
import mpmath as mp, random, sys
mp.mp.dps = 50

def herm(d, rng, s=1.0):
    M = mp.matrix(d, d)
    for i in range(d):
        M[i, i] = mp.mpf(rng.gauss(0, s))
        for j in range(i + 1, d):
            z = mp.mpc(rng.gauss(0, s), rng.gauss(0, s)) / mp.sqrt(2)
            M[i, j] = z; M[j, i] = mp.conj(z)
    return M

def expmh(M):
    return mp.expm(M)

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
    return sum(S[(n, m)][k, k] for k in range(d)) / mp.binomial(n + m, n)

def taylor(f, K, R):
    M = 4 * K
    vals = [f(R * mp.expjpi(2 * mp.mpf(j) / M)) for j in range(M)]
    return [sum(vals[j] * mp.expjpi(-2 * mp.mpf(j * k) / M) for j in range(M)) / M / R ** k for k in range(K + 1)]

def _main():
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 0)
    K = 16
    for trial in range(8):
        d = [2, 3, 3, 4][trial % 4]
        Z = herm(d, rng, 1.0); T = herm(d, rng, 1.0)
        ev, U = mp.eighe(Z)
        Tz = U.H * T * U
        for i in range(d): Tz[i, i] = 0
        T = U * Tz * U.H  # off-diagonal w.r.t. Z
        n, m = [(1, 1), (2, 1), (2, 2), (3, 2)][trial % 4]
        th = mp.mpf(n) / (n + m)
        f = lambda lam: word_avg(expmh(Z + (1 - th) * lam * T), expmh(Z - th * lam * T), n, m)
        c = taylor(f, K, mp.mpf(1))
        mom = [mp.re(c[k]) * mp.factorial(k) for k in range(K + 1)]
        # Hankel PSD test on moments m_0..m_{2J}
        J = K // 2
        H = mp.matrix(J + 1, J + 1)
        for i in range(J + 1):
            for j in range(J + 1):
                H[i, j] = mom[i + j]
        # normalise rows/cols to avoid scaling issues
        D = [1 / mp.sqrt(abs(H[i, i])) for i in range(J + 1)]
        for i in range(J + 1):
            for j in range(J + 1):
                H[i, j] *= D[i] * D[j]
        eig = mp.eigsy(H)[0]
        mineig = min(eig[i] for i in range(J + 1))
        print(f"d={d} (n,m)=({n},{m})  m1={mp.nstr(mom[1],5)} m2={mp.nstr(mom[2],5)} m3={mp.nstr(mom[3],5)} m4={mp.nstr(mom[4],5)}  "
              f"min eig of normalised Hankel(0..{2*J}) = {mp.nstr(mineig, 5)}")


if __name__ == "__main__":
    _main()
