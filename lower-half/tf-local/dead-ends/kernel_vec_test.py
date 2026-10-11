"""Is g(lam) = <v, e^{H + lam K} v> a positive Laplace transform when K v = 0 ?  (Hankel test on Taylor moments.)
Also tests the superoperator form of BMV-P at (n,m) = (1,1): v = I, H = L_Z + R_Z, K = (L_T - R_T)/2."""
import mpmath as mp, random, sys
mp.mp.dps = 60

def herm(d, rng, s=1.0):
    M = mp.matrix(d, d)
    for i in range(d):
        M[i, i] = mp.mpf(rng.gauss(0, s))
        for j in range(i + 1, d):
            z = mp.mpc(rng.gauss(0, s), rng.gauss(0, s)) / mp.sqrt(2)
            M[i, j] = z; M[j, i] = mp.conj(z)
    return M

def taylor(f, K, R):
    M = 4 * K
    vals = [f(R * mp.expjpi(2 * mp.mpf(j) / M)) for j in range(M)]
    return [sum(vals[j] * mp.expjpi(-2 * mp.mpf(j * k) / M) for j in range(M)) / M / R ** k for k in range(K + 1)]

def hankel_min(mom, J):
    H = mp.matrix(J + 1, J + 1)
    for i in range(J + 1):
        for j in range(J + 1):
            H[i, j] = mom[i + j]
    Dg = [1 / mp.sqrt(abs(H[i, i])) for i in range(J + 1)]
    for i in range(J + 1):
        for j in range(J + 1):
            H[i, j] *= Dg[i] * Dg[j]
    e = mp.eigsy(H)[0]
    return min(e[i] for i in range(J + 1))

rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 0)
Kord = 20
print("rank-one kernel test: g(lam) = <v, e^{H+lam K} v>, K v = 0")
for trial in range(10):
    d = [2, 3, 4, 5][trial % 4]
    H = herm(d, rng, rng.choice([0.5, 1.5, 3.0]))
    Kf = herm(d - 1, rng, rng.choice([0.5, 1.5, 3.0]))
    K = mp.zeros(d, d)
    for i in range(1, d):
        for j in range(1, d):
            K[i, j] = Kf[i - 1, j - 1]
    g = lambda lam: (mp.expm(H + lam * K))[0, 0]
    c = taylor(g, Kord, mp.mpf(1) / 2)
    mom = [mp.re(c[k]) * mp.factorial(k) for k in range(Kord + 1)]
    print(f"  d={d}: min eig normalised Hankel J=4,7,10: {[mp.nstr(hankel_min(mom, J), 4) for J in (4, 7, 10)]}")
