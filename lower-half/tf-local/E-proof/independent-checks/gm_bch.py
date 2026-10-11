"""Check log(e^P # e^Q) = (P+Q)/2 - (1/48)([P,[P,Q]] + [Q,[Q,P]]) + O(5) (used for the theta = 1/2 bottom value)."""
import mpmath as mp, random
mp.mp.dps = 50
def herm(d, rng):
    M = mp.matrix(d, d)
    for i in range(d):
        M[i, i] = mp.mpf(rng.gauss(0, 1))
        for j in range(i + 1, d):
            z = mp.mpc(rng.gauss(0, 1), rng.gauss(0, 1)); M[i, j] = z; M[j, i] = mp.conj(z)
    return M
def fun(M, f):
    ev, U = mp.eighe(M); return U * mp.diag([f(ev[i]) for i in range(M.rows)]) * U.H
rng = random.Random(2)
P, Q = herm(3, rng), herm(3, rng)
br = lambda a, b: a * b - b * a
for h in (mp.mpf('1e-2'), mp.mpf('5e-3')):
    eP, eQ = fun(h * P, mp.exp), fun(h * Q, mp.exp)
    Ph, Pmh = fun(eP, mp.sqrt), fun(eP, lambda t: 1 / mp.sqrt(t))
    G = Ph * fun(Pmh * eQ * Pmh, mp.sqrt) * Ph
    L = fun((G + G.H) / 2, mp.log)
    pred = h * (P + Q) / 2 - h ** 3 / 48 * (br(P, br(P, Q)) + br(Q, br(Q, P)))
    R = L - pred
    print('h', h, ' max|log G - prediction| / h^5 =', mp.nstr(max(abs(R[i, j]) for i in range(3) for j in range(3)) / h ** 5, 6))
