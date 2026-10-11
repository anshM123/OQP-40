"""Shared helpers (mpmath) for the near-identity computations."""
import mpmath as mp

def herm(d, rng, scale=1.0):
    M = mp.matrix(d, d)
    for i in range(d):
        M[i, i] = mp.mpf(rng.gauss(0, scale))
        for j in range(i + 1, d):
            z = mp.mpc(rng.gauss(0, scale), rng.gauss(0, scale)) / mp.sqrt(2)
            M[i, j] = z; M[j, i] = mp.conj(z)
    return M

def tr(M):
    return mp.re(sum(M[k, k] for k in range(M.rows)))

def fpow(M, p):
    ev, U = mp.eighe(M)
    return U * mp.diag([ev[i] ** p for i in range(M.rows)]) * U.H

def fexp(M):
    ev, U = mp.eighe(M)
    return U * mp.diag([mp.exp(ev[i]) for i in range(M.rows)]) * U.H

def gmean(P, Q, t=mp.mpf(1) / 2):
    """Kubo-Ando weighted geometric mean P #_t Q."""
    Ph, Pmh = fpow(P, mp.mpf(1) / 2), fpow(P, -mp.mpf(1) / 2)
    return Ph * fpow(Pmh * Q * Pmh, t) * Ph

def tbot_half(X, Y, h):
    """Bottom-level TF value at theta = 1/2 for A = e^{hX}, B = e^{hY}: [GT - 2 e^{3 zeta_min} AH]/6."""
    A, B = fexp(h * X), fexp(h * Y)
    Z = h * (X + Y) / 2
    GT = tr(A * B) - tr(fexp(2 * Z))
    zmin = min(mp.eighe(Z)[0][i] for i in range(X.rows))
    AH = tr(fexp(-Z)) - tr(gmean(fexp(-h * X), fexp(-h * Y)))
    return (GT - 2 * mp.exp(3 * zmin) * AH) / 6

def kappa(X, Y):
    C = X * Y - Y * X
    return mp.re(sum(abs(C[i, j]) ** 2 for i in range(X.rows) for j in range(X.rows)))
