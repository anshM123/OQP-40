"""The n -> infinity limit of Conjecture F and of the lower half (LH) of OQP 40.
With A = exp(H/n) and n -> infinity, the word average p_{n,m}(A,B) tends to D_m(H,B) := d^m/dt^m Tr exp(H + tB) at t = 0,
so the limits of the two inequalities are
   (CF_m)  D_m(H,B) >= Tr((e^{H/m} B)^m),        (CLH_m)  D_m(H,B) >= Tr exp(H + m log B).
D_m is computed as m! times the trace of the top-right block of expm of the (m+1)-block bidiagonal matrix with H on the
diagonal and B above it.  Search: for m = 2..6 and d = 2..4, the best of 40 random starts (H Hermitian, B = exp(Hermitian)),
then Nelder-Mead on log(D_m / right side).  Usage: python lh_limit_search.py seed   (we used seed 1)."""
import sys
import numpy as np
from scipy.linalg import expm, logm, eigh
from scipy.optimize import minimize
from math import factorial

rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 1)


def herm(v, d):
    M = np.zeros((d, d), complex)
    iu = np.triu_indices(d, 1)
    M[np.diag_indices(d)] = v[:d]
    k = len(iu[0])
    M[iu] = v[d:d + k] + 1j * v[d + k:d + 2 * k]
    M = M + np.triu(M, 1).conj().T
    return M


def Dm(H, B, m):
    d = H.shape[0]
    N = (m + 1) * d
    Z = np.zeros((N, N), complex)
    for k in range(m + 1):
        Z[k*d:(k+1)*d, k*d:(k+1)*d] = H
        if k < m:
            Z[k*d:(k+1)*d, (k+1)*d:(k+2)*d] = B
    E = expm(Z)
    return factorial(m) * np.trace(E[0:d, m*d:(m+1)*d]).real


def powm(B, p):
    w, V = eigh(B)
    return (V * np.maximum(w, 0) ** p) @ V.conj().T


def F(H, B, m):
    w, V = eigh(H)
    Em = (V * np.exp(w / m)) @ V.conj().T
    return np.trace(np.linalg.matrix_power(Em @ B, m)).real


def L(H, B, m):
    w, V = eigh(B)
    lB = (V * np.log(w)) @ V.conj().T
    return np.trace(expm(H + m * lB)).real


def unpack(x, d):
    nh = d * d
    H = herm(x[:nh], d)
    G = herm(x[nh:2*nh], d)
    B = expm(G)  # B > 0
    return H, B


def obj(x, d, m, which):
    H, B = unpack(x, d)
    D = Dm(H, B, m)
    R = F(H, B, m) if which == 'F' else L(H, B, m)
    if D <= 0 or R <= 0:
        return -1e3 if D <= 0 else 1e3
    return np.log(D / R)


if __name__ == '__main__':
    for m in [2, 3, 4, 5, 6]:
        for d in [2, 3, 4]:
            for which in ['F', 'L']:
                best = np.inf
                bx = None
                for trial in range(40):
                    scale = rng.choice([1.0, 3.0, 8.0])
                    x0 = rng.normal(size=2 * d * d) * scale
                    v = obj(x0, d, m, which)
                    if v < best:
                        best, bx = v, x0
                for rep in range(6):
                    x0 = bx + rng.normal(size=2 * d * d) * 0.5 if rep else bx
                    r = minimize(obj, x0, args=(d, m, which), method='Nelder-Mead',
                                 options={'maxiter': 6000, 'xatol': 1e-10, 'fatol': 1e-14})
                    if r.fun < best:
                        best, bx = r.fun, r.x
                H, B = unpack(bx, d)
                ev = np.linalg.eigvalsh(H)
                print(f"m={m} d={d} {which}: min log(D/R) = {best:.3e}  spread(H)={ev[-1]-ev[0]:.2f}  cond(B)={np.linalg.cond(B):.1e}", flush=True)
