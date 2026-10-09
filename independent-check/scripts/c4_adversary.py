"""Adversarial search against D2 (Dinh's Conjecture 5.1) and the two-sided bound D3, PSD letters.

Independent code. For each run: dimension d, exponents (n, m) with m >= 3, a structural mode, and an objective.
Parametrisation:
  A = U diag(alpha) U*,  alpha_i = a_i^2 / max_j a_j^2  (PSD, ||A|| = 1),  U = expm(anti-Hermitian generator);
  B = Z Z* / ||Z Z*||  (PSD, ||B|| = 1), Z complex d x r.
Modes:
  generic    : alpha free (distinct eigenvalues; fine pinching onto the eigenvectors of A)
  near_deg   : alpha_1 = alpha_0 + delta with delta in [1e-10, 1e-3] (log-parametrised), fine pinching:
               this is the regime where E_A jumps as delta -> 0
  exact_deg  : alpha_1 = alpha_0 exactly (coarse pinching onto a 2-dim eigenspace)
  sing_A     : alpha_0 = 0
  lowrank_B  : r = 1 or 2 < d
Objectives (all >= 0 if D2/D3 hold; the optimiser minimises them):
  gap_norm : gap / ||B - E_A(B)||_F^2
  d3_low   : gap / (m(m-1) l_min(B)^{m-2} S_n) - 1           (only for full-rank B)
  d3_up    : 1 - gap / (m(m-1) l_max(B)^{m-2} S_n)
gap = A_{n,m}(A,B) - Tr(A^n E_A(B)^m), A_{n,m} by the t-expansion of Tr (A + tB)^{n+m}.
Best points are re-evaluated in 50-digit arithmetic (mpmath).

usage: python c4_adversary.py SEED SECONDS
"""
import sys
import time
from math import comb

import numpy as np
import mpmath as mp
from scipy.linalg import expm
from scipy.optimize import minimize

seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
budget = float(sys.argv[2]) if len(sys.argv) > 2 else 600
rng = np.random.default_rng(seed)
mp.mp.dps = 50

NM = [(1, 3), (2, 3), (3, 3), (0, 3), (2, 4), (3, 5), (5, 5), (4, 6), (6, 3), (1, 7), (8, 4)]
MODES = ["generic", "near_deg", "exact_deg", "sing_A", "lowrank_B"]
OBJS = ["gap_norm", "d3_low", "d3_up"]


def word_avg(A, B, n, m):
    d = A.shape[0]
    coeffs = [np.eye(d, dtype=complex)]
    for _ in range(n + m):
        new = [np.zeros((d, d), complex) for _ in range(len(coeffs) + 1)]
        for j, C in enumerate(coeffs):
            if j <= m:
                new[j] += C @ A
                if j + 1 <= m:
                    new[j + 1] += C @ B
        coeffs = new[: m + 1]
    return np.trace(coeffs[m]).real / comb(n + m, n)


def unpack(x, d, r, mode):
    k = 0
    a = x[k:k + d]; k += d
    G = x[k:k + d * d].reshape(d, d); k += d * d
    Zr = x[k:k + d * r].reshape(d, r); k += d * r
    Zi = x[k:k + d * r].reshape(d, r); k += d * r
    alpha = a ** 2
    groups = [[i] for i in range(d)]
    if mode == "near_deg":
        ld = x[k]; k += 1
        delta = 10.0 ** (-10 + 7 * (np.tanh(ld) + 1) / 2)       # in [1e-10, 1e-3]
        alpha[1] = alpha[0] + delta * max(alpha.max(), 1e-300)
    elif mode == "exact_deg":
        alpha[1] = alpha[0]
        groups = [[0, 1]] + [[i] for i in range(2, d)]
    elif mode == "sing_A":
        alpha[0] = 0.0
    alpha = alpha / alpha.max()
    H = (G - G.T) / 2 + 1j * (G + G.T) / 2                       # anti-Hermitian: real skew + i * symmetric
    U = expm(H)
    Z = Zr + 1j * Zi
    B = Z @ Z.conj().T
    B = B / np.linalg.norm(B, 2)
    return alpha, U, B, groups


def evaluate(alpha, U, B, groups, n, m):
    d = len(alpha)
    A = (U * alpha) @ U.conj().T
    Qs = [U[:, g] @ U[:, g].conj().T for g in groups]
    E = sum(Q @ B @ Q for Q in Qs)
    gap = word_avg(A, B, n, m) - np.trace(np.linalg.matrix_power(A, n) @ np.linalg.matrix_power(E, m)).real
    off = np.linalg.norm(B - E, "fro") ** 2
    levels = [alpha[g[0]] for g in groups]
    Sn = 0.0
    for j in range(len(groups)):
        for k in range(j + 1, len(groups)):
            wjk = np.linalg.norm(Qs[j] @ B @ Qs[k], "fro") ** 2
            x, y = levels[j], levels[k]
            Sn += wjk * sum(x ** r * y ** (n - r) for r in range(n + 1)) / (n + 1)
    ev = np.linalg.eigvalsh(B)
    return gap, off, Sn, ev[0], ev[-1], A, E


def objective(x, d, r, mode, obj, n, m):
    try:
        alpha, U, B, groups = unpack(x, d, r, mode)
        gap, off, Sn, lmin, lmax, A, E = evaluate(alpha, U, B, groups, n, m)
    except Exception:
        return 1e3
    if off < 1e-14 or Sn < 1e-300:
        return 1e3
    if obj == "gap_norm":
        return gap / off
    if obj == "d3_low":
        if lmin <= 1e-12:
            return 1e3
        return gap / (m * (m - 1) * lmin ** (m - 2) * Sn) - 1
    return 1 - gap / (m * (m - 1) * lmax ** (m - 2) * Sn)


def mp_check(x, d, r, mode, n, m):
    """50-digit recomputation from the raw parameters: U = expm(H) and B = Z Z* rebuilt in 50 digits, so that
    U is unitary and B is PSD to 50 digits (no double-precision artefacts)"""
    alpha, U, B, groups = unpack(x, d, r, mode)
    k = d
    G = x[k:k + d * d].reshape(d, d); k += d * d
    Zr = x[k:k + d * r].reshape(d, r); k += d * r
    Zi = x[k:k + d * r].reshape(d, r)
    H = mp.matrix(d, d)
    for i in range(d):
        for j in range(d):
            H[i, j] = mp.mpc((G[i, j] - G[j, i]) / 2, (G[i, j] + G[j, i]) / 2)
    Um = mp.expm(H)
    Zm = mp.matrix(d, r)
    for i in range(d):
        for j in range(r):
            Zm[i, j] = mp.mpc(Zr[i, j], Zi[i, j])
    Bm = Zm * Zm.H
    Zd = Zr + 1j * Zi
    Bm = Bm / mp.mpf(float(np.linalg.norm(Zd @ Zd.conj().T, 2)))     # any positive normalisation keeps B PSD
    Am = Um * mp.diag([mp.mpf(float(a)) for a in alpha]) * Um.H
    Qs = []
    for g in groups:
        Q = mp.zeros(d, d)
        for i in g:
            col = Um[:, i]
            Q += col * col.H
        Qs.append(Q)
    E = mp.zeros(d, d)
    for Q in Qs:
        E += Q * Bm * Q
    coeffs = [mp.eye(d)]
    for _ in range(n + m):
        new = [mp.zeros(d, d) for _ in range(len(coeffs) + 1)]
        for j, C in enumerate(coeffs):
            new[j] += C * Am
            new[j + 1] += C * Bm
        coeffs = new
    tr = lambda M: sum(M[i, i] for i in range(d))
    aw = mp.re(tr(coeffs[m])) / comb(n + m, n)
    pin = mp.re(tr((Am ** n) * (E ** m)))
    gap = aw - pin
    D = Bm - E
    off = mp.re(sum(abs(D[i, j]) ** 2 for i in range(d) for j in range(d)))
    levels = [mp.mpf(float(alpha[g[0]])) for g in groups]
    Sn = mp.mpf(0)
    for j in range(len(groups)):
        for k in range(j + 1, len(groups)):
            M = Qs[j] * Bm * Qs[k]
            wjk = mp.re(sum(abs(M[a, b]) ** 2 for a in range(d) for b in range(d)))
            x, y = levels[j], levels[k]
            Sn += wjk * sum(x ** r * y ** (n - r) for r in range(n + 1)) / (n + 1)
    ev = sorted(mp.re(v) for v in mp.eig(Bm)[0])
    return gap, off, Sn, ev[0], ev[-1]


def main():
    t0 = time.time()
    best = {}
    suspects = []
    rounds = 0
    while time.time() - t0 < budget:
        d = int(rng.integers(2, 6))
        n, m = NM[int(rng.integers(len(NM)))]
        mode = MODES[int(rng.integers(len(MODES)))]
        obj = OBJS[int(rng.integers(len(OBJS)))]
        if mode in ("exact_deg", "near_deg") and d < 3:
            d = 3
        r = int(rng.integers(1, d)) if mode == "lowrank_B" else d
        if obj == "d3_low" and r < d:
            obj = "gap_norm"
        npar = d + d * d + 2 * d * r + (1 if mode == "near_deg" else 0)
        x0 = rng.normal(size=npar)
        res = minimize(objective, x0, args=(d, r, mode, obj, n, m), method="Nelder-Mead",
                       options=dict(maxiter=2500, maxfev=2500, xatol=1e-10, fatol=1e-14, adaptive=True))
        res = minimize(objective, res.x, args=(d, r, mode, obj, n, m), method="Powell",
                       options=dict(maxiter=50, maxfev=2500, xtol=1e-10, ftol=1e-15))
        rounds += 1
        key = (obj, mode)
        if key not in best or res.fun < best[key][0]:
            best[key] = (res.fun, d, r, n, m, res.x.copy())
        if res.fun < 0:
            suspects.append((res.fun, d, r, n, m, mode, obj, res.x.copy()))
    print(f"seed {seed}: {rounds} optimisation rounds in {time.time() - t0:.0f}s")
    print(f"rounds ending with a negative double-precision objective: {len(suspects)} (all re-checked in 50 digits)")
    still_neg = 0
    min_hp = None
    for i, (val, d, r, n, m, mode, obj, x) in enumerate(sorted(suspects, key=lambda z: z[0])):
        gap, off, Sn, lmin, lmax = mp_check(x, d, r, mode, n, m)
        if obj == "gap_norm":
            hp = gap / off
        elif obj == "d3_low":
            hp = gap / (m * (m - 1) * lmin ** (m - 2) * Sn) - 1
        else:
            hp = 1 - gap / (m * (m - 1) * lmax ** (m - 2) * Sn)
        still_neg += hp < 0
        min_hp = hp if min_hp is None or hp < min_hp else min_hp
        if i < 8 or hp < 0:
            print(f"  suspect {obj} {mode} d={d} r={r} (n,m)=({n},{m}): double {val:.3e} -> 50-digit {mp.nstr(hp, 8)} "
                  f"(gap {mp.nstr(gap, 8)}, ||B-E||^2 {mp.nstr(off, 4)})")
    if suspects:
        print(f"  suspects still negative in 50 digits: {still_neg}; smallest 50-digit objective among suspects: "
              f"{mp.nstr(min_hp, 6)}")
    print("best (smallest) objective values found, re-evaluated in 50-digit arithmetic:")
    for key in sorted(best):
        val, d, r, n, m, x = best[key]
        obj, mode = key
        alpha, U, B, groups = unpack(x, d, r, mode)
        gap, off, Sn, lmin, lmax = mp_check(x, d, r, mode, n, m)
        if obj == "gap_norm":
            hp = gap / off
        elif obj == "d3_low":
            hp = gap / (m * (m - 1) * lmin ** (m - 2) * Sn) - 1
        else:
            hp = 1 - gap / (m * (m - 1) * lmax ** (m - 2) * Sn)
        print(f"  {obj:8s} {mode:9s} d={d} r={r} (n,m)=({n},{m}): double {val: .3e}  50-digit {mp.nstr(hp, 6):>12s}  "
              f"gap {mp.nstr(gap, 6)}  ||B-E||^2 {mp.nstr(off, 4)}  l_min(B) {mp.nstr(lmin, 3)}  "
              f"min gap of A-spectrum {np.min(np.diff(np.sort(alpha))) if d > 1 else 0:.1e}")


if __name__ == "__main__":
    main()
