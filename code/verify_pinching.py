"""Independent numerical check of the corollary of Theorem A for Dinh's Conjecture 5.1 (arXiv:2605.17782).

Notation (Dinh): A_{n,m}(A,B) = C(n+m,n)^{-1} * sum over words W with n letters A and m letters B of Tr W(A,B);
E_A(B) = sum_k Q_k B Q_k, the pinching of B onto the eigenspaces Q_k of A.

Claims checked:
  (1) gap := A_{n,m}(A,B) - Tr(A^n E_A(B)^m) >= 0 for A, B >= 0 (Conjecture 5.1, all n, m);
  (2) two-sided bound, with w_jk = ||Q_j B Q_k||_F^2 and hbar_n(x,y) = (x^{n+1}-y^{n+1})/((n+1)(x-y)):
        m(m-1) lmin(B)^{m-2} S_n <= gap <= m(m-1) lmax(B)^{m-2} S_n,   S_n = sum_{j<k} w_jk hbar_n(p_j,p_k);
      equality at m = 2 (Dinh's Prop. 6.1 formula);
  (3) n, m both even: gap >= 0 for Hermitian (indefinite) A, B;
  (4) the exact integral formula gap = m(m-1) int int s^{m-2} tau^n rho(s,tau) ds dtau on a few cases (quadrature).

A_{n,m} is computed exactly from the definition through the matrix-polynomial recursion for (A + tB)^{n+m},
so no word is ever skipped (C(n+m,n) A_{n,m} = [t^m] Tr (A + tB)^{n+m})."""
import itertools
import sys
from math import comb

import numpy as np
from scipy.linalg import eigvals

rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 2026)


def word_average(A, B, n, m):
    """A_{n,m}(A,B) via the coefficient of t^m in Tr (A + tB)^{n+m}."""
    d = A.shape[0]
    N = n + m
    coeffs = [np.eye(d, dtype=complex)]               # coefficients of (A + tB)^k in powers of t
    for _ in range(N):
        new = [None] * (len(coeffs) + 1)
        for j, C in enumerate(coeffs):
            new[j] = C @ A if new[j] is None else new[j] + C @ A
            new[j + 1] = C @ B
        coeffs = new
    return np.trace(coeffs[m]) / comb(N, n)


def word_average_bruteforce(A, B, n, m):
    """Same quantity by listing every word (used as a cross-check for small n + m)."""
    tot = 0.0
    for pos in itertools.combinations(range(n + m), m):
        W = np.eye(A.shape[0], dtype=complex)
        for i in range(n + m):
            W = W @ (B if i in pos else A)
        tot += np.trace(W)
    return tot / comb(n + m, n)


def random_unitary(d):
    return np.linalg.qr(rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d)))[0]


def random_psd(d, rank=None):
    r = d if rank is None else rank
    X = rng.normal(size=(d, r)) + 1j * rng.normal(size=(d, r))
    return X @ X.conj().T / r


def pinch_data(levels, U, B):
    """Spectral projections of A = U diag(levels) U^*, the pinching E_A(B), and the weights w_jk."""
    vals = np.unique(levels)
    Qs = [U[:, levels == v] @ U[:, levels == v].conj().T for v in vals]
    EB = sum(Q @ B @ Q for Q in Qs)
    w = {(j, k): np.linalg.norm(Qs[j] @ B @ Qs[k], "fro") ** 2 for j in range(len(vals)) for k in range(j + 1, len(vals))}
    return vals, Qs, EB, w


def hbar(n, x, y):
    return np.mean([x ** r * y ** (n - r) for r in range(n + 1)])   # = (x^{n+1}-y^{n+1})/((n+1)(x-y))


def check_case(levels, B, n, m, U=None):
    d = len(levels)
    U = random_unitary(d) if U is None else U
    A = U @ np.diag(levels) @ U.conj().T
    vals, Qs, EB, w = pinch_data(np.asarray(levels), U, B)
    lhs = word_average(A, B, n, m)
    pinched = np.trace(np.linalg.matrix_power(A, n) @ np.linalg.matrix_power(EB, m))
    gap = (lhs - pinched).real
    S = sum(wjk * hbar(n, vals[j], vals[k]) for (j, k), wjk in w.items())
    ev = np.linalg.eigvalsh(B)
    lo = m * (m - 1) * (ev[0] ** (m - 2) if m >= 2 else 0.0) * S if m >= 2 else 0.0
    hi = m * (m - 1) * (ev[-1] ** (m - 2) if m >= 2 else 0.0) * S if m >= 2 else 0.0
    scale = max(abs(lhs), abs(pinched), 1e-300)
    return gap, lo, hi, scale, abs(lhs.imag)


def main():
    # (0) recursion vs explicit word listing
    worst = 0.0
    for _ in range(30):
        d = rng.integers(2, 5)
        A, B = random_psd(d), random_psd(d)
        n, m = rng.integers(0, 5), rng.integers(0, 5)
        a1, a2 = word_average(A, B, n, m), word_average_bruteforce(A, B, n, m)
        worst = max(worst, abs(a1 - a2) / max(1.0, abs(a2)))
    print(f"[0] recursion vs brute-force word listing: max rel. diff {worst:.2e}")

    # (1)+(2) PSD A (repeated eigenvalues allowed) and PSD B (full and low rank), 0 <= n, m <= 8
    min_rel_gap, bound_viol, m2_err, ncase, max_imag = np.inf, 0.0, 0.0, 0, 0.0
    for trial in range(500):
        d = int(rng.integers(2, 7))
        nlev = int(rng.integers(1, d + 1))
        base = rng.uniform(0, 1, size=nlev)
        if rng.random() < 0.3:
            base[0] = 0.0                                        # singular A
        levels = np.sort(rng.choice(base, size=d, replace=True))
        B = random_psd(d, rank=int(rng.integers(1, d + 1)))
        U = random_unitary(d)
        for n in range(0, 9):
            for m in range(0, 9):
                gap, lo, hi, scale, im = check_case(levels, B, n, m, U)
                ncase += 1
                max_imag = max(max_imag, im / scale)
                min_rel_gap = min(min_rel_gap, gap / scale)
                tol = 1e-11 * scale
                bound_viol = max(bound_viol, (lo - gap) / scale, (gap - hi) / scale)
                if m == 2:
                    m2_err = max(m2_err, abs(gap - lo) / scale)
    print(f"[1] PSD cases: {ncase}; most negative relative gap {min_rel_gap:.2e}; max |Im A_nm|/scale {max_imag:.1e}")
    print(f"[2] two-sided bound: worst relative violation {bound_viol:.2e}; m=2 equality error {m2_err:.2e}")

    # (3) indefinite Hermitian A, B with n, m even
    worst3, n3 = np.inf, 0
    for trial in range(300):
        d = int(rng.integers(2, 6))
        nlev = int(rng.integers(1, d + 1))
        base = rng.uniform(-1, 1, size=nlev)
        levels = np.sort(rng.choice(base, size=d, replace=True))
        X = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))
        B = (X + X.conj().T) / 2
        U = random_unitary(d)
        for n in range(0, 9, 2):
            for m in range(0, 9, 2):
                gap, *_ , scale, _im = check_case(levels, B, n, m, U)
                worst3 = min(worst3, gap / scale)
                n3 += 1
    print(f"[3] Hermitian, n and m even: {n3} cases; most negative relative gap {worst3:.2e}")

    # (3b) odd exponent with indefinite letters: expect violations (sign of s^{m-2} tau^n not fixed)
    found = 0
    for trial in range(300):
        d = 3
        levels = np.sort(rng.uniform(-1, 1, size=d))
        X = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))
        B = (X + X.conj().T) / 2
        gap, *_ , scale, _im = check_case(levels, B, 1, 3)
        if gap < -1e-9 * scale:
            found += 1
    print(f"[3b] Hermitian (n,m)=(1,3): negative gap in {found}/300 random cases (sign condition is needed)")


def rho(g, P, s, tau):
    M = g.shape[0]
    xi = eigvals(g - s * np.eye(M), P - tau * np.eye(M))
    xi = xi[np.isfinite(xi)]
    return np.sum(np.abs(xi.imag)) / (2 * np.pi)


def integral_formula(n_s=500, n_phi=200):
    """(4) gap versus m(m-1) int int s^{m-2} tau^n rho_{B,A}(s,tau)."""
    print("[4] integral formula (quadrature):")
    for d, levels in [(3, [0.1, 0.5, 0.5]), (3, [0.0, 0.3, 0.9]), (4, [0.2, 0.2, 0.6, 1.0])]:
        U = random_unitary(d)
        levels = np.array(levels)
        A = U @ np.diag(levels) @ U.conj().T
        B = random_psd(d)
        lo, hi = np.linalg.eigvalsh(B)[[0, -1]]
        s = np.linspace(lo, hi, n_s)
        ws = np.full(n_s, s[1] - s[0]); ws[0] = ws[-1] = ws[0] / 2
        cuts = np.unique(levels)
        phi = (np.arange(n_phi) + 0.5) * np.pi / n_phi
        R = []                                   # rho on the grid, per piece
        for c, e in zip(cuts[:-1], cuts[1:]):
            tau = c + (e - c) * (1 - np.cos(phi)) / 2
            wt = (e - c) / 2 * np.sin(phi) * (np.pi / n_phi)
            R.append((tau, wt, np.array([[rho(B, A, si, tk) for si in s] for tk in tau])))
        for n, m in [(0, 2), (3, 2), (2, 3), (4, 4), (5, 3)]:
            val = sum(np.sum(wt[:, None] * ws[None, :] * (s[None, :] ** (m - 2)) * (tau[:, None] ** n) * r)
                      for tau, wt, r in R) * m * (m - 1)
            gap, *_ = check_case(levels, B, n, m, U)
            print(f"   d={d} levels={list(levels)} (n,m)=({n},{m}): gap {gap:+.6f}  integral {val:+.6f}")


if __name__ == "__main__":
    main()
    integral_formula()
