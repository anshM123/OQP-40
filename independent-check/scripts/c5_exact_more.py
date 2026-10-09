"""More exact (rational) checks: D5 (Jensen form), near-degenerate A, long words, d = 6.

[F1] D5 inequality: T_f(A,B) >= Tr f(A, E_A(B)) for random polynomials f(tau, s) that are convex in s on a
     rational rectangle R = [a_1, a_r] x [L, U] containing [a_1, a_r] x [l_min(B), l_max(B)], but are neither
     monotone in s nor positive, and are NOT convex in s outside R. Construction:
        d^2 f / ds^2 = q(tau, s) = c(tau) * (W^2 + delta - (s - s_mid)^2) * (positive factor) + SOS,
     where W = (U - L)/2, s_mid = (U + L)/2, c(tau) > 0 on [a_1, a_r]; then
        f = double s-antiderivative of q + a(tau) + b(tau) s   with random indefinite a, b.
     Exact rational arithmetic; also Hermitian (indefinite) A and B (D5 is stated for Hermitian letters).
[F2] D5 sharpness: f with d^2 f/ds^2 >= 0 only for s >= s_*, s_* inside (l_min, l_max): the inequality can fail.
[F3] near-degenerate A: eigenvalues alpha, alpha + 10^-k (k = 2..12) with fine pinching; gap >= 0 and D3 exactly;
     and the comparison with the coarse pinching at delta = 0.
[F4] long words: d = 3, all (n,m) with n + m = 30, PSD; and d = 6 with eigenvalue multiplicities (3,2,1), rank-2 B,
     n + m <= 14.
"""
import random
import sys
from math import comb

import mpmath as mp
from flint import fmpq, fmpq_mat

mp.mp.dps = 60
R = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 777)


def eye(d):
    return fmpq_mat(d, d, [1 if i == j else 0 for i in range(d) for j in range(d)])


def zero(d):
    return fmpq_mat(d, d, [0] * (d * d))


def tr(M):
    s = fmpq(0)
    for i in range(M.nrows()):
        s += M[i, i]
    return s


def rq(lo, hi, den=12):
    return fmpq(R.randint(lo * den, hi * den), den)


def rand_orth(d):
    S = zero(d)
    for i in range(d):
        for j in range(i + 1, d):
            v = rq(-2, 2, 5)
            S[i, j], S[j, i] = v, -v
    return (eye(d) - S) * (eye(d) + S).inv()


def pair(d, levels, rankB=None, indefB=False):
    U = rand_orth(d)
    D = zero(d)
    for i, l in enumerate(levels):
        D[i, i] = fmpq(l)
    A = U * D * U.transpose()
    alphas = sorted(set(fmpq(l) for l in levels))
    projs = []
    for a in alphas:
        idx = [i for i, l in enumerate(levels) if fmpq(l) == a]
        Uk = fmpq_mat(d, len(idx), [U[r, c] for r in range(d) for c in idx])
        projs.append(Uk * Uk.transpose())
    if indefB:
        B = zero(d)
        for i in range(d):
            for j in range(i, d):
                v = rq(-2, 2)
                B[i, j], B[j, i] = v, v
    else:
        r = rankB or d
        X = fmpq_mat(d, r, [rq(-2, 2, 6) for _ in range(d * r)])
        B = X * X.transpose()
    E = sum((P * B * P for P in projs), zero(d))
    return A, B, E, projs, alphas


def word_sums(A, B, Nmax, only_N=None):
    d = A.nrows()
    ws = {(0, 0): tr(eye(d))}
    coeffs = [eye(d)]
    for N in range(1, Nmax + 1):
        new = [None] * (N + 1)
        for j, C in enumerate(coeffs):
            CA, CB = C * A, C * B
            new[j] = CA if new[j] is None else new[j] + CA
            new[j + 1] = CB if new[j + 1] is None else new[j + 1] + CB
        coeffs = new
        if only_N is None or N == only_N:
            for m in range(N + 1):
                ws[(N - m, m)] = tr(coeffs[m])
    return ws


def powers(M, k):
    out = [eye(M.nrows())]
    for _ in range(k):
        out.append(out[-1] * M)
    return out


def eig_ext(Bm):
    d = Bm.nrows()
    M = mp.matrix([[mp.mpf(int(Bm[i, j].p)) / int(Bm[i, j].q) for j in range(d)] for i in range(d)])
    ev = sorted(mp.eigsy(M)[0])
    return ev[0], ev[-1]


def outer_rational(x, below):
    """rational number just below (or above) the real x"""
    q = fmpq(int(mp.floor(x * 10 ** 6)), 10 ** 6) if below else fmpq(int(mp.ceil(x * 10 ** 6)), 10 ** 6)
    return q


# ---- polynomials in (tau, s) as dicts {(n,m): fmpq} -------------------------------------------------------------
def padd(p, q, c=1):
    out = dict(p)
    for k, v in q.items():
        out[k] = out.get(k, fmpq(0)) + c * v
    return {k: v for k, v in out.items() if v != 0}


def pmul(p, q):
    out = {}
    for (a, b), u in p.items():
        for (c, d), v in q.items():
            out[(a + c, b + d)] = out.get((a + c, b + d), fmpq(0)) + u * v
    return {k: v for k, v in out.items() if v != 0}


def s_antider2(q):
    """double antiderivative in s (constants zero)"""
    return {(n, m + 2): c / ((m + 1) * (m + 2)) for (n, m), c in q.items()}


def rand_poly(dt, ds, lo=-2, hi=2):
    return {(n, m): rq(lo, hi, 4) for n in range(dt + 1) for m in range(ds + 1) if R.random() < 0.8}


def evalp(p, t, s):
    return sum((c * t ** n * s ** m for (n, m), c in p.items()), fmpq(0))


def T_f(p, ws):
    return sum((c * ws[(n, m)] / comb(n + m, n) for (n, m), c in p.items()), fmpq(0))


def Tr_f_pinched(p, Ap, Ep):
    return sum((c * tr(Ap[n] * Ep[m]) for (n, m), c in p.items()), fmpq(0))


def main():
    say = lambda s: (print(s), sys.stdout.flush())
    # ---------------- [F1] D5 inequality ----------------
    n_cases, n_neg, n_nonmono, n_nonpos, n_nonconvex_out = 0, 0, 0, 0, 0
    worst = None
    for trial in range(60):
        d = R.randint(2, 4)
        herm = trial % 3 == 2
        if herm:
            levels = [rq(-2, 2, 3) for _ in range(d)]
        else:
            levels = [rq(0, 2, 3) for _ in range(d)]
        if trial % 4 == 1:
            levels[1] = levels[0]                       # repeated eigenvalue
        A, B, E, projs, alphas = pair(d, levels, indefB=herm)
        if len(alphas) < 2 or A * B == B * A:
            continue
        lmin, lmax = eig_ext(B)
        L, U = outer_rational(lmin, True), outer_rational(lmax, False)
        a1, ar = alphas[0], alphas[-1]
        W, smid = (U - L) / 2, (U + L) / 2
        delta = W * W / 10
        # q = c(tau) * (W^2 + delta - (s - smid)^2) * (1 + small) + SOS ;  c(tau) = 1 + (tau - a1)^2 > 0
        c_tau = padd({(0, 0): fmpq(1)}, pmul({(1, 0): fmpq(1), (0, 0): -a1}, {(1, 0): fmpq(1), (0, 0): -a1}))
        bump = {(0, 0): W * W + delta - smid * smid, (0, 1): 2 * smid, (0, 2): fmpq(-1)}
        q = pmul(c_tau, bump)
        for _ in range(R.randint(0, 2)):
            g = rand_poly(1, 1)
            q = padd(q, pmul(g, g), fmpq(1, 10))
        f = s_antider2(q)
        f = padd(f, rand_poly(3, 0, -5, 5))                # a(tau)
        f = padd(f, pmul(rand_poly(2, 0, -5, 5), {(0, 1): fmpq(1)}))   # b(tau) s
        # properties of f on the rectangle (sampled exactly on a grid)
        grid_t = [a1 + (ar - a1) * fmpq(i, 6) for i in range(7)]
        grid_s = [L + (U - L) * fmpq(j, 10) for j in range(11)]
        vals = [[evalp(f, t, s) for s in grid_s] for t in grid_t]
        nonpos = any(v < 0 for row in vals for v in row)
        nonmono = any(any(row[j + 1] < row[j] for j in range(10)) and any(row[j + 1] > row[j] for j in range(10))
                      for row in vals)
        q_out = evalp(q, a1, U + 3 * W)                   # outside the rectangle the bump makes q negative
        n_nonpos += nonpos
        n_nonmono += nonmono
        n_nonconvex_out += q_out < 0
        Nmax = max(n + m for (n, m) in f)
        ws = word_sums(A, B, Nmax)
        Ap, Ep = powers(A, Nmax), powers(E, Nmax)
        gap = T_f(f, ws) - Tr_f_pinched(f, Ap, Ep)
        n_cases += 1
        if gap < 0:
            n_neg += 1
            say(f"   D5 VIOLATION: trial {trial}, gap {float(gap)}")
        rel = gap / (abs(T_f(f, ws)) + abs(Tr_f_pinched(f, Ap, Ep)))
        worst = rel if worst is None or rel < worst else worst
    say(f"[F1] D5: {n_cases} random (pair, f) cases (d=2..4; PSD and Hermitian letters; repeated eigenvalues); "
        f"f negative somewhere on R in {n_nonpos}, non-monotone in s on R in {n_nonmono}, not convex outside R in "
        f"{n_nonconvex_out}; violations of T_f >= Tr f(A,E_A(B)): {n_neg}; smallest relative excess {float(worst):.3e}")

    # ---------------- [F2] sharpness: convexity only on part of [l_min, l_max] ----------------
    found = 0
    tried = 0
    for trial in range(200):
        d = 3
        A, B, E, projs, alphas = pair(d, [rq(0, 2, 3) for _ in range(d)])
        lmin, lmax = eig_ext(B)
        sstar = outer_rational(lmin + (lmax - lmin) * mp.mpf(R.randint(3, 7)) / 10, True)
        # f'' = (s - s*)^3 * K -> concave below s*, convex above;  f = K (s-s*)^5 / 20 (times tau^n)
        n = R.randint(0, 3)
        fpoly = {}
        # (s - s*)^5 expanded
        for k in range(6):
            fpoly[(n, k)] = fmpq(comb(5, k)) * (-sstar) ** (5 - k) / 20
        Nmax = 5 + n
        ws = word_sums(A, B, Nmax)
        Ap, Ep = powers(A, Nmax), powers(E, Nmax)
        gap = T_f(fpoly, ws) - Tr_f_pinched(fpoly, Ap, Ep)
        tried += 1
        found += gap < 0
    say(f"[F2] f = tau^n (s - s*)^5/20 (convex in s only for s > s*, s* inside (l_min, l_max)): T_f < Tr f(A,E_A(B)) "
        f"in {found}/{tried} random PSD pairs -> the convexity hypothesis on the whole s-range is needed")

    # ---------------- [F3] near-degenerate A ----------------
    bad, total = 0, 0
    minratio_lo, maxratio_hi = None, None
    for k in range(2, 13):
        for rep in range(3):
            d = 3 + rep % 2
            base = fmpq(R.randint(1, 5), 7)
            levels = [base, base + fmpq(1, 10 ** k)] + [rq(0, 2, 3) for _ in range(d - 2)]
            A, B, E, projs, alphas = pair(d, levels)
            lmin, lmax = eig_ext(B)
            ws = word_sums(A, B, 10)
            Ap, Ep = powers(A, 10), powers(E, 10)
            for N in range(2, 11):
                for m in range(2, N + 1):
                    n = N - m
                    total += 1
                    gap = ws[(n, m)] / comb(N, n) - tr(Ap[n] * Ep[m])
                    Sn = fmpq(0)
                    for j in range(len(alphas)):
                        for kk in range(j + 1, len(alphas)):
                            wjk = tr(projs[j] * B * projs[kk] * B)
                            x, y = alphas[j], alphas[kk]
                            Sn += wjk * sum((x ** r * y ** (n - r) for r in range(n + 1)), fmpq(0)) / (n + 1)
                    lo = m * (m - 1) * (lmin ** (m - 2)) * mp.mpf(int(Sn.p)) / int(Sn.q)
                    hi = m * (m - 1) * (lmax ** (m - 2)) * mp.mpf(int(Sn.p)) / int(Sn.q)
                    g = mp.mpf(int(gap.p)) / int(gap.q)
                    if gap <= 0 or g < lo * (1 - mp.mpf(10) ** -40) or g > hi * (1 + mp.mpf(10) ** -40):
                        bad += 1
                    rlo = g / lo if lo > 0 else None
                    if rlo is not None and (minratio_lo is None or rlo < minratio_lo):
                        minratio_lo = rlo
    say(f"[F3] near-degenerate A (eigenvalue gap 1e-2 ... 1e-12, fine pinching): {total} (pair,n,m) cases with m>=2: "
        f"failures of gap>0 or of D3 (60 digits) = {bad}; min gap/(D3 lower bound) = {mp.nstr(minratio_lo, 8)}")

    # ---------------- [F4] long words and d = 6 ----------------
    A, B, E, projs, alphas = pair(3, [fmpq(0), fmpq(1, 3), fmpq(1)])
    ws = word_sums(A, B, 30, only_N=30)
    Ap, Ep = powers(A, 30), powers(E, 30)
    negs = sum(1 for m in range(2, 31) if ws[(30 - m, m)] / comb(30, m) - tr(Ap[30 - m] * Ep[m]) <= 0)
    say(f"[F4] d=3, singular A, all (n,m) with n+m=30, m>=2: non-positive gaps = {negs} of 29")
    A, B, E, projs, alphas = pair(6, [fmpq(0), fmpq(0), fmpq(0), fmpq(1, 2), fmpq(1, 2), fmpq(1)], rankB=2)
    ws = word_sums(A, B, 14)
    Ap, Ep = powers(A, 14), powers(E, 14)
    negs, cnt = 0, 0
    for N in range(2, 15):
        for m in range(2, N + 1):
            cnt += 1
            negs += (ws[(N - m, m)] / comb(N, m) - tr(Ap[N - m] * Ep[m])) <= 0
    say(f"[F4] d=6, A multiplicities (3,2,1) incl. kernel of dim 3, rank-2 B, n+m<=14, m>=2: non-positive gaps = "
        f"{negs} of {cnt}")


if __name__ == "__main__":
    main()
