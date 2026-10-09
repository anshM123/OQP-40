"""Exact rational checks of D1 (d = 2, closed form), D2, D3, D4 of DINH.md.

Independent code (does not import verify_dinh.py).

Exact arithmetic: python-flint fmpq / fmpq_mat. Complex Hermitian matrices are handled through the real
embedding X + iY -> [[X, -Y], [Y, X]] (products are preserved, traces double).

Construction of exact test pairs:
  - U rational orthogonal by the Cayley transform U = (I - S)(I + S)^{-1}, S rational skew-symmetric;
  - A = U diag(levels) U^T with rational levels (repeated levels allowed, zero allowed), spectral
    projections Q_k = U_k U_k^T exact;
  - B = X X^T with rational X of chosen rank (PSD), or a rational symmetric indefinite matrix.

Word sums: S_{n,m} = sum over all words with n letters A and m letters B of Tr W is the trace of the t^m
coefficient of (A + tB)^{n+m}; checked against brute-force enumeration of all words for n + m <= 8.

D1 for d = 2 (closed form derived in REPORT.md (this folder's report), Section 4): in the eigenbasis of A = diag(a1, a2),
a1 < a2, with B = [[b11, b], [conj b, b22]], the density rho_{B,A}(., tau) is, for a1 < tau < a2, a semicircle
in s with centre c(tau) = (b11 (a2 - tau) + b22 (tau - a1)) / (a2 - a1), squared radius
R^2 = 4 (tau - a1)(a2 - tau)|b|^2 / (a2 - a1)^2 and mass |b|^2 / (a2 - a1). Hence
   int int s^k tau^n rho = |b|^2/(a2-a1) int_{a1}^{a2} tau^n sum_j C(k,2j) Cat_j c^{k-2j} (R^2/4)^j dtau,
a rational number. D1 then is an exact rational identity.
"""
import itertools
import random
import sys
from math import comb

import flint
import mpmath as mp
from flint import fmpq, fmpq_mat, fmpq_poly

mp.mp.dps = 60
R = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 12345)
Q = lambda p, q=1: fmpq(p, q)


def eye(d):
    return fmpq_mat(d, d, [1 if i == j else 0 for i in range(d) for j in range(d)])


def zero(d):
    return fmpq_mat(d, d, [0] * (d * d))


def tr(M):
    s = fmpq(0)
    for i in range(M.nrows()):
        s += M[i, i]
    return s


def is_zero(M):
    return all(M[i, j] == 0 for i in range(M.nrows()) for j in range(M.ncols()))


def rand_q(lo=-3, hi=3, den=(1, 2, 3, 4, 5)):
    return fmpq(R.randint(lo * 6, hi * 6), R.choice(den) * 6)


def cayley(S):
    d = S.nrows()
    return (eye(d) - S) * (eye(d) + S).inv()


def rand_skew(d):
    S = zero(d)
    for i in range(d):
        for j in range(i + 1, d):
            v = rand_q(-2, 2)
            S[i, j] = v
            S[j, i] = -v
    return S


def embed(X, Y):
    """real embedding of X + iY (X, Y real d x d) as a 2d x 2d real matrix"""
    d = X.nrows()
    M = zero(2 * d)
    for i in range(d):
        for j in range(d):
            M[i, j] = X[i, j]
            M[i, j + d] = -Y[i, j]
            M[i + d, j] = Y[i, j]
            M[i + d, j + d] = X[i, j]
    return M


def make_pair(d, levels, rankB, complex_=False, indefinite_B=False, levels_sign_free=False):
    """Return (A, B, projs, alphas, U, dim) with exact rationals; for complex_ the matrices are the real
    embeddings (dimension 2d) of complex Hermitian d x d matrices."""
    levels = [fmpq(x) if not isinstance(x, fmpq) else x for x in levels]
    alphas = sorted(set(levels))
    if not complex_:
        S = rand_skew(d)
        U = cayley(S)
        D = zero(d)
        for i, l in enumerate(levels):
            D[i, i] = l
        A = U * D * U.transpose()
        projs = []
        for a in alphas:
            idx = [i for i, l in enumerate(levels) if l == a]
            Uk = fmpq_mat(d, len(idx), [U[r, c] for r in range(d) for c in idx])
            projs.append(Uk * Uk.transpose())
        if indefinite_B:
            Bm = zero(d)
            for i in range(d):
                for j in range(i, d):
                    v = rand_q(-2, 2)
                    Bm[i, j] = v
                    Bm[j, i] = v
        else:
            X = fmpq_mat(d, rankB, [rand_q(-2, 2) for _ in range(d * rankB)])
            Bm = X * X.transpose()
        return A, Bm, projs, alphas, U, d
    # complex Hermitian through the real embedding
    Xs = rand_skew(d)
    Ys = zero(d)
    for i in range(d):
        for j in range(i, d):
            v = rand_q(-2, 2)
            Ys[i, j] = v
            Ys[j, i] = v
    Sphi = embed(Xs, Ys)            # embedding of an anti-Hermitian matrix: skew-symmetric
    U = cayley(Sphi)                # embedding of a unitary
    dd = 2 * d
    D = zero(dd)
    for i, l in enumerate(levels):
        D[i, i] = l
        D[i + d, i + d] = l
    A = U * D * U.transpose()
    projs = []
    for a in alphas:
        idx = [i for i, l in enumerate(levels) if l == a]
        idx = idx + [i + d for i in idx]
        Uk = fmpq_mat(dd, len(idx), [U[r, c] for r in range(dd) for c in idx])
        projs.append(Uk * Uk.transpose())
    if indefinite_B:
        Xb, Yb = zero(d), zero(d)
        for i in range(d):
            for j in range(i, d):
                v = rand_q(-2, 2)
                Xb[i, j] = v
                Xb[j, i] = v
                if i != j:
                    w = rand_q(-2, 2)
                    Yb[i, j] = w
                    Yb[j, i] = -w
        Bm = embed(Xb, Yb)
    else:
        Zr = fmpq_mat(d, rankB, [rand_q(-2, 2) for _ in range(d * rankB)])
        Zi = fmpq_mat(d, rankB, [rand_q(-2, 2) for _ in range(d * rankB)])
        Zphi = fmpq_mat(dd, 2 * rankB, [0] * (dd * 2 * rankB))
        for i in range(d):
            for j in range(rankB):
                Zphi[i, j] = Zr[i, j]
                Zphi[i, j + rankB] = -Zi[i, j]
                Zphi[i + d, j] = Zi[i, j]
                Zphi[i + d, j + rankB] = Zr[i, j]
        Bm = Zphi * Zphi.transpose()
    return A, Bm, projs, alphas, U, dd


def word_sums(A, B, Nmax):
    """ws[(n,m)] = sum over words with n A's and m B's of Tr W, for n + m <= Nmax"""
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
        for m in range(N + 1):
            ws[(N - m, m)] = tr(coeffs[m])
    return ws


def word_sum_brute(A, B, n, m):
    tot = fmpq(0)
    d = A.nrows()
    for pos in itertools.combinations(range(n + m), m):
        W = eye(d)
        for i in range(n + m):
            W = W * (B if i in pos else A)
        tot += tr(W)
    return tot


def mpow(M, k):
    P = eye(M.nrows())
    for _ in range(k):
        P = P * M
    return P


def hbar(n, x, y):
    return sum((x ** r * y ** (n - r) for r in range(n + 1)), fmpq(0)) / (n + 1)


def eig_extremes(Bm):
    M = mp.matrix([[mp.mpf(int(Bm[i, j].p)) / int(Bm[i, j].q) for j in range(Bm.ncols())] for i in range(Bm.nrows())])
    ev = sorted(mp.eigsy(M)[0])
    return ev[0], ev[-1]


def to_mp(q):
    return mp.mpf(int(q.p)) / int(q.q)


def catalan(j):
    return comb(2 * j, j) // (j + 1)


def d2_rho_moment(a1, a2, b11, b22, babs2, k, n):
    """exact int int s^k tau^n rho_{B,A} for d = 2 (semicircle closed form); all inputs fmpq"""
    L = a2 - a1
    t = fmpq_poly([0, 1])
    c = (b11 * (fmpq_poly([a2]) - t) + b22 * (t - fmpq_poly([a1]))) * (1 / L)
    r2q = (t - fmpq_poly([a1])) * (fmpq_poly([a2]) - t) * (babs2 / (L * L))      # = R^2 / 4
    integrand = fmpq_poly([0])
    for j in range(k // 2 + 1):
        term = c ** (k - 2 * j) * r2q ** j * (comb(k, 2 * j) * catalan(j))
        integrand += term
    integrand = integrand * t ** n
    P = integrand.integral()
    return (babs2 / L) * (P(a2) - P(a1))


def main():
    log = []
    say = lambda s: (print(s), log.append(s), sys.stdout.flush())

    # ---- [E0] word recursion vs brute force -------------------------------------------------------------
    worst = 0
    for trial in range(12):
        d = R.randint(2, 4)
        levels = [Q(R.randint(0, 4), 2) for _ in range(d)]
        A, Bm, projs, alphas, U, dd = make_pair(d, levels, R.randint(1, d), complex_=(trial % 3 == 0))
        ws = word_sums(A, Bm, 8)
        for n in range(0, 5):
            for m in range(0, 9 - n):
                if ws[(n, m)] != word_sum_brute(A, Bm, n, m):
                    worst += 1
    say(f"[E0] recursion vs brute-force enumeration of words (n+m<=8, 12 pairs incl. complex): mismatches = {worst}")

    # ---- [E1] D1 for d = 2, exact (real and complex, PSD and indefinite, singular A, rank-one B) -------------
    n_id, n_bad = 0, 0
    for trial in range(60):
        complex_ = trial % 2 == 1
        kind = trial % 6
        if kind == 0:
            levels = [Q(0), Q(R.randint(1, 5), 3)]               # singular A
        elif kind == 1:
            levels = [Q(-R.randint(1, 5), 3), Q(R.randint(1, 5), 2)]  # indefinite A
        else:
            a = R.randint(0, 6)
            levels = [Q(a, 4), Q(a + R.randint(1, 6), 4)]
        rankB = 1 if kind in (0, 3) else 2
        indef = kind in (1, 4)
        A, Bm, projs, alphas, U, dd = make_pair(2, levels, rankB, complex_=complex_, indefinite_B=indef)
        ws = word_sums(A, Bm, 14)
        # eigenbasis entries of B
        Bp = U.transpose() * Bm * U
        if not complex_:
            b11, b22, babs2 = Bp[0, 0], Bp[1, 1], Bp[0, 1] ** 2
        else:
            b11, b22 = Bp[0, 0], Bp[1, 1]
            babs2 = Bp[0, 1] ** 2 + Bp[2, 1] ** 2              # X12^2 + Y12^2 (Y = lower-left block)
        a1, a2 = alphas
        E = sum((P * Bm * P for P in projs), zero(dd))
        fac = 2 if complex_ else 1                               # real embedding doubles traces
        for N in range(0, 15):
            for m in range(0, N + 1):
                n = N - m
                gap = ws[(n, m)] / comb(N, n) - tr(mpow(A, n) * mpow(E, m))
                rhs = (m * (m - 1) * d2_rho_moment(a1, a2, b11, b22, babs2, m - 2, n) * fac) if m >= 2 else fmpq(0)
                n_id += 1
                if gap != rhs:
                    n_bad += 1
                    if n_bad < 5:
                        say(f"   MISMATCH d=2 trial {trial} (n,m)=({n},{m}): gap={gap} rhs={rhs}")
    say(f"[E1] D1 exact for d=2 (semicircle closed form), 60 pairs, 0<=n+m<=14: {n_id} identities, {n_bad} mismatches")

    # ---- [E2] D2/D3 exact: PSD A, B, many structures, d = 2..5, 0 <= n + m <= 12 --------------------------
    configs = []
    for d in (2, 3, 4, 5):
        configs += [
            (d, "generic", lambda d: [Q(R.randint(1, 9), 3) for _ in range(d)], d, False),
            (d, "singular A", lambda d: [Q(0)] + [Q(R.randint(1, 9), 3) for _ in range(d - 1)], d, False),
            (d, "rank-one B", lambda d: [Q(R.randint(0, 9), 3) for _ in range(d)], 1, False),
            (d, "repeated eig", lambda d: [Q(1, 2)] * 2 + [Q(R.randint(2, 9), 3) for _ in range(d - 2)], d, False),
            (d, "scalar A", lambda d: [Q(2, 3)] * d, d, False),
            (d, "singular A, singular B", lambda d: [Q(0)] * (d - 1) + [Q(1)], max(1, d - 1), False),
            (d, "complex generic", lambda d: [Q(R.randint(0, 9), 3) for _ in range(d)], d, True),
            (d, "complex rank-one B, repeated", lambda d: [Q(1, 3)] * (d - 1) + [Q(2)], 1, True),
        ]
    stats = dict(cases=0, neg=0, strict_bad=0, d3_bad=0, m2_bad=0, min_rel=None)
    Nmax = 12
    for (d, name, levf, rankB, cplx) in configs:
        if cplx and d > 4:
            continue
        for rep in range(3):
            levels = levf(d)
            A, Bm, projs, alphas, U, dd = make_pair(d, levels, min(rankB, d), complex_=cplx)
            ws = word_sums(A, Bm, Nmax)
            E = sum((P * Bm * P for P in projs), zero(dd))
            commute = is_zero(A * Bm - Bm * A)
            fac = 2 if cplx else 1
            w = {}
            for j in range(len(alphas)):
                for k in range(j + 1, len(alphas)):
                    w[(j, k)] = tr(projs[j] * Bm * projs[k] * Bm) / fac
            lmin, lmax = eig_extremes(Bm)
            Apow = [eye(dd)]
            Epow = [eye(dd)]
            for _ in range(Nmax):
                Apow.append(Apow[-1] * A)
                Epow.append(Epow[-1] * E)
            for N in range(0, Nmax + 1):
                for m in range(0, N + 1):
                    n = N - m
                    gap = (ws[(n, m)] / comb(N, n) - tr(Apow[n] * Epow[m])) / fac
                    stats["cases"] += 1
                    if gap < 0:
                        stats["neg"] += 1
                        say(f"   NEGATIVE GAP: d={d} {name} (n,m)=({n},{m}) gap={gap}")
                    if m >= 2:
                        if (gap > 0) == commute:          # strict iff non-commuting
                            stats["strict_bad"] += 1
                            say(f"   STRICTNESS FAILS: d={d} {name} (n,m)=({n},{m}) gap={gap} commute={commute}")
                        Sn = sum((wjk * hbar(n, alphas[j], alphas[k]) for (j, k), wjk in w.items()), fmpq(0))
                        if m == 2:
                            if gap != 2 * Sn:
                                stats["m2_bad"] += 1
                                say(f"   m=2 EQUALITY FAILS: d={d} {name} n={n}: gap={gap} 2S_n={2*Sn}")
                        lo = m * (m - 1) * (lmin ** (m - 2) if m > 2 else 1) * to_mp(Sn)
                        hi = m * (m - 1) * (lmax ** (m - 2) if m > 2 else 1) * to_mp(Sn)
                        g = to_mp(gap)
                        tol = mp.mpf(10) ** (-45) * (abs(hi) + 1)
                        if g < lo - tol or g > hi + tol:
                            stats["d3_bad"] += 1
                            say(f"   D3 FAILS: d={d} {name} (n,m)=({n},{m}) lo={mp.nstr(lo,12)} gap={mp.nstr(g,12)} hi={mp.nstr(hi,12)}")
                    if gap != 0:
                        scale = abs(ws[(n, m)] / comb(N, n)) / fac
                        rel = gap / scale if scale != 0 else None
                        if rel is not None and (stats["min_rel"] is None or rel < stats["min_rel"]):
                            stats["min_rel"] = rel
    say(f"[E2] D2/D3 exact over {stats['cases']} (pair,n,m) cases (d=2..5, real and complex, structures: generic, "
        f"singular A, rank-one B, repeated eigenvalue, scalar A, singular A and B): negative gaps = {stats['neg']}, "
        f"strictness-iff-noncommuting failures = {stats['strict_bad']}, m=2 equality failures = {stats['m2_bad']}, "
        f"D3 bound failures (60-digit l_min/l_max) = {stats['d3_bad']}; smallest nonzero relative gap = "
        f"{float(stats['min_rel']) if stats['min_rel'] is not None else None:.3e}")

    # ---- [E3] D4 exact: Hermitian letters under the sign conditions; and failures without them ---------------
    cnt = dict(ee=0, ee_bad=0, Am=0, Am_bad=0, Bn=0, Bn_bad=0, odd=0, odd_neg=0, Aodd=0, Aodd_neg=0)
    for trial in range(40):
        d = R.randint(2, 4)
        # (i) both even, both indefinite
        levels = [Q(R.randint(-6, 6), 3) for _ in range(d)]
        A, Bm, projs, alphas, U, dd = make_pair(d, levels, d, indefinite_B=True)
        ws = word_sums(A, Bm, 10)
        E = sum((P * Bm * P for P in projs), zero(dd))
        for n in range(0, 11, 2):
            for m in range(0, 11 - n, 2):
                gap = ws[(n, m)] / comb(n + m, n) - tr(mpow(A, n) * mpow(E, m))
                cnt["ee"] += 1
                cnt["ee_bad"] += gap < 0
        # (ii) A >= 0, B indefinite, m even, n arbitrary ; and m odd (expect failures)
        levels = [Q(R.randint(0, 6), 3) for _ in range(d)]
        A, Bm, projs, alphas, U, dd = make_pair(d, levels, d, indefinite_B=True)
        ws = word_sums(A, Bm, 10)
        E = sum((P * Bm * P for P in projs), zero(dd))
        for n in range(0, 11):
            for m in range(0, 11 - n):
                gap = ws[(n, m)] / comb(n + m, n) - tr(mpow(A, n) * mpow(E, m))
                if m % 2 == 0:
                    cnt["Am"] += 1
                    cnt["Am_bad"] += gap < 0
                elif m >= 3:
                    cnt["Aodd"] += 1
                    cnt["Aodd_neg"] += gap < 0
        # (iii) B >= 0, A indefinite, n even
        levels = [Q(R.randint(-6, 6), 3) for _ in range(d)]
        A, Bm, projs, alphas, U, dd = make_pair(d, levels, d, indefinite_B=False)
        ws = word_sums(A, Bm, 10)
        E = sum((P * Bm * P for P in projs), zero(dd))
        for n in range(0, 11, 2):
            for m in range(0, 11 - n):
                gap = ws[(n, m)] / comb(n + m, n) - tr(mpow(A, n) * mpow(E, m))
                cnt["Bn"] += 1
                cnt["Bn_bad"] += gap < 0
        # (iv) (n,m) = (1,3) fully indefinite
        levels = [Q(R.randint(-6, 6), 3) for _ in range(3)]
        A, Bm, projs, alphas, U, dd = make_pair(3, levels, 3, indefinite_B=True)
        ws = word_sums(A, Bm, 4)
        E = sum((P * Bm * P for P in projs), zero(dd))
        gap = ws[(1, 3)] / 4 - tr(A * mpow(E, 3))
        cnt["odd"] += 1
        cnt["odd_neg"] += gap < 0
    say(f"[E3] D4 exact: (n,m both even, A,B indefinite) {cnt['ee']} cases, negative {cnt['ee_bad']}; "
        f"(A>=0, m even) {cnt['Am']} cases, negative {cnt['Am_bad']}; (B>=0, n even) {cnt['Bn']} cases, negative "
        f"{cnt['Bn_bad']}. Without sign condition: (A>=0, B indefinite, m odd >= 3) negative in {cnt['Aodd_neg']}/{cnt['Aodd']}; "
        f"(n,m)=(1,3) both indefinite: negative in {cnt['odd_neg']}/{cnt['odd']}")
    return log


if __name__ == "__main__":
    main()
