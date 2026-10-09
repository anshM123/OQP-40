"""Independent check of the logical chain (F) => OQP 40 lower half, and of the conventions (internal check).

Formal part (exact, word level):
  * p_{n,m}(A,B) = p_{m,n}(B,A): the multiset of words is the same after renaming letters.
  * tr((A^{n/m}B)^m) = tr((A^{s}BA^{s})^m), s = n/2m, by cyclicity alone (checked as words with A^{n/m} = Z^2, Z = A^s).
Numerical part (mpmath, 40 digits, random complex PD A, B of sizes 2..6, incl. spread spectra):
  * p_{n,m}(A,B) - p_{m,n}(B,A) = 0;  tr((A^{n/m}B)^m) - tr((A^{n/2m}BA^{n/2m})^m) = 0;
  * substitution semantics: X = A^{1/ea} (PSD root) gives X^k = A^{k/ea};
  * ALT: phi(t) = tr((e^{tH/2} e^{tK} e^{tH/2})^{1/t}), H = n log A, K = m log B, is nondecreasing in t and
    phi(1/m) = tr((A^{n/m}B)^m), phi(t) -> tr e^{H+K} as t -> 0;
  * the chain p >= tr((A^{n/m}B)^m) >= tr exp(n log A + m log B) at (4,4), (3,4), (6,4), and the swapped
    statements at (4,3), (4,6): p_{4,3}(A,B) = p_{3,4}(B,A) >= tr((B^{3/4}A)^4) >= L_{4,3}(A,B).
"""
import itertools
import math
import os
import random
import sys
import time

import mpmath as mp

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from indep_core import cyc, poly_p  # noqa: E402

mp.mp.dps = 40


def herm_fun(Mh, fn):
    """f(M) for Hermitian M via eigendecomposition."""
    E, Q = mp.eigh(Mh)
    d = Mh.rows
    D = mp.zeros(d, d)
    for i in range(d):
        D[i, i] = fn(E[i])
    return Q * D * Q.transpose_conj()


def rand_unitary(d, rng):
    Z = mp.matrix(d, d)
    for i in range(d):
        for j in range(d):
            Z[i, j] = mp.mpc(rng.gauss(0, 1), rng.gauss(0, 1))
    Q, R = mp.qr(Z)
    for j in range(d):
        ph = R[j, j] / abs(R[j, j])
        for i in range(d):
            Q[i, j] *= ph
    return Q


def rand_pd(d, rng, spread):
    U = rand_unitary(d, rng)
    D = mp.zeros(d, d)
    for i in range(d):
        D[i, i] = mp.mpf(10) ** rng.uniform(-spread, spread)
    M = U * D * U.transpose_conj()
    return (M + M.transpose_conj()) / 2


def tr(M):
    return sum(M[i, i] for i in range(M.rows))


def mpow_int(M, k):
    out = mp.eye(M.rows)
    for _ in range(k):
        out = out * M
    return out


def p_val(A, B, n, m):
    """average of tr W over the C(n+m,n) words with n letters A and m letters B (prefix-memoized)."""
    memo = {'': mp.eye(A.rows)}

    def word(w):
        M = memo.get(w)
        if M is None:
            M = word(w[:-1]) * (A if w[-1] == 'A' else B)
            memo[w] = M
        return M
    tot = 0
    s = mp.mpc(0)
    for posA in itertools.combinations(range(n + m), n):
        S = set(posA)
        s += tr(word(''.join('A' if i in S else 'B' for i in range(n + m))))
        tot += 1
    assert tot == math.comb(n + m, n)
    return s / tot


def mat_pow(M, a):
    return herm_fun(M, lambda e: mp.power(e, a))


def main():
    logf = open(os.path.join(HERE, 'logs', 'indep_chain.log'), 'w')

    def log(s):
        print(s, flush=True)
        logf.write(s + '\n')
        logf.flush()
    log(f"# run {time.strftime('%Y-%m-%d %H:%M:%S')}, mpmath dps={mp.mp.dps}")
    # ---- formal checks
    for (n, m) in [(4, 4), (3, 4), (4, 3), (6, 4), (4, 6), (3, 3)]:
        a = poly_p(n, m, 1, 1)
        swapped = {cyc(k.translate(str.maketrans('xy', 'yx'))): v for k, v in poly_p(m, n, 1, 1).items()}
        assert a == swapped
    log("formal: p_{n,m}(A,B) = p_{m,n}(B,A) as polynomials (letter renaming) for (4,4),(3,4),(4,3),(6,4),(4,6),(3,3)")
    # (A^{n/m} B)^m with A^{n/m} = Z^2 vs (Z B Z)^m: same cyclic class
    for m in (2, 3, 4, 6):
        w1 = ('zz' + 'b') * m
        w2 = ('z' + 'b' + 'z') * m
        assert cyc(w1) == cyc(w2)
    log("formal: (Z^2 B)^m and (Z B Z)^m are cyclically equal words (m = 2,3,4,6), so tr((A^{n/m}B)^m) = "
        "tr((A^{n/2m} B A^{n/2m})^m) by cyclicity only")
    # ---- numerical checks
    rng = random.Random(4040)
    worst = dict(sym=0, conv=0, subst=0)
    alt_viol = 0
    chain_viol = 0
    n_samples = 0
    min_gap_F = mp.inf
    min_gap_L = mp.inf
    for d in (2, 3, 4, 5, 6):
        for spread in (0.5, 2, 4):
            A = rand_pd(d, rng, spread)
            B = rand_pd(d, rng, spread)
            logA = herm_fun(A, mp.log)
            logB = herm_fun(B, mp.log)
            for (n, m) in [(4, 4), (3, 4), (6, 4), (4, 3), (4, 6)]:
                n_samples += 1
                p = p_val(A, B, n, m)
                p_sw = p_val(B, A, m, n)
                worst['sym'] = max(worst['sym'], float(abs(p - p_sw) / abs(p)))
                Anm = mat_pow(A, mp.mpf(n) / m)
                F1 = tr(mpow_int(Anm * B, m))
                As = mat_pow(A, mp.mpf(n) / (2 * m))
                F2 = tr(mpow_int(As * B * As, m))
                worst['conv'] = max(worst['conv'], float(abs(F1 - F2) / abs(F1)))
                L = tr(herm_fun(n * logA + m * logB, mp.exp))
                # ALT monotonicity in t on a grid, and the endpoint t = 1/m
                H, K = n * logA, m * logB
                prev = None
                ts = [mp.mpf(1) / m * mp.mpf(2) ** (-j) for j in range(0, 12)][::-1]
                vals = []
                for t in ts:
                    eH = herm_fun(H, lambda e: mp.exp(t * e / 2))
                    eK = herm_fun(K, lambda e: mp.exp(t * e))
                    Mt = eH * eK * eH
                    Mt = (Mt + Mt.transpose_conj()) / 2
                    phi = tr(herm_fun(Mt, lambda e: mp.power(e, 1 / t)))
                    vals.append(phi)
                    if prev is not None and mp.re(phi) < mp.re(prev) * (1 - mp.mpf(10) ** -30):
                        alt_viol += 1
                    prev = phi
                if abs(vals[-1] - F1) > abs(F1) * mp.mpf(10) ** -25:
                    alt_viol += 1
                # chain
                if not (mp.re(p) >= mp.re(F1) * (1 - mp.mpf(10) ** -30) and mp.re(F1) >= mp.re(L) * (1 - mp.mpf(10) ** -30)):
                    chain_viol += 1
                min_gap_F = min(min_gap_F, mp.re(p - F1) / abs(p))
                min_gap_L = min(min_gap_L, mp.re(F1 - L) / abs(F1))
                if d == 3 and spread == 2:
                    log(f"  d={d} spread=1e+-{spread} (n,m)=({n},{m}): p={mp.nstr(mp.re(p), 12)} "
                        f"tr(A^(n/m)B)^m={mp.nstr(mp.re(F1), 12)} L={mp.nstr(mp.re(L), 12)}; "
                        f"phi(t) at t=1/m*2^-11..1/m: {mp.nstr(mp.re(vals[0]), 10)} ... {mp.nstr(mp.re(vals[-1]), 10)}")
            # substitution semantics: X = A^{1/4}; X^3 == A^{3/4}
            X = mat_pow(A, mp.mpf(1) / 4)
            err = mp.mnorm(mpow_int(X, 3) - mat_pow(A, mp.mpf(3) / 4), 1) / mp.mnorm(A, 1)
            X2 = mat_pow(A, mp.mpf(1) / 2)
            err2 = mp.mnorm(mpow_int(X2, 3) - mat_pow(A, mp.mpf(3) / 2), 1) / mp.mnorm(A, 1)
            worst['subst'] = max(worst['subst'], float(err), float(err2))
    log(f"numerical: {n_samples} (sample, (n,m)) pairs, d = 2..6, spreads 1e+-0.5 .. 1e+-4")
    log(f"  max rel |p_(n,m)(A,B) - p_(m,n)(B,A)| = {worst['sym']:.2e}")
    log(f"  max rel |tr((A^(n/m)B)^m) - tr((A^(n/2m)BA^(n/2m))^m)| = {worst['conv']:.2e}")
    log(f"  substitution: max rel ||X^3 - A^(3/4)|| (X = A^(1/4)) and ||X^3 - A^(3/2)|| (X = A^(1/2)) = {worst['subst']:.2e}")
    log(f"  ALT monotonicity / endpoint violations: {alt_viol}")
    log(f"  chain violations (p >= tr(A^(n/m)B)^m >= L): {chain_viol}; min (p-F)/p = {mp.nstr(min_gap_F, 6)}, "
        f"min (F-L)/F = {mp.nstr(min_gap_L, 6)}")


if __name__ == '__main__':
    main()
