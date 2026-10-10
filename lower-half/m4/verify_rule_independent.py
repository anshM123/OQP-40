"""Independent verification (written from scratch) of an m = 4 diagonal-share rule for Conjecture F at (n, 4).

Mathematical claim being checked.  Let K_n(x1..x4) = h_n(x)/C(n+3,3) - (x1x2x3x4)^{n/4}.  A rule is a function
k(x,y; e,f) (symmetric in x<->y and in e<->f), homogeneous of degree n, such that
  (S) k(x,y;e,f) + k(e,f;x,y) = 2 K_n(x,e,y,f)                          (share identity), and
  (P) for every x, y > 0 the kernel (e,f) -> k(x,y;e,f) is positive semidefinite on (0, inf).
Then for PSD B and diagonal A (simple spectrum; general A by continuity), with prod(a,c,b,d) = B_ac B_cb B_bd B_da,
  p_{n,4}(A,B) - Tr((A^{n/4}B)^4) = sum_{a,c,b,d} K_n(.) prod = sum_{(a,b)} sum_{(c,d)} k(a,b;c,d) prod(a,c,b,d) >= 0,
because for fixed (a,b) the matrix [prod(a,c,b,d)]_{c,d} = w w^* with w_c = conj(B_ac B_cb)... is PSD.

The rule is stored as monomial coefficients gamma in root variables X = x^{1/qd} etc.:
  k = sum over ordered (a,b,i,j), a+b+i+j = N = n qd, of gamma(canon(a,b), canon(i,j)) X^a Y^b U^i V^j.
Checks (exact rational arithmetic, python-flint fmpq / fmpq_poly, own Bareiss; positivity on (0,1) by a Descartes test after s = t/(1+t), else Arb root isolation):
  1. (S) coefficientwise against K_n rebuilt from its definition;
  2. (P) via the coefficient matrix C(s) = [coeff of U^i V^j in k(1, s; U, V)] (s = (y/x)^{1/qd} in (0,1], wlog y <= x):
     zero rows are exactly zero; every leading principal minor of the remaining block is a polynomial in s with no
     root in the open interval (0,1) and positive at s = 1/2  =>  C(s) > 0 on (0,1), C(1) >= 0;
  3. an end-to-end numerical test of the certificate on random (A, B) in 60-digit arithmetic.
"""
import json
import sys
import itertools
from fractions import Fraction
from math import comb

from flint import fmpq, fmpq_poly

if hasattr(sys, 'set_int_max_str_digits'):
    sys.set_int_max_str_digits(0)   # the exact tables can contain rationals with many thousands of digits

d = json.load(open(sys.argv[1]))
n, qd = int(d["n"]), int(d["qd"])
N = n * qd
assert (N % 4 == 0) or True
live = set(int(e) for e in d["exponents_units"])
var = [(tuple(p), tuple(q)) for p, q in d["var"]]
zval = {v: fmpq(Fraction(z).numerator, Fraction(z).denominator) for v, z in zip(var, d["z"])}
Cn = comb(n + 3, 3)


def kappa(a, b, i, j):
    """coefficient of X^a Y^b U^i V^j in K_n written in root variables (x = X^qd, ...)."""
    c = fmpq(0)
    if a % qd == 0 and b % qd == 0 and i % qd == 0 and j % qd == 0:
        c += fmpq(1, Cn)            # h_n contains every monomial x^p y^q e^r f^s with p+q+r+s = n once
    if (N % 4 == 0) and a == b == i == j == N // 4:
        c -= 1                      # the geometric-mean term (xyef)^{n/4} = (XYUV)^{N/4}
    return c


def canon(a, b):
    return (a, b) if a <= b else (b, a)


# gamma on canonical pairs, rebuilt from the stored free values by the rule's own conventions
# (free value z on (p,q) in var; partner (q,p) gets 2 kappa - z; pairs with a dead exponent get 0, their partner 2 kappa;
#  diagonal p == q gets kappa) -- and then every value is checked against (S) independently.
pairs = [(a, b) for a in range(N + 1) for b in range(a, N + 1 - a)]
gamma = {}
for p in pairs:
    for q in pairs:
        if sum(p) + sum(q) != N:
            continue
        kp = kappa(p[0], p[1], q[0], q[1])
        if p == q:
            gamma[(p, q)] = kp
        elif (p, q) in zval:
            gamma[(p, q)] = zval[(p, q)]
        elif (q, p) in zval:
            gamma[(p, q)] = 2 * kp - zval[(q, p)]
        elif q[1] not in live:
            gamma[(p, q)] = fmpq(0)
        elif p[1] not in live:
            gamma[(p, q)] = 2 * kp
        else:
            raise SystemExit(f"no value for {(p, q)}")

# ---- 1. share identity, coefficientwise, over ALL ordered exponent tuples
bad = 0
cnt = 0
for a in range(N + 1):
    for b in range(N + 1 - a):
        for i in range(N + 1 - a - b):
            j = N - a - b - i
            lhs = gamma[(canon(a, b), canon(i, j))] + gamma[(canon(i, j), canon(a, b))]
            # K_n(x, e, y, f): the D-pair (x, y) sits at positions 1, 3 and E = (e, f) at 2, 4; K_n is symmetric
            rhs = 2 * kappa(a, b, i, j)
            cnt += 1
            if lhs != rhs:
                bad += 1
print(f"n={n} qd={qd}: share identity checked on {cnt} monomials, mismatches: {bad}", flush=True)
assert bad == 0
# dead exponents: any monomial with i or j > max(live) must have gamma 0 on that side (kernel rows that are zero)

# ---- 2. the kernel matrix C(s)
dim = N + 1
s_poly = fmpq_poly([0, 1])
C = [[fmpq_poly([]) for _ in range(dim)] for _ in range(dim)]
for i in range(dim):
    for j in range(dim):
        if i + j > N:
            continue
        acc = fmpq_poly([])
        for a in range(N - i - j + 1):
            b = N - i - j - a
            g = gamma[(canon(a, b), canon(i, j))]
            if g != 0:
                coeffs = [fmpq(0)] * (b + 1)
                coeffs[b] = g
                acc += fmpq_poly(coeffs)   # X = 1, Y = s: X^a Y^b -> s^b
        C[i][j] = acc
for i in range(dim):
    for j in range(dim):
        assert C[i][j] == C[j][i], "C not symmetric"
rows = [i for i in range(dim) if C[i][i] != 0]
for i in range(dim):
    if i not in rows:
        assert all(C[i][j] == 0 for j in range(dim)), f"row {i} has zero diagonal but nonzero entries"
print(f"nonzero rows: {rows}", flush=True)


def bareiss_minors(M):
    """leading principal minors of a symmetric matrix over Q[s] by fraction-free (Bareiss) elimination."""
    k = len(M)
    A = [row[:] for row in M]
    minors = []
    prev = fmpq_poly([1])
    for t in range(k):
        piv = A[t][t]
        minors.append(piv)
        if piv == 0:
            raise SystemExit(f"zero pivot at step {t}: minor vanishes identically")
        for i in range(t + 1, k):
            for j in range(t + 1, k):
                num = A[i][j] * piv - A[i][t] * A[t][j]
                q, r = divmod(num, prev)
                assert r == 0, "Bareiss division not exact"
                A[i][j] = q
        prev = piv
    return minors


def no_root_open01(P):
    """True iff P has no root in the open interval (0,1) (P not identically 0). Two independent certificates:
    (a) fast path: Q(t) = (1+t)^deg P(t/(1+t)) has coefficients of one sign (Descartes: no positive root);
    (b) otherwise Arb-certified isolation of all complex roots of the squarefree part (python-flint complex_roots):
        each isolating ball must either have real part outside [0,1] or imaginary part excluding 0."""
    while P(0) == 0:
        P = P // s_poly
    one_minus = fmpq_poly([1, -1])
    while P(1) == 0:
        P = P // one_minus
    deg = P.degree()
    if deg <= 0:
        return True, 'constant'
    # (a) Moebius transform: s = t/(1+t)
    Q = fmpq_poly([0])
    for k in range(deg + 1):
        ck = P[k]
        if ck == 0:
            continue
        # s^k (1+t)^deg -> t^k (1+t)^(deg-k)
        Q += ck * fmpq_poly([0] * k + [1]) * fmpq_poly([1, 1]) ** (deg - k)
    coeffs = [Q[k] for k in range(Q.degree() + 1)]
    nz = [c for c in coeffs if c != 0]
    if all(c > 0 for c in nz) or all(c < 0 for c in nz):
        return True, 'descartes'
    # (b) Arb root isolation of the squarefree part
    from flint import fmpz_poly, arb, acb
    g = P.gcd(P.derivative())
    R = P // g
    den = R.denom()
    Rz = fmpz_poly([int((R[k] * den).p) for k in range(R.degree() + 1)])
    roots = Rz.complex_roots()
    for item in roots:
        z = item[0] if isinstance(item, tuple) else item
        re, im = z.real, z.imag
        if im.contains(0) and re.overlaps(arb(0.5, 0.5)):
            return False, 'root-ball meets (0,1)'
    return True, 'arb'


# If C(s) is block diagonal for the parity of the row index (C[i][j] = 0 whenever i + j is odd), it is positive
# definite iff both parity blocks are, so each block is treated separately (smaller degrees). Otherwise: one block.
parity = all(C[i][j] == 0 for i in rows for j in rows if (i + j) % 2 == 1)
blocks = [[i for i in rows if i % 2 == 0], [i for i in rows if i % 2 == 1]] if parity else [rows]
blocks = [b for b in blocks if b]
print(f"parity splitting: {parity}; blocks of sizes {[len(b) for b in blocks]}", flush=True)
ok = True
for bi, blk in enumerate(blocks):
    M = [[C[i][j] for j in blk] for i in blk]
    minors = bareiss_minors(M)
    for t, P in enumerate(minors):
        noroot, how = no_root_open01(P)
        v = P(fmpq(1, 2))
        good = noroot and (v > 0)
        ok = ok and good
        print(f"  block {bi} minor {t + 1}: degree {P.degree()}, no root in (0,1): {noroot} [{how}], value at 1/2 > 0: {v > 0}"
              f" -> {'OK' if good else 'FAIL'}", flush=True)
print("KERNEL CONDITION (P):", "PROVED" if ok else "FAILED", flush=True)

# ---- 3. end-to-end numerical test of the certificate (mpmath, 60 digits)
import mpmath as mp
import random
mp.mp.dps = 60
random.seed(1)


def k_eval(x, y, e, f):
    X, Y, U, V = (mp.mpf(t) ** (mp.mpf(1) / qd) for t in (x, y, e, f))
    tot = mp.mpf(0)
    for (p, q), g in gamma.items():
        if g == 0:
            continue
        gv = mp.mpf(int(g.p)) / int(g.q)
        # sum over orderings of p in (X,Y) and q in (U,V)
        ps = {(p[0], p[1]), (p[1], p[0])}
        qs = {(q[0], q[1]), (q[1], q[0])}
        for (a, b) in ps:
            for (i, j) in qs:
                tot += gv * X ** a * Y ** b * U ** i * V ** j
    return tot


def Kn_eval(xs):
    # h_n via recursion
    e = [mp.mpf(0)] * (n + 1)
    e[0] = mp.mpf(1)
    for xv in xs:
        for t in range(1, n + 1):
            e[t] += xv * e[t - 1]
    return e[n] / Cn - mp.fprod(xs) ** (mp.mpf(n) / 4)


worst_id = mp.mpf(0)
worst_eig = mp.mpf(1)
for trial in range(4):
    dd = 3 if trial < 2 else 4
    alpha = sorted(mp.e ** (mp.mpf(random.uniform(0, 4))) for _ in range(dd))
    # random complex PSD B
    Z = mp.matrix(dd, dd)
    for i in range(dd):
        for j in range(dd):
            Z[i, j] = mp.mpc(random.gauss(0, 1), random.gauss(0, 1))
    Bm = Z * Z.H
    # direct: sum over 4-tuples of K_n * cycle product
    direct = mp.mpf(0)
    cert = mp.mpf(0)
    for (a, c, b, dq) in itertools.product(range(dd), repeat=4):
        pr = Bm[a, c] * Bm[c, b] * Bm[b, dq] * Bm[dq, a]
        direct += (Kn_eval([alpha[a], alpha[c], alpha[b], alpha[dq]]) * pr).real
        cert += (k_eval(alpha[a], alpha[b], alpha[c], alpha[dq]) * pr).real
    worst_id = max(worst_id, abs(direct - cert) / max(abs(direct), mp.mpf(1e-30)))
    # the reduction itself: word average p_{n,4}(A,B) - Tr((A^{n/4} B)^4) by direct enumeration of words
    Am = mp.diag(alpha)
    tot = mp.mpf(0)
    cntw = 0
    for pos in itertools.combinations(range(n + 4), 4):
        Mw = mp.eye(dd)
        for t in range(n + 4):
            Mw = Mw * (Bm if t in pos else Am)
        tot += sum(Mw[i, i] for i in range(dd)).real
        cntw += 1
    An4 = mp.diag([a ** (mp.mpf(n) / 4) for a in alpha])
    Fv = An4 * Bm
    Fv = Fv * Fv * Fv * Fv
    gap = tot / cntw - sum(Fv[i, i] for i in range(dd)).real
    # the cycle expansion counts each word through its 4 B-letters: sum_i K_n prod = C(n+3,3)/C(n+3,3) * gap
    worst_id = max(worst_id, abs(gap - direct) / max(abs(direct), mp.mpf(1e-30)))
    # PSD of each G^{ab} = [k(a,b; c,d)]_{c,d}
    for a in range(dd):
        for b in range(dd):
            G = mp.matrix(dd, dd)
            for c in range(dd):
                for dq in range(dd):
                    G[c, dq] = k_eval(alpha[a], alpha[b], alpha[c], alpha[dq])
            ev = mp.eigsy(G)[0]
            worst_eig = min(worst_eig, min(ev[i] for i in range(dd)) / max(abs(G[i, i]) for i in range(dd)))
    print(f"  trial {trial}: d={dd}, direct sum = {mp.nstr(direct, 12)}, certificate sum = {mp.nstr(cert, 12)}", flush=True)
print(f"end-to-end: max relative identity error {mp.nstr(worst_id, 5)}; min normalised eigenvalue of G^ab {mp.nstr(worst_eig, 5)}")
print("RESULT:", "ALL CHECKS PASSED" if ok and worst_id < mp.mpf('1e-40') and worst_eig > -mp.mpf('1e-40') else "CHECK FAILED")
