"""From a numerical polynomial rule z (polyrule_sos.py) to an EXACT rational rule with a rigorous proof that
C(s) is positive definite for 0 < s < 1 (hence PSD on [0,1], hence the rule is valid).

Steps
 1. exact affine structure: C(s) = sum_k s^k (C0[k] + sum_v z_v Cv[k][v]) with rational C0, Cv;
 2. structural constraints (linear in z) at the degenerate endpoints s = 0 and s = 1, found numerically from the
    solution and imposed EXACTLY (their only role is to make the rounding succeed; the final check is independent);
 3. rounding of z to rationals and exact projection onto the constraints;
 4. exact leading principal minors of C(s) (Bareiss over Q[s]) and a rigorous Descartes/bisection test that each
    is > 0 on (0,1).
Usage: python exact_rule.py n qd sol.npz [denominator_bits] [out.json]"""
import json
import sys
import time
from fractions import Fraction

import numpy as np
import flint

from polyrule import Setup
from exactcheck import bareiss_minors, positive_on_open01

n, qd, solfile = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
dbits = int(sys.argv[4]) if len(sys.argv) > 4 else 40
outjson = sys.argv[5] if len(sys.argv) > 5 else None
S = Setup(n, qd, 0, n * qd)
E = S.E
m = len(E)
nv = len(S.var)
N = S.N
D = N
zf = np.load(solfile)["z"]
print(f"n={n} qd={qd} m={m} nv={nv} D={D}", flush=True)

# ---------- 1. exact affine structure ----------
C0 = [[[Fraction(0)] * m for _ in range(m)] for _ in range(D + 1)]
Cv = {}   # (k, i, j) -> {v: coeff}
for ii, i in enumerate(E):
    for jj, j in enumerate(E):
        if jj < ii:
            continue
        ij = (i, j)
        for (a, b) in S.pairs_by_sum.get(N - i - j, []):
            key = ((a, b), ij)
            pw = [a, b] if a != b else [a]
            for pp in pw:
                for (r_, c_) in {(ii, jj), (jj, ii)}:
                    if key in S.fixed:
                        if (a, b) == ij:
                            val = S.kappa((a, b), ij, exact=True)
                        elif ij[1] not in S.live:
                            val = Fraction(0)
                        else:
                            val = 2 * S.kappa((a, b), ij, exact=True) if S.fixed[key] != 0.0 or True else 0
                            # fixed entries are either gamma(p;p) = kappa, 0 (dead kernel side), or 2 kappa
                            val = Fraction(S.fixed[key]).limit_denominator(10 ** 12)
                            val = _ = val
                        C0[pp][r_][c_] += val
                    elif key in S.vidx:
                        Cv.setdefault((pp, r_, c_), {})
                        Cv[(pp, r_, c_)][S.vidx[key]] = Cv[(pp, r_, c_)].get(S.vidx[key], 0) + 1
                    else:
                        C0[pp][r_][c_] += 2 * S.kappa((a, b), ij, exact=True)
                        v = S.vidx[(ij, (a, b))]
                        Cv.setdefault((pp, r_, c_), {})
                        Cv[(pp, r_, c_)][v] = Cv[(pp, r_, c_)].get(v, 0) - 1


def fixed_exact(key):
    p, q = key
    if p == q:
        return S.kappa(p, q, exact=True)
    if q[1] not in S.live:
        return Fraction(0)
    return 2 * S.kappa(p, q, exact=True)


# rebuild C0 with exact fixed values (avoid any float -> Fraction conversion)
C0 = [[[Fraction(0)] * m for _ in range(m)] for _ in range(D + 1)]
for ii, i in enumerate(E):
    for jj, j in enumerate(E):
        if jj < ii:
            continue
        ij = (i, j)
        for (a, b) in S.pairs_by_sum.get(N - i - j, []):
            key = ((a, b), ij)
            pw = [a, b] if a != b else [a]
            for pp in pw:
                for (r_, c_) in {(ii, jj), (jj, ii)}:
                    if key in S.fixed:
                        C0[pp][r_][c_] += fixed_exact(key)
                    elif key not in S.vidx:
                        C0[pp][r_][c_] += 2 * S.kappa((a, b), ij, exact=True)


def C_coef_num(z, k):
    M = np.array([[float(C0[k][i][j]) for j in range(m)] for i in range(m)])
    for i in range(m):
        for j in range(m):
            for v, c in Cv.get((k, i, j), {}).items():
                M[i, j] += c * z[v]
    return M


def C_num(z, s):
    return sum(s ** k * C_coef_num(z, k) for k in range(D + 1))


# ---------- 2. structural constraints ----------
def rationalize_basis(B, maxden=24):
    """B: m x k numerical basis of a subspace. Return a rational basis (list of Fraction vectors) via RREF+rounding."""
    import sympy
    k = B.shape[1]
    # RREF numerically
    A = B.T.copy()
    piv = []
    r = 0
    for c in range(m):
        if r == k:
            break
        p = np.argmax(np.abs(A[r:, c])) + r
        if abs(A[p, c]) < 1e-6:
            continue
        A[[r, p]] = A[[p, r]]
        A[r] /= A[r, c]
        for rr in range(k):
            if rr != r:
                A[rr] -= A[rr, c] * A[r]
        piv.append(c)
        r += 1
    vecs = []
    for row in A[:r]:
        vecs.append([Fraction(float(x)).limit_denominator(maxden) for x in row])
    return vecs


def endpoint_constraints(z, at_one, tol=1e-7):
    """Return list of (k, w1, w2) meaning: coefficient of u^k (u = s or 1-s) in w1^T C w2 must vanish, plus the
    transformed basis description, from the numerical solution."""
    # Taylor coefficients in u
    coefs = []
    if not at_one:
        coefs = [C_coef_num(z, k) for k in range(D + 1)]
    else:
        # C(1-u) = sum_k C_k (1-u)^k -> coefficients in u
        from math import comb
        Ck = [C_coef_num(z, k) for k in range(D + 1)]
        for p in range(D + 1):
            coefs.append(sum(Ck[k] * comb(k, p) * (-1) ** p for k in range(p, D + 1)))
    scale = max(np.abs(c).max() for c in coefs)
    M0 = coefs[0]
    ev, V = np.linalg.eigh(M0)
    ker = V[:, ev < tol * max(1.0, ev.max())]
    # exact forced kernels (see LOG): s = 1: v(1), v(-1) (qd even); s = 0: e_i (i < N/4, i != 0 mod qd) and
    # e_i - e_0 (i < N/4, i = 0 mod qd, i > 0)
    if at_one:
        kv = [[Fraction(1)] * m]
        if qd % 2 == 0:
            kv = [[Fraction(1 - (E[t] % 2)) for t in range(m)], [Fraction(E[t] % 2) for t in range(m)]]
    else:
        kv = []
        for t in range(m):
            i = E[t]
            if 4 * i < N and i % qd != 0:
                kv.append([Fraction(int(u == t)) for u in range(m)])
            if 4 * i < N and i % qd == 0 and i > 0:
                kv.append([Fraction(int(u == t)) - Fraction(int(u == 0)) for u in range(m)])
    if ker.shape[1] != len(kv):
        print(f"   WARNING endpoint {'1' if at_one else '0'}: numerical kernel dim {ker.shape[1]} != forced {len(kv)}")
    # complete to a basis with coordinate vectors
    T = [list(v) for v in kv]
    Tm = np.array([[float(x) for x in v] for v in T]).T if T else np.zeros((m, 0))
    for c in range(m):
        if len(T) == m:
            break
        cand = np.zeros(m); cand[c] = 1
        test = np.column_stack([Tm, cand]) if Tm.size else cand.reshape(-1, 1)
        if np.linalg.matrix_rank(test, tol=1e-9) > (Tm.shape[1] if Tm.size else 0):
            T.append([Fraction(int(x == c)) for x in range(m)])
            Tm = test
    Tf = np.array([[float(x) for x in v] for v in T]).T   # columns
    print("   endpoint", "1" if at_one else "0", "kernel eigenvalues", np.round(ev[ev < tol * max(1.0, ev.max())], 12),
          "rational kernel basis", [[str(x) for x in v] for v in kv])
    for a in range(len(kv)):
        w = Tf[:, a]
        print("     w^T C_k w for k=0..3:", [float(w @ coefs[k] @ w) for k in range(4)])
    # orders of the diagonal in the new basis
    orders = []
    for a in range(m):
        w = Tf[:, a]
        o = None
        for k, c in enumerate(coefs):
            if abs(w @ c @ w) > 1e-6 * max(1.0, np.abs(M0).max()):
                o = k
                break
        orders.append(o if o is not None else D + 1)
    if at_one:
        # only C(1) w = 0 is imposed at s = 1 (the u^1 conditions then hold exactly by the x <-> y congruence)
        orders = [2 if a < len(kv) else 0 for a in range(m)]
        cons = []
        for a in range(len(kv)):
            for b in range(m):
                cons.append((0, T[a], T[b]))
        return cons, orders, len(kv)
    saved = np.load(solfile)
    if "orders" in saved.files:
        orders = [int(o) for o in saved["orders"]]
    cons = []
    for a in range(m):
        for b in range(a, m):
            lim = (orders[a] + orders[b]) / 2
            for k in range(D + 1):
                if k < lim:
                    cons.append((k, T[a], T[b]))
    return cons, orders, len(kv)


cons0, ord0, k0 = endpoint_constraints(zf, at_one=False)
cons1, ord1, k1 = endpoint_constraints(zf, at_one=True)
print(f"s=0: kernel dim {k0}, orders {ord0}, {len(cons0)} coefficient conditions", flush=True)
print(f"s=1: kernel dim {k1}, orders {ord1}, {len(cons1)} coefficient conditions", flush=True)


def constraint_rows(cons, at_one):
    """each condition: coefficient of u^k of w1^T C(s) w2 = 0, as (row over z, rhs) in exact rationals."""
    from math import comb
    rows = []
    for (k, w1, w2) in cons:
        # coefficient of u^k: at_one -> sum_{K>=k} C_K comb(K,k)(-1)^k ; else C_k
        Ks = range(k, D + 1) if at_one else [k]
        row = {}
        rhs = Fraction(0)
        for K in Ks:
            fac = Fraction(comb(K, k) * (-1) ** k) if at_one else Fraction(1)
            for i in range(m):
                if w1[i] == 0:
                    continue
                for j in range(m):
                    if w2[j] == 0:
                        continue
                    f = fac * w1[i] * w2[j]
                    rhs -= f * C0[K][i][j]
                    for v, c in Cv.get((K, i, j), {}).items():
                        row[v] = row.get(v, 0) + f * c
        rows.append((row, rhs))
    return rows


rows = constraint_rows(cons0, False) + constraint_rows(cons1, True)
import os as _os0
if _os0.environ.get("PARITY", "1") == "1":
    # parity reduction (see LOG.md): gamma = 0 on classes with a + b odd
    for v, (p, q_) in enumerate(S.var):
        if (p[0] + p[1]) % 2 == 1:
            rows.append(({v: Fraction(1)}, Fraction(0)))
# drop trivial rows (structurally 0 = 0)
rows = [(r, b) for (r, b) in rows if any(v != 0 for v in r.values()) or b != 0]
bad = [(r, b) for (r, b) in rows if not any(v != 0 for v in r.values()) and b != 0]
if bad:
    print("INCONSISTENT structural condition (0 = nonzero): the numerical structure guess is wrong", flush=True)
    sys.exit(1)
print(f"{len(rows)} nontrivial exact linear constraints", flush=True)

# ---------- 3. round and project exactly ----------
import os as _osr
if _osr.environ.get("COMDEN"):
    # round every entry to a multiple of 1/(COMDEN * C(n+3,3)) (small common denominator)
    from math import comb as _comb
    _D0 = int(_osr.environ["COMDEN"]) * _comb(n + 3, 3)
    zr = [Fraction(round(float(x) * _D0), _D0) for x in zf]
else:
    zr = [Fraction(float(x)).limit_denominator(2 ** dbits) for x in zf]
L = flint.fmpq_mat(len(rows), nv) if rows else None
bvec = []
for t_, (r, b) in enumerate(rows):
    for v, c in r.items():
        L[t_, v] = flint.fmpq(c.numerator, c.denominator)
    bvec.append(b)
if rows:
    # residual
    res = []
    for t_, (r, b) in enumerate(rows):
        res.append(b - sum(c * zr[v] for v, c in r.items()))
    maxres = max(abs(float(x)) for x in res)
    print(f"max residual of rounded z in the constraints: {maxres:.2e}", flush=True)
    import os as _os
if rows and _os.environ.get("PROJ", "rref") == "rref":
    # RREF projection: free variables keep their rounded values, pivot variables are solved exactly
    Maug = flint.fmpq_mat(len(rows), nv + 1)
    for t_, (r, b) in enumerate(rows):
        for v, c in r.items():
            Maug[t_, v] = flint.fmpq(c.numerator, c.denominator)
        Maug[t_, nv] = flint.fmpq(b.numerator, b.denominator)
    R, rank = Maug.rref()
    pivots = []
    for r_ in range(rank):
        p = next(c for c in range(nv + 1) if R[r_, c] != 0)
        assert p < nv, "inconsistent structural equalities"
        pivots.append(p)
    zq = [flint.fmpq(x.numerator, x.denominator) for x in zr]
    for r_, p in enumerate(pivots):
        val = R[r_, nv]
        for c in range(nv):
            if c != p and R[r_, c] != 0:
                val -= R[r_, c] * zq[c]
        zq[p] = val
    for t_, (r, b) in enumerate(rows):
        val = sum(flint.fmpq(c.numerator, c.denominator) * zq[v] for v, c in r.items())
        assert val == flint.fmpq(b.numerator, b.denominator), "projection failed"
    print(f"RREF projection: {rank} pivot variables solved exactly; max |change| = "
          f"{max(abs(float(zq[v]) - float(zr[v])) for v in range(nv)):.2e}", flush=True)
elif rows:
    # least-norm exact correction: delta = L^T y, (L L^T) y = res, on a row basis
    Lt = L.transpose()
    G = L * Lt
    rk = G.rank()
    # select independent rows greedily
    R = flint.fmpq_mat(G)
    rr, rank = R.rref()
    # use sympy-free approach: solve via pseudo-inverse on independent subset
    idx = []
    cur = None
    for t_ in range(len(rows)):
        trial = idx + [t_]
        sub = flint.fmpq_mat([[L[a, v] for v in range(nv)] for a in trial])
        if sub.rank() == len(trial):
            idx = trial
    Ls = flint.fmpq_mat([[L[a, v] for v in range(nv)] for a in idx])
    rs = flint.fmpq_mat([[flint.fmpq(res[a].numerator, res[a].denominator)] for a in idx])
    Gs = Ls * Ls.transpose()
    y = Gs.solve(rs)
    delta = Ls.transpose() * y
    zq = [flint.fmpq(x.numerator, x.denominator) + delta[v, 0] for v, x in enumerate(zr)]
    # verify all constraints exactly
    for t_, (r, b) in enumerate(rows):
        val = sum(flint.fmpq(c.numerator, c.denominator) * zq[v] for v, c in r.items())
        assert val == flint.fmpq(b.numerator, b.denominator), "projection failed"
    print(f"projected onto {len(idx)} independent constraints; max |delta| = "
          f"{max(abs(float(delta[v, 0])) for v in range(nv)):.2e}", flush=True)
else:
    zq = [flint.fmpq(x.numerator, x.denominator) for x in zr]

# ---------- 4. exact C(s), minors, positivity ----------
t0 = time.time()
Cp = [[None] * m for _ in range(m)]
for i in range(m):
    for j in range(m):
        coeffs = []
        for k in range(D + 1):
            c = flint.fmpq(C0[k][i][j].numerator, C0[k][i][j].denominator)
            for v, cc in Cv.get((k, i, j), {}).items():
                c += cc * zq[v]
            coeffs.append(c)
        Cp[i][j] = flint.fmpq_poly(coeffs)
# symmetric?
assert all(Cp[i][j] == Cp[j][i] for i in range(m) for j in range(m))
zero_rows = [i for i in range(m) if Cp[i][i] == 0]
for i in zero_rows:
    assert all(Cp[i][j] == 0 for j in range(m)), f"row {i} has zero diagonal but nonzero entries"
keep = [i for i in range(m) if i not in zero_rows]
print(f"identically zero rows (exponents {[E[i] for i in zero_rows]}) removed; size {len(keep)}", flush=True)
# block structure by exponent parity (exact check): C_ij == 0 whenever E_i + E_j is odd
blockdiag = all(Cp[i][j] == 0 for i in keep for j in keep if (E[i] + E[j]) % 2 == 1)
if blockdiag:
    blocks = [[i for i in keep if E[i] % 2 == 0], [i for i in keep if E[i] % 2 == 1]]
    blocks = [b for b in blocks if b]
    print(f"C(s) is exactly block diagonal (even/odd exponents): block sizes {[len(b) for b in blocks]}", flush=True)
else:
    blocks = [keep]
minors = []
for bl in blocks:
    Ck = [[Cp[i][j] for j in bl] for i in bl]
    minors += bareiss_minors(Ck)
print(f"minors computed in {time.time() - t0:.1f} s; degrees {[p.degree() for p in minors]}", flush=True)
allok = True
info = []
for k, p in enumerate(minors):
    ok, inf = positive_on_open01(p)
    info.append((k + 1, ok, inf if isinstance(inf, str) else {kk: vv for kk, vv in inf.items()}))
    print(f"  Delta_{k + 1}: positive on (0,1): {ok}  {inf}", flush=True)
    allok = allok and ok
print("RESULT:", "C(s) positive definite on (0,1): PROVED" if allok else "FAILED", flush=True)
if outjson and allok:
    data = dict(n=n, qd=qd, exponents_units=E, var=[[list(p), list(q)] for (p, q) in S.var],
                z=[str(x) for x in zq], zero_rows=[E[i] for i in zero_rows],
                minor_degrees=[p.degree() for p in minors])
    with open(outjson, "w") as fh:
        json.dump(data, fh)
    print("saved", outjson)
