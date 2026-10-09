"""Independent EXACT verification of the 11 positive certificates (internal check, written from scratch).

For each certificate file:
  1. Build the target f from the CLAIM (hard-coded below from the task statement / SOS_RESULTS.md, not from the
     file), using my own enumeration of words (indep_core).  Separately rebuild the target implied by the file's
     meta block and require that the two agree (so the file states what is claimed).
  2. Build the SOS side from the data: sum_t w_t tr(P g_t^* Q g_t) (explicit format) or
     sum_b sum_{ij} (T_b S_b T_b^T)_{ij} tr(P_b u_i^* Q_b u_j) (Gram format), with u^* = reversed word (X, Y Hermitian).
  3. Compare f and the SOS side exactly, modulo PLAIN CYCLIC ROTATION ONLY.  Report the positive scale lambda with
     SOS = lambda * f.  Also report whether both sides are reversal symmetric and whether the dihedral comparison
     agrees.
  4. Exact PSD: weights > 0 (explicit) or exact LDL^T of every S block with all pivots > 0 (=> S PD => G = T S T^T PSD).
  5. Structural checks: P = Q in {1, X, Y}; half-word bidegrees; integrality of T; symmetry of S.
Usage: python -I indep_verify_positive.py [cert names ...]
"""
import json
import os
import sys
import time
from collections import Counter
from fractions import Fraction
from math import lcm

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from indep_core import (cyc, poly_p, poly_pmult, frac_word, poly_sub, is_reversal_symmetric, to_dihedral,  # noqa
                        ldl_pd_exact, bideg)
from flint import fmpz, fmpq, fmpz_mat  # noqa: E402

sys.set_int_max_str_digits(0)
CERT_DIR = os.path.join(HERE, '..', 'certs')

# claims, hard-coded from the task statement / SOS_RESULTS.md (NOT read from the files)
CLAIMS = {
    'F44_11-xx-yy.json': dict(kind='F', n=4, m=4, ea=2, eb=2, text='(F) p_{4,4}(A,B) >= tr((AB)^4), X=A^{1/2}, Y=B^{1/2}'),
    'F44_gram.json': dict(kind='F', n=4, m=4, ea=2, eb=2, text='(F) p_{4,4}(A,B) >= tr((AB)^4), Gram form'),
    'D44_11-xx-yy.json': dict(kind='D', n=4, m=4, ea=2, eb=2, text='(D) p_{4,4} >= p^mult_{4,4}, X=A^{1/2}, Y=B^{1/2}'),
    'M44_11-xx-yy.json': dict(kind='M', n=4, m=4, ea=2, eb=2, text='(M) p^mult_{4,4} >= tr((AB)^4), X=A^{1/2}, Y=B^{1/2}'),
    'F34m_11-xx-yy.json': dict(kind='F', n=3, m=4, ea=4, eb=2, text='(F) p_{3,4}(A,B) >= tr((A^{3/4}B)^4), X=A^{1/4}, Y=B^{1/2}'),
    'D34m_11-xx-yy.json': dict(kind='D', n=3, m=4, ea=4, eb=2, text='(D) p_{3,4} >= p^mult_{3,4}, X=A^{1/4}, Y=B^{1/2}'),
    'M34m_11-xx-yy.json': dict(kind='M', n=3, m=4, ea=4, eb=2, text='(M) p^mult_{3,4} >= tr((A^{3/4}B)^4), X=A^{1/4}, Y=B^{1/2}'),
    'F64_11-xx-yy.json': dict(kind='F', n=6, m=4, ea=2, eb=2, text='(F) p_{6,4}(A,B) >= tr((A^{3/2}B)^4), X=A^{1/2}, Y=B^{1/2}'),
    'P44.json': dict(kind='P', n=4, m=4, ea=2, eb=2, text='sanity: p_{4,4}(X^2,Y^2) >= 0, pure cyclic SOS (BMV S_{8,4})'),
    'F24_11-xx-yy.json': dict(kind='F', n=2, m=4, ea=2, eb=2, text='sanity: (F) p_{2,4}(A,B) >= tr((A^{1/2}B)^4)'),
    'F42_11-xx-yy.json': dict(kind='F', n=4, m=2, ea=2, eb=2, text='sanity: (F) p_{4,2}(A,B) >= tr((A^2B)^2)'),
}


def claim_target(cl):
    n, m, ea, eb = cl['n'], cl['m'], cl['ea'], cl['eb']
    if cl['kind'] == 'F':
        return poly_sub(poly_p(n, m, ea, eb), {cyc(frac_word(n, m, ea, eb)): Fraction(1)})
    if cl['kind'] == 'D':
        return poly_sub(poly_p(n, m, ea, eb), poly_pmult(n, m, ea, eb))
    if cl['kind'] == 'M':
        return poly_sub(poly_pmult(n, m, ea, eb), {cyc(frac_word(n, m, ea, eb)): Fraction(1)})
    if cl['kind'] == 'P':
        return poly_p(n, m, ea, eb)
    raise ValueError(cl)


def meta_target(meta):
    """my own reading of the meta block: LHS ('p' or 'pmult') minus each listed rhs word, minus p^mult if sub."""
    n, m, ea, eb = meta['n'], meta['m'], meta['ea'], meta['eb']
    if meta['lhs'] == 'p':
        f = poly_p(n, m, ea, eb)
    elif meta['lhs'] == 'pmult':
        f = poly_pmult(n, m, ea, eb)
    else:
        raise ValueError(meta['lhs'])
    for c, w in meta['rhs']:
        assert set(w) <= {'x', 'y'}
        f = poly_sub(f, {cyc(w): Fraction(c)})
    if meta.get('sub') == 'pmult':
        f = poly_sub(f, poly_pmult(n, m, ea, eb))
    else:
        assert meta.get('sub') is None, meta.get('sub')
    return f


def ratio_check(f, s_num, s_den):
    """check s_num[C]/s_den == lam * f[C] for every cyclic class C, with one rational lam (returned)."""
    keys = set(f) | set(k for k, v in s_num.items() if v != 0)
    lam = None
    bad = []
    for k in keys:
        fv = f.get(k, Fraction(0))
        sv = s_num.get(k, 0)
        if fv == 0 or sv == 0:
            if not (fv == 0 and sv == 0):
                bad.append(k)
            continue
        if lam is None:
            # lam = (sv / s_den) / fv, as an exact fraction (one big gcd only)
            q = fmpq(fmpz(sv) * fv.denominator, fmpz(s_den) * fv.numerator)
            lam = Fraction(int(q.p), int(q.q))
        # sv * fden * lam_den == fnum * s_den * lam_num   (integers, no gcd)
        if fmpz(sv) * fv.denominator * lam.denominator != fmpz(fv.numerator) * s_den * lam.numerator:
            bad.append(k)
    return lam, bad, len(keys)


def sos_explicit(terms, log):
    """returns (dict class -> integer numerator, common denominator, info)."""
    cache = {}
    per_term = []
    dens = []
    types = Counter()
    bidegs = Counter()
    coeff_sum_zero = True
    for t in terms:
        P, Q = t['P'], t['Q']
        assert P in ('', 'x', 'y') and Q in ('', 'x', 'y'), (P, Q)
        assert P == Q, "off-diagonal localizer"
        types[(P or '1', Q or '1')] += 1
        w = Fraction(t['weight'])
        assert w > 0, "non-positive weight"
        items = [(u, Fraction(c)) for u, c in t['poly'].items()]
        assert all(set(u) <= {'x', 'y'} and len(u) > 0 for u, _ in items)
        assert len(set(u for u, _ in items)) == len(items)
        for u, _ in items:
            bidegs[(P or '1', bideg(u))] += 1
        if sum(c for _, c in items) != 0:
            coeff_sum_zero = False
        L = 1
        for _, c in items:
            L = lcm(L, c.denominator)
        ints = [(u, c.numerator * (L // c.denominator)) for u, c in items]
        acc = {}
        for u, a in ints:
            left = P + u[::-1] + Q
            for v, b in ints:
                word = left + v
                k = cache.get(word)
                if k is None:
                    k = cyc(word)
                    cache[word] = k
                acc[k] = acc.get(k, 0) + a * b
        D = w.denominator * L * L
        per_term.append((w.numerator, D, acc))
        dens.append(D)
    Dall = 1
    for D in dens:
        Dall = lcm(Dall, D)
    Dall_f = fmpz(Dall)
    total = {}
    for wn, D, acc in per_term:
        c = fmpz(wn) * (Dall // D)
        for k, v in acc.items():
            if v:
                total[k] = total.get(k, fmpz(0)) + c * v
    info = dict(n_terms=len(terms), types={f"({a},{b})": c for (a, b), c in types.items()},
                half_word_bidegrees=sorted(set(bidegs)),
                coefficient_sums_zero=coeff_sum_zero, common_den_digits=len(str(Dall)))
    return {k: int(v) for k, v in total.items()}, Dall_f, info


def sos_gram(blocks, log):
    """returns (dict class -> integer numerator, common denominator, info); also does the exact PSD test of S."""
    info = dict(blocks=[])
    results = []
    for bi, blk in enumerate(blocks):
        P, Q, words = blk['P'], blk['Q'], blk['words']
        assert P in ('', 'x', 'y') and Q in ('', 'x', 'y'), (P, Q)
        assert P == Q, "off-diagonal localizer"
        N = len(words)
        assert len(set(words)) == N, "repeated half-words"
        assert all(set(u) <= {'x', 'y'} for u in words)
        bd = set(bideg(u) for u in words)
        S = [[Fraction(v) for v in row] for row in blk['S']]
        r = len(S)
        assert all(len(row) == r for row in S)
        assert all(S[a][c] == S[c][a] for a in range(r) for c in range(a + 1, r)), "S not symmetric"
        Tcols = blk['T_columns']
        assert len(Tcols) == r and all(len(col) == N for col in Tcols)
        Tint = []
        for col in Tcols:
            colv = []
            for v in col:
                fv = Fraction(v)
                assert fv.denominator == 1, "non-integer T entry"
                colv.append(int(fv))
            Tint.append(colv)
        # exact PD test of S by LDL^T in exact rationals (flint fmpq for speed)
        t0 = time.time()
        Sq = [[fmpq(x.numerator, x.denominator) for x in row] for row in S]
        pd, piv = ldl_pd_exact(Sq)
        t_ldl = time.time() - t0
        piv_digits = max(len(str(p.p)) + len(str(p.q)) for p in piv)
        minpiv = min(float(p) for p in piv)
        # G = T S T^T over a common denominator
        D = 1
        for row in S:
            for x in row:
                D = lcm(D, x.denominator)
        Sint = fmpz_mat(r, r, [x.numerator * (D // x.denominator) for row in S for x in row])
        T = fmpz_mat(N, r, [Tint[a][i] for i in range(N) for a in range(r)])
        G = T * Sint * T.transpose()
        # rank of T (so rank G = rank T when S is PD)
        rankT = T.rank()
        acc = {}
        nz = 0
        for i in range(N):
            left = P + words[i][::-1] + Q
            for j in range(N):
                g = G[i, j]
                if g != 0:
                    nz += 1
                    k = cyc(left + words[j])
                    acc[k] = acc.get(k, 0) + int(g)
        results.append((D, acc))
        binfo = dict(P=P or '1', Q=Q or '1', N=N, r=r, rankT=int(rankT), half_word_bidegree=sorted(bd), S_PD=pd,
                     min_pivot_float=minpiv, max_pivot_digits=piv_digits, ldl_seconds=round(t_ldl, 1),
                     den_digits=len(str(D)), G_nonzeros=nz)
        info['blocks'].append(binfo)
        log(f"    block {bi}: P=Q={P or '1'} N={N} r={r} rank(T)={rankT} bideg={sorted(bd)} S exactly PD: {pd} "
            f"(LDL^T {len(piv)} pivots > 0, min pivot ~ {minpiv:.3e}, max pivot size {piv_digits} digits, "
            f"{t_ldl:.1f}s)")
        if not pd:
            return None, None, info
    Dall = 1
    for D, _ in results:
        Dall = lcm(Dall, D)
    total = {}
    for D, acc in results:
        c = Dall // D
        for k, v in acc.items():
            if v:
                total[k] = total.get(k, 0) + c * v
    return total, fmpz(Dall), info


def verify(fn, log):
    cl = CLAIMS[fn]
    path = os.path.join(CERT_DIR, fn)
    t0 = time.time()
    with open(path) as fh:
        cert = json.load(fh)
    meta = cert['meta']
    log(f"== {fn}: CLAIM {cl['text']}")
    # 1. target from the claim, and agreement with the file's meta
    f = claim_target(cl)
    assert (meta['n'], meta['m'], meta['ea'], meta['eb']) == (cl['n'], cl['m'], cl['ea'], cl['eb']), "meta n,m,ea,eb differ"
    fm = meta_target(meta)
    meta_ok = (fm == f)
    log(f"    target f built from the definition: {len(f)} cyclic classes, total degree {len(next(iter(f)))}, "
        f"bidegree {bideg(next(iter(f)))}; meta block states the same target: {meta_ok}")
    log(f"    f reversal-symmetric (needed only for the dihedral variant): {is_reversal_symmetric(f)}")
    # 2. SOS side
    if cert.get('format') == 'gram':
        s_num, s_den, info = sos_gram(cert['blocks'], log)
        if s_num is None:
            log("    => FAILED (S block not PD)")
            return dict(file=fn, ok=False, info=info)
        fmt = 'gram'
    else:
        s_num, s_den, info = sos_explicit(cert['terms'], log)
        fmt = 'explicit'
        log(f"    explicit: {info['n_terms']} terms by localizer {info['types']}, all weights > 0 (exact), half-word "
            f"bidegrees {info['half_word_bidegrees']}, every g has coefficient sum 0: {info['coefficient_sums_zero']}, "
            f"common denominator {info['common_den_digits']} digits")
    # 3. exact comparison modulo cyclic rotation
    lam, bad, nkeys = ratio_check(f, s_num, s_den)
    ok_cyc = (not bad) and lam is not None and lam > 0
    # reversal symmetry of the SOS side (as a check of the dihedral reduction)
    s_rev_sym = all(s_num.get(cyc(k[::-1]), 0) == v for k, v in s_num.items())
    # dihedral comparison (diagnostic): same lam
    fd = to_dihedral(f)
    sd = {}
    for k, v in s_num.items():
        from indep_core import dih
        kk = dih(k)
        sd[kk] = sd.get(kk, 0) + v
    lam_d, bad_d, _ = ratio_check(fd, sd, s_den)
    ok_dih = (not bad_d) and lam_d == lam
    log(f"    exact identity SOS == lambda * f modulo plain cyclic rotation: {ok_cyc}  (lambda = {lam}, "
        f"{nkeys} classes compared, {len(bad)} mismatches)")
    log(f"    SOS side reversal-symmetric: {s_rev_sym}; dihedral comparison agrees: {ok_dih}")
    ok = ok_cyc and meta_ok
    log(f"    => {'VERIFIED' if ok else 'FAILED'}  ({time.time() - t0:.1f}s)")
    return dict(file=fn, ok=ok, fmt=fmt, lam=str(lam), meta_ok=meta_ok, cyclic_identity=ok_cyc,
                dihedral_identity=ok_dih, f_rev_sym=is_reversal_symmetric(f), s_rev_sym=s_rev_sym, info=info,
                n_classes=len(f), seconds=round(time.time() - t0, 1))


def main():
    names = sys.argv[1:] or list(CLAIMS)
    logf = open(os.path.join(HERE, 'logs', 'indep_verify_positive.log'), 'a')

    def log(s):
        print(s, flush=True)
        logf.write(s + '\n')
        logf.flush()
    log(f"# run {time.strftime('%Y-%m-%d %H:%M:%S')}  files: {names}")
    res = []
    for fn in names:
        res.append(verify(fn, log))
    with open(os.path.join(HERE, 'logs', 'indep_verify_positive_' + ('all' if not sys.argv[1:] else
                                                                    '_'.join(n.split('.')[0] for n in names)) + '.json'), 'w') as fh:
        json.dump(res, fh, indent=1, default=str)
    log("SUMMARY: " + ", ".join(f"{r['file']}: {'OK' if r['ok'] else 'FAIL'}" for r in res))


if __name__ == '__main__':
    main()
