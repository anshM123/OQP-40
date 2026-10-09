"""Independent numerical / exact-matrix cross-check of the positive certificates (internal check).

Two evaluation modes, both from scratch:
  exact : X = U diag(lam) U^*, U = (I+K)^{-1}(I-K) exactly unitary (Cayley transform of a skew-Hermitian
          Gaussian-integer K), lam exact (integers incl. 0, spread up to 1e8, repeated values).  Computed with the
          integer-scaled matrix adj(I+K)(I-K) lam (I-K)^* adj(I+K)^* (= |det(I+K)|^2 X; harmless because f is
          bihomogeneous and every SOS term scales the same way).  Everything is exact integer arithmetic.
  arb   : X = U diag(lam) U^*, U Haar-random (Gram-Schmidt of a complex Gaussian matrix, in ball arithmetic at high
          precision), lam generic / spread over many decades / near-singular / degenerate / near-commuting pairs.
          Ball arithmetic gives rigorous enclosures.
Complex matrices are realified: Z = R + iI  ->  [[R, -I], [I, R]]; then Z^* -> transpose, and Re tr Z = tr(.)/2,
Im tr Z = trace of the lower-left block.
For every sample we evaluate, DIRECTLY from the definitions with A = X^ea, B = Y^eb as matrices:
  f = p_{n,m}(A,B) - RHS (or the D / M variant),  and the SOS side  sum_blocks sum_ij G_ij Re tr(P u_i^* Q u_j)
  (explicit format: sum_t w_t Re tr(P g_t^* Q g_t)), each block/term separately.
Checks: SOS == f (exact equality, resp. enclosure of 0 in the ball difference); every block/term >= 0; f >= 0;
Im tr f == 0.
Usage: python -I indep_numeric.py MODE [cert ...]      MODE in {exact, arb}
"""
import json
import math
import os
import random
import sys
import time
from fractions import Fraction
from math import lcm

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from indep_core import p_words, weak_compositions, frac_word  # noqa: E402
from flint import fmpz, fmpq, fmpz_mat, arb, arb_mat, acb, ctx  # noqa: E402

sys.set_int_max_str_digits(0)
CERT_DIR = os.path.join(HERE, '..', 'certs')

CLAIMS = {
    'F44_11-xx-yy.json': ('F', 4, 4, 2, 2), 'F44_gram.json': ('F', 4, 4, 2, 2), 'D44_11-xx-yy.json': ('D', 4, 4, 2, 2),
    'M44_11-xx-yy.json': ('M', 4, 4, 2, 2), 'F34m_11-xx-yy.json': ('F', 3, 4, 4, 2),
    'D34m_11-xx-yy.json': ('D', 3, 4, 4, 2), 'M34m_11-xx-yy.json': ('M', 3, 4, 4, 2),
    'F64_11-xx-yy.json': ('F', 6, 4, 2, 2), 'P44.json': ('P', 4, 4, 2, 2), 'F24_11-xx-yy.json': ('F', 2, 4, 2, 2),
    'F42_11-xx-yy.json': ('F', 4, 2, 2, 2),
}


# ------------------------------------------------------------------------------------------------ matrix helpers
class Ring:
    def __init__(self, kind):
        self.kind = kind

    def mat(self, r, c, flat):
        return fmpz_mat(r, c, flat) if self.kind == 'exact' else arb_mat(r, c, flat)

    def eye(self, n):
        return self.mat(n, n, [1 if i == j else 0 for i in range(n) for j in range(n)])

    def trace(self, M):
        n = M.nrows()
        s = M[0, 0]
        for i in range(1, n):
            s = s + M[i, i]
        return s

    def im_trace(self, M):
        d = M.nrows() // 2
        s = M[d, 0]
        for i in range(1, d):
            s = s + M[d + i, i]
        return s

    def frob(self, M1, M2):
        e1, e2 = M1.entries(), M2.entries()
        s = e1[0] * e2[0]
        for a, b in zip(e1[1:], e2[1:]):
            s = s + a * b
        return s


def realify(Re, Im):
    d = len(Re)
    flat = []
    for i in range(d):
        flat += list(Re[i]) + [-v for v in Im[i]]
    for i in range(d):
        flat += list(Im[i]) + list(Re[i])
    return flat


def mpow(R, M, k, n2):
    out = R.eye(n2)
    for _ in range(k):
        out = out * M
    return out


# ------------------------------------------------------------------------------------------------ exact samples
def int_det(M):
    return int(fmpz_mat(M).det())


def cayley_scaled(d, rng, lam, kbound=2):
    """returns realified integer matrix of adj(I+K)(I-K) diag(lam) (I-K)^* adj(I+K)^*, with K skew-Hermitian
    Gaussian-integer; lam: list of nonnegative integers.  Spectrum = |det(I+K)|^2 * lam exactly."""
    # K = i H with H Hermitian Gaussian-integer  => K skew-Hermitian
    Hr = [[0] * d for _ in range(d)]
    Hi = [[0] * d for _ in range(d)]
    for i in range(d):
        Hr[i][i] = rng.randint(-kbound, kbound)
        for j in range(i + 1, d):
            a, b = rng.randint(-kbound, kbound), rng.randint(-kbound, kbound)
            Hr[i][j], Hi[i][j] = a, b
            Hr[j][i], Hi[j][i] = a, -b
    # K = i H: Re K = -Im H, Im K = Re H
    Kr = [[-Hi[i][j] for j in range(d)] for i in range(d)]
    Ki = [[Hr[i][j] for j in range(d)] for i in range(d)]
    IpK = fmpz_mat(2 * d, 2 * d, realify([[int(i == j) + Kr[i][j] for j in range(d)] for i in range(d)], Ki))
    ImK = fmpz_mat(2 * d, 2 * d, realify([[int(i == j) - Kr[i][j] for j in range(d)] for i in range(d)],
                                         [[-v for v in row] for row in Ki]))
    # adjugate of the realified I+K: det * inverse (exact); realified inverse = realified complex inverse
    det = IpK.det()
    inv = fmpz_mat(IpK).inv()            # fmpq_mat
    adj_flat = []
    for i in range(2 * d):
        for j in range(2 * d):
            q = inv[i, j] * det
            assert q.q == 1
            adj_flat.append(int(q.p))
    adj = fmpz_mat(2 * d, 2 * d, adj_flat)
    Usc = adj * ImK                      # = det(realified I+K) * U ; realified, so det = |det(I+K)|^2
    L = fmpz_mat(2 * d, 2 * d, realify([[lam[i] if i == j else 0 for j in range(d)] for i in range(d)],
                                       [[0] * d for _ in range(d)]))
    X = Usc * L * Usc.transpose()
    return X


def exact_samples(d, rng, family):
    if family == 'generic':
        lx = [rng.randint(1, 9) for _ in range(d)]
        ly = [rng.randint(1, 9) for _ in range(d)]
    elif family == 'spread':
        lx = [10 ** round(8 * i / max(d - 1, 1)) for i in range(d)]
        ly = [10 ** round(8 * (d - 1 - i) / max(d - 1, 1)) * rng.randint(1, 3) for i in range(d)]
    elif family == 'singular':
        lx = [0] + [rng.randint(1, 9) for _ in range(d - 1)]
        ly = [0] * (d - 1) + [rng.randint(1, 9)]            # Y rank one
    elif family == 'degenerate':
        lx = [1] * (d // 2) + [5] * (d - d // 2)
        ly = [2] * (d - 1) + [7]
    elif family == 'near_singular':
        lx = [1] + [10 ** 8 * rng.randint(1, 9) for _ in range(d - 1)]
        ly = [10 ** 8 * rng.randint(1, 9) for _ in range(d - 1)] + [1]
    else:
        raise ValueError(family)
    X = cayley_scaled(d, rng, lx)
    Y = cayley_scaled(d, rng, ly)
    return X, Y, dict(lam_x=lx, lam_y=ly)


# ------------------------------------------------------------------------------------------------ arb samples
def haar_unitary(d, rng):
    """complex Gaussian matrix -> Gram-Schmidt (columns) in acb arithmetic at the current precision."""
    cols = [[acb(rng.gauss(0, 1), rng.gauss(0, 1)) for _ in range(d)] for _ in range(d)]
    Q = []
    for v in cols:
        w = list(v)
        for q in Q:
            c = sum((q[i].conjugate() * w[i] for i in range(d)), acb(0))
            w = [w[i] - c * q[i] for i in range(d)]
        nrm = sum((abs(w[i]) ** 2 for i in range(d)), arb(0)).sqrt()
        Q.append([w[i] / nrm for i in range(d)])
    # U[i][j] = Q[j][i]
    return [[Q[j][i] for j in range(d)] for i in range(d)]


def arb_hermitian(U, lam):
    d = len(U)
    Re = [[None] * d for _ in range(d)]
    Im = [[None] * d for _ in range(d)]
    for i in range(d):
        for j in range(i, d):
            s = acb(0)
            for k in range(d):
                s += U[i][k] * lam[k] * U[j][k].conjugate()
            if i == j:
                Re[i][i], Im[i][i] = s.real, arb(0)
            else:
                Re[i][j], Im[i][j] = s.real, s.imag
                Re[j][i], Im[j][i] = s.real, -s.imag
    return arb_mat(2 * d, 2 * d, realify(Re, Im))


def arb_samples(d, rng, family):
    U = haar_unitary(d, rng)
    if family == 'near_commuting':
        V0 = [[U[i][j] + arb('1e-6') * acb(rng.gauss(0, 1), rng.gauss(0, 1)) for j in range(d)] for i in range(d)]
        # re-orthonormalize the perturbed basis
        cols = [[V0[i][j] for i in range(d)] for j in range(d)]
        Q = []
        for v in cols:
            w = list(v)
            for q in Q:
                c = sum((q[i].conjugate() * w[i] for i in range(d)), acb(0))
                w = [w[i] - c * q[i] for i in range(d)]
            nrm = sum((abs(w[i]) ** 2 for i in range(d)), arb(0)).sqrt()
            Q.append([w[i] / nrm for i in range(d)])
        V = [[Q[j][i] for j in range(d)] for i in range(d)]
    else:
        V = haar_unitary(d, rng)
    if family == 'generic':
        lx = [arb(rng.uniform(0.05, 1)) for _ in range(d)]
        ly = [arb(rng.uniform(0.05, 1)) for _ in range(d)]
    elif family == 'spread':
        lx = [arb(10) ** rng.uniform(-6, 6) for _ in range(d)]
        ly = [arb(10) ** rng.uniform(-6, 6) for _ in range(d)]
    elif family == 'very_spread':
        lx = [arb(10) ** (-12 + 24 * i / max(d - 1, 1)) for i in range(d)]
        ly = [arb(10) ** (12 - 24 * i / max(d - 1, 1)) for i in range(d)]
    elif family == 'near_singular':
        lx = [arb('1e-30')] + [arb(rng.uniform(0.1, 1)) for _ in range(d - 1)]
        ly = [arb(rng.uniform(0.1, 1)) for _ in range(d - 1)] + [arb('1e-30')]
    elif family == 'degenerate':
        lx = [arb(1)] * (d // 2) + [arb(3)] * (d - d // 2)
        ly = [arb('0.5')] * (d - 1) + [arb(2)]
    elif family == 'near_commuting':
        lx = [arb(rng.uniform(0.1, 1)) for _ in range(d)]
        ly = [arb(rng.uniform(0.1, 1)) for _ in range(d)]
    else:
        raise ValueError(family)
    return arb_hermitian(U, lx), arb_hermitian(V, ly), dict(family=family)


# ------------------------------------------------------------------------------------------------ evaluation
def evaluate(R, cert, claim, RX, RY):
    kind, n, m, ea, eb = claim
    n2 = RX.nrows()
    A = mpow(R, RX, ea, n2)
    B = mpow(R, RY, eb, n2)
    I = R.eye(n2)
    memo = {'': I}

    def wAB(w):
        M = memo.get(w)
        if M is None:
            M = wAB(w[:-1]) * (A if w[-1] == 'A' else B)
            memo[w] = M
        return M

    def p_val():
        tot = math.comb(n + m, n)
        re = None
        im = None
        for w in p_words(n, m):
            M = wAB(w)
            t, ti = R.trace(M), R.im_trace(M)
            re = t if re is None else re + t
            im = ti if im is None else im + ti
        return re, im, tot                  # (2 Re sum, Im sum, count)

    def pmult_val():
        re = None
        im = None
        for N in weak_compositions(n, m):
            mult = math.factorial(n)
            for Nj in N:
                mult //= math.factorial(Nj)
            w = ''.join('B' + 'A' * Nj for Nj in N)
            M = wAB(w)
            t, ti = R.trace(M) * mult, R.im_trace(M) * mult
            re = t if re is None else re + t
            im = ti if im is None else im + ti
        return re, im, m ** n

    def frac_val():
        k = ea * n // m
        Z = mpow(R, RX, k, n2) * mpow(R, RY, eb, n2)
        M = mpow(R, Z, m, n2)
        return R.trace(M), R.im_trace(M)

    # f = LHS - RHS, kept as (2 Re f, Im f) in the ring; rationals for exact mode
    def scal(x, den):
        return fmpq(int(x), den) if R.kind == 'exact' else x / den

    if kind in ('F', 'D', 'P'):
        a, ai, c = p_val()
        lhs, lhs_i = scal(a, c), scal(ai, c)
    else:
        a, ai, c = pmult_val()
        lhs, lhs_i = scal(a, c), scal(ai, c)
    if kind in ('F', 'M'):
        b, bi = frac_val()
        rhs, rhs_i = scal(b, 1), scal(bi, 1)
    elif kind == 'D':
        b, bi, c2 = pmult_val()
        rhs, rhs_i = scal(b, c2), scal(bi, c2)
    else:
        rhs, rhs_i = scal(0, 1), scal(0, 1)
    f2 = lhs - rhs                     # = 2 Re tr f
    fim = lhs_i - rhs_i                # = Im tr f
    lhs2, rhs2 = lhs, rhs

    # SOS side
    memo_xy = {'': I}

    def wxy(w):
        M = memo_xy.get(w)
        if M is None:
            M = wxy(w[:-1]) * (RX if w[-1] == 'x' else RY)
            memo_xy[w] = M
        return M
    loc = {'': I, 'x': RX, 'y': RY}
    parts = []
    if cert.get('format') == 'gram':
        for blk in cert['blocks']:
            P, Q, words = blk['P'], blk['Q'], blk['words']
            N = len(words)
            r = len(blk['S'])
            mats = [wxy(u) for u in words]
            Vf, Wf = [], []
            for Mi in mats:
                Vf += Mi.entries()
                Wf += (loc[Q] * Mi * loc[P]).entries()
            V = R.mat(N, n2 * n2, Vf)
            W = R.mat(N, n2 * n2, Wf)
            H = V * W.transpose()                     # H_ij = 2 Re tr(P u_i^* Q u_j)
            T = R.mat(N, r, [int(blk['T_columns'][a][i]) for i in range(N) for a in range(r)])
            K = T.transpose() * H * T
            S = [[Fraction(v) for v in row] for row in blk['S']]
            if R.kind == 'exact':
                D = 1
                for row in S:
                    for x in row:
                        D = lcm(D, x.denominator)
                acc = fmpz(0)
                for a_ in range(r):
                    for c_ in range(r):
                        acc += fmpz(S[a_][c_].numerator * (D // S[a_][c_].denominator)) * K[a_, c_]
                val = fmpq(int(acc), D)
            else:
                val = None
                for a_ in range(r):
                    for c_ in range(r):
                        t = arb(fmpq(S[a_][c_].numerator, S[a_][c_].denominator)) * K[a_, c_]
                        val = t if val is None else val + t
            parts.append((f"{P or '1'}{Q or '1'}", val))
    else:
        for t in cert['terms']:
            P, Q = t['P'], t['Q']
            items = [(u, Fraction(c)) for u, c in t['poly'].items()]
            L = 1
            for _, c in items:
                L = lcm(L, c.denominator)
            g = None
            for u, c in items:
                Mu = wxy(u) * int(c.numerator * (L // c.denominator))
                g = Mu if g is None else g + Mu
            val_int = R.frob(g, loc[Q] * g * loc[P])        # 2 Re tr(P g^* Q g) * L^2
            w = Fraction(t['weight'])
            if R.kind == 'exact':
                val = fmpq(int(val_int), 1) * fmpq(w.numerator, w.denominator * L * L)
            else:
                val = val_int * arb(fmpq(w.numerator, w.denominator)) / (fmpz(L) * fmpz(L))
            parts.append((f"{P or '1'}{Q or '1'}", val))
    s2 = parts[0][1]
    for _, v in parts[1:]:
        s2 = s2 + v
    return dict(f2=f2, fim=fim, s2=s2, parts=parts, lhs2=lhs2, rhs2=rhs2)


def run(mode, names, log, full=False, dmin=2):
    R = Ring(mode)
    rng = random.Random((20261008 if mode == 'exact' else 777) + (1000 if full else 0))
    if mode == 'exact':
        fams = ['generic', 'spread', 'singular', 'degenerate', 'near_singular']
    else:
        fams = ['generic', 'spread', 'very_spread', 'near_singular', 'degenerate', 'near_commuting']
    summary = {}
    for fn in names:
        claim = CLAIMS[fn]
        with open(os.path.join(CERT_DIR, fn)) as fh:
            cert = json.load(fh)
        big = cert.get('format') == 'gram' and len(cert['blocks'][0]['words']) > 100
        n_ok = n_tot = 0
        worst_rel = 0.0
        min_f_rel = None
        min_part_rel = None
        t0 = time.time()
        for d in range(dmin, 9):
            fam_list = fams if (full or not big or d <= 5) else fams[:2]
            for fam in fam_list:
                ts = time.time()
                if mode == 'exact':
                    RX, RY, info = exact_samples(d, rng, fam)
                else:
                    ctx.prec = 1200 if fam in ('very_spread', 'near_commuting', 'near_singular') else 600
                    RX, RY, info = arb_samples(d, rng, fam)
                ev = evaluate(R, cert, claim, RX, RY)
                f2, s2, fim = ev['f2'], ev['s2'], ev['fim']
                if mode == 'exact':
                    ok_id = (f2 == s2)
                    ok_im = (fim == 0)
                    ok_f = f2 >= 0
                    ok_parts = all(v >= 0 for _, v in ev['parts'])
                    scale = abs(ev['lhs2']) + abs(ev['rhs2'])          # exact; ratios formed exactly
                    rel = 0.0 if ok_id else float('inf')
                    frel = float(f2 / scale) if scale != 0 else 0.0
                    prel = float(min(v for _, v in ev['parts']) / scale) if scale != 0 else 0.0
                else:
                    diff = f2 - s2
                    ok_id = diff.contains(0)
                    ok_im = fim.contains(0)
                    ok_f = (f2 > 0) or f2.contains(0)          # rigorous: f >= 0 not excluded
                    ok_parts = all((v > 0) or v.contains(0) for _, v in ev['parts'])
                    scale = abs(ev['lhs2']) + abs(ev['rhs2'])
                    rel = float((abs(diff) / scale).mid())
                    frel = float((f2 / scale).mid())
                    prel = min(float((v / scale).mid()) for _, v in ev['parts'])
                ok = ok_id and ok_im and ok_f and ok_parts
                n_tot += 1
                n_ok += ok
                worst_rel = max(worst_rel, rel)
                min_f_rel = frel if min_f_rel is None else min(min_f_rel, frel)
                min_part_rel = prel if min_part_rel is None else min(min_part_rel, prel)
                log(f"  {fn} d={d} {fam:14s} identity={'ok' if ok_id else 'FAIL'} Im f=0:{ok_im} f>=0:{ok_f} "
                    f"all parts>=0:{ok_parts} |f-SOS|/scale={rel:.2e} f/scale={frel:.3e} "
                    f"min part/scale={prel:.3e} ({time.time() - ts:.1f}s)")
        summary[fn] = dict(samples=n_tot, ok=n_ok, worst_rel_diff=worst_rel, min_f_over_scale=min_f_rel,
                           min_part_over_scale=min_part_rel, seconds=round(time.time() - t0, 1))
        log(f"== {fn} [{mode}]: {n_ok}/{n_tot} samples pass; worst |f-SOS|/scale {worst_rel:.2e}; "
            f"min f/scale {min_f_rel:.3e}; min part/scale {min_part_rel:.3e} ({time.time() - t0:.1f}s)")
    return summary


def main():
    mode = sys.argv[1]
    full = '--full68' in sys.argv            # all families at d = 6..8 also for the 210-half-word certificates
    args = [a for a in sys.argv[2:] if not a.startswith('--')]
    names = args or list(CLAIMS)
    suffix = '_full68' if full else ''
    logf = open(os.path.join(HERE, 'logs', f'indep_numeric_{mode}{suffix}.log'), 'a')

    def log(s):
        print(s, flush=True)
        logf.write(s + '\n')
        logf.flush()
    log(f"# run {time.strftime('%Y-%m-%d %H:%M:%S')} mode={mode} files={names} full68={full}")
    summary = run(mode, names, log, full=full, dmin=6 if full else 2)
    tag = ('all' if not args else '_'.join(n.split('.')[0] for n in names)) + suffix
    with open(os.path.join(HERE, 'logs', f'indep_numeric_{mode}_{tag}.json'), 'w') as fh:
        json.dump(summary, fh, indent=1)
    log("SUMMARY " + json.dumps(summary))


if __name__ == '__main__':
    main()
