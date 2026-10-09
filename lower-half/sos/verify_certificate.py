"""Independent exact verifier for the certificate files in certs/ (self-contained: does not import the search code).

A certificate file (JSON) contains
  meta: n, m, ea, eb (A = X^ea, B = Y^eb), lhs ('p' or 'pmult'), rhs (list of [coefficient, word in x,y]),
        sub (optional 'pmult': subtract p^mult_{n,m}(A,B) as well)
  terms: list of {P, Q, weight, poly}, P, Q in {'', 'x', 'y'}, weight a positive rational (string),
         poly a dict word -> rational coefficient (string).
It asserts the identity of trace polynomials in Hermitian letters X, Y
  f(X,Y) := LHS_{n,m}(X^ea, Y^eb) - sum_rhs c * word  ==  sum_terms weight * P g^* Q g      (modulo cyclic
  rotation and reversal of words; for real coefficients this is equality of tau f for every tracial state tau)
by exact rational arithmetic, where LHS is recomputed here from its definition:
  p_{n,m}(A,B)     = C(n+m,n)^{-1} * sum of all words with n letters A and m letters B,
  p^mult_{n,m}(A,B) = m^{-n} sum_{J in [m]^n} tr prod_{j=1}^m (B A^{N_j(J)}).
Consequence: for X, Y >= 0 (and for all Hermitian X, Y if every term has P = Q = ''), tau f(X,Y) >= 0 since
tau(P g^* Q g) = ||Q^{1/2} g P^{1/2}||_2^2 >= 0.
Usage: python verify_certificate.py certs/*.json
"""
import itertools
import json
import sys
from fractions import Fraction
from math import comb


def dihedral_key(w):
    """lexicographically least word among all rotations of w and of its reversal."""
    n = len(w)
    ww, rr = w + w, w[::-1] + w[::-1]
    return min(min(ww[i:i + n] for i in range(n)), min(rr[i:i + n] for i in range(n)))


def add(poly, word, c):
    k = dihedral_key(word)
    poly[k] = poly.get(k, Fraction(0)) + c


def lhs_p(n, m, a, b):
    poly = {}
    tot = comb(n + m, n)
    count = 0
    for seq in itertools.product('AB', repeat=n + m):
        if seq.count('A') != n:
            continue
        count += 1
        add(poly, ''.join(a if s == 'A' else b for s in seq), Fraction(1, tot))
    assert count == tot
    return poly


def lhs_pmult(n, m, a, b):
    poly = {}
    for J in itertools.product(range(m), repeat=n):
        word = ''.join(b + a * J.count(j) for j in range(m))
        add(poly, word, Fraction(1, m ** n))
    return poly


def target(meta):
    n, m, a, b = meta['n'], meta['m'], 'x' * meta['ea'], 'y' * meta['eb']
    f = lhs_p(n, m, a, b) if meta['lhs'] == 'p' else lhs_pmult(n, m, a, b)
    for c, word in meta['rhs']:
        add(f, word, -Fraction(c))
    if meta.get('sub') == 'pmult':
        for k, v in lhs_pmult(n, m, a, b).items():
            f[k] = f.get(k, Fraction(0)) - v
    return {k: v for k, v in f.items() if v != 0}


def expand(terms):
    out = {}
    hermitian_only = True
    for t in terms:
        P, Q, wgt = t['P'], t['Q'], Fraction(t['weight'])
        assert P in ('', 'x', 'y') and Q in ('', 'x', 'y'), (P, Q)
        assert wgt > 0, "non-positive weight"
        if P or Q:
            hermitian_only = False
        g = [(u, Fraction(c)) for u, c in t['poly'].items()]
        for u, cu in g:
            ru = P + u[::-1] + Q
            for v, cv in g:
                add(out, ru + v, wgt * cu * cv)
    return {k: v for k, v in out.items() if v != 0}, hermitian_only


def half_words(nx, ny):
    out = []
    for pos in itertools.combinations(range(nx + ny), ny):
        S = set(pos)
        out.append(''.join('y' if i in S else 'x' for i in range(nx + ny)))
    return out


def psd_exact(M):
    """exact PSD test of a symmetric rational matrix (symmetric elimination, zero pivots need zero rows)."""
    A = [row[:] for row in M]
    alive = list(range(len(A)))
    while alive:
        k = alive[0]
        piv = A[k][k]
        if piv < 0:
            return False
        if piv == 0:
            if any(A[k][j] != 0 for j in alive):
                return False
            alive.pop(0)
            continue
        rest = alive[1:]
        for i in rest:
            if A[i][k] != 0:
                fct = A[i][k] / piv
                for j in rest:
                    A[i][j] -= fct * A[k][j]
        alive = rest
    return True


def pd_bareiss(S):
    """exact positive-definiteness test (Sylvester) by fraction-free Bareiss elimination on the integer-scaled
    symmetric matrix; returns True iff all leading principal minors are > 0.  Standard library only."""
    from math import lcm
    D = 1
    for row in S:
        for q in row:
            D = lcm(D, q.denominator)
    M = [[int(q * D) for q in row] for row in S]
    r = len(M)
    prev = 1
    for k in range(r):
        if M[k][k] <= 0:
            return False
        pk = M[k][k]
        for i in range(k + 1, r):
            Mi, Mik = M[i], M[i][k]
            Mk = M[k]
            for j in range(k + 1, r):
                Mi[j] = (Mi[j] * pk - Mik * Mk[j]) // prev
        prev = pk
    return True


def verify_nonexistence(path, cert):
    """y >= 0 on the cone  <=>  every localized moment matrix M_P(y)[u,v] = y([P rev(u) P v]) is PSD (P in the
    listed localizers, u, v all half-words of the matching bidegree; by the Newton-polytope argument no other
    half-words can occur in a certificate of a bihomogeneous f).  y(f) < 0 then shows f is not in the cone."""
    meta = cert['meta']
    f = target(meta)
    y = {dihedral_key(w): Fraction(v) for w, v in cert['y'].items()}
    w0 = next(iter(f))
    tx, ty = w0.count('x'), w0.count('y')
    ok = True
    sizes = []
    for P in meta['localizers']:
        px, py = 2 * P.count('x'), 2 * P.count('y')
        if (tx - px) % 2 or (ty - py) % 2:
            continue
        hw = half_words((tx - px) // 2, (ty - py) // 2)
        M = [[y.get(dihedral_key(P + u[::-1] + P + v), Fraction(0)) for v in hw] for u in hw]
        psd = psd_exact(M)
        sizes.append((P or '1', len(hw), psd))
        ok = ok and psd
    val = sum(f.get(k, Fraction(0)) * v for k, v in y.items())
    print(f"{path}: NON-EXISTENCE  {cert['label']}")
    print(f"   recomputed from definition: lhs {meta['lhs']}_{{{meta['n']},{meta['m']}}}(X^{meta['ea']}, "
          f"Y^{meta['eb']}){' - p^mult' if meta.get('sub') == 'pmult' and 'p^mult' not in meta.get('rhs_meaning', '') else ''}, subtracted words {meta['rhs']}")
    print(f"   localized moment matrices (localizer, size, PSD exact): {sizes};  y(f) = {val}")
    good = ok and val < 0
    print(f"   => {'OK: f is not a sum of terms tau(P g^* P g), P in ' + str(meta['localizers']) if good else 'FAILED'}")
    return good


def verify_gram(path, cert):
    """Gram-block format: f == sum_b sum_{i,j} (T_b S_b T_b^T)_{ij} [P_b rev(u_i) Q_b u_j], each S_b PSD (checked
    exactly).  Then tau f = sum_b tau(P V_b^* (G_b (x) 1) Q V_b) >= 0 for X, Y >= 0 (and all Hermitian X, Y if
    every block has P = Q = '')."""
    meta = cert['meta']
    f = target(meta)
    out = {}
    herm = True
    ranks = []
    for blk in cert['blocks']:
        P, Q, words = blk['P'], blk['Q'], blk['words']
        assert P in ('', 'x', 'y') and Q in ('', 'x', 'y')
        if P or Q:
            herm = False
        S = [[Fraction(v) for v in row] for row in blk['S']]
        r = len(S)
        assert all(S[a][c] == S[c][a] for a in range(r) for c in range(r)), "S not symmetric"
        if not (pd_bareiss(S) or psd_exact(S)):
            print(f"{path}: Gram block ({P or '1'},{Q or '1'}) NOT PSD")
            return False
        T = [[int(v) for v in col] for col in blk['T_columns']]           # r columns of length N
        N = len(words)
        assert all(len(col) == N for col in T) and len(T) == r
        # G = T S T^T with a common denominator (exact big-integer arithmetic)
        from math import lcm
        D = 1
        for row in S:
            for q in row:
                D = lcm(D, q.denominator)
        Si = [[int(q * D) for q in row] for row in S]
        TS = [[sum(T[a][i] * Si[a][c] for a in range(r)) for c in range(r)] for i in range(N)]    # N x r
        for i in range(N):
            ri = P + words[i][::-1] + Q
            for j in range(N):
                gij = sum(TS[i][c] * T[c][j] for c in range(r))
                if gij:
                    add(out, ri + words[j], Fraction(gij, D))
        ranks.append((P or '1', Q or '1', r))
    s = {k: v for k, v in out.items() if v != 0}
    ok = (f == s)
    print(f"{path}: target  p_{{{meta['n']},{meta['m']}}}(X^{meta['ea']}, Y^{meta['eb']})"
          f"{' [p^mult]' if meta['lhs'] == 'pmult' else ''} - {meta.get('rhs_meaning', '')}"
          f"{' - p^mult' if meta.get('sub') == 'pmult' and 'p^mult' not in meta.get('rhs_meaning', '') else ''}")
    print(f"   recomputed from definition: A = X^{meta['ea']}, B = Y^{meta['eb']}, subtracted words: "
          f"{[(c, w) for c, w in meta['rhs']]}")
    print(f"   Gram blocks (P, Q, rank) {ranks}: all exactly PSD")
    print(f"   exact identity f == sum of Gram blocks: {'OK' if ok else 'FAILED'}")
    if ok:
        dom = "all Hermitian X, Y" if herm else "all X, Y >= 0"
        print(f"   => tau f(X,Y) >= 0 for {dom}, in every tracial von Neumann algebra (all matrix sizes).")
    return ok


def verify(path):
    with open(path) as fh:
        cert = json.load(fh)
    if cert.get('type') == 'nonexistence':
        return verify_nonexistence(path, cert)
    if cert.get('format') == 'gram':
        return verify_gram(path, cert)
    meta = cert['meta']
    f = target(meta)
    s, herm = expand(cert['terms'])
    ok = (f == s)
    nl = {}
    for t in cert['terms']:
        key = f"({t['P'] or '1'},{t['Q'] or '1'})"
        nl[key] = nl.get(key, 0) + 1
    print(f"{path}: target  p_{{{meta['n']},{meta['m']}}}(X^{meta['ea']}, Y^{meta['eb']})"
          f"{' [p^mult]' if meta['lhs'] == 'pmult' else ''} - {meta['rhs_meaning']}"
          f"{' - p^mult' if meta.get('sub') == 'pmult' and 'p^mult' not in meta.get('rhs_meaning', '') else ''}")
    print(f"   recomputed from definition: A = X^{meta['ea']}, B = Y^{meta['eb']}, subtracted words: "
          f"{[(c, w) for c, w in meta['rhs']]}")
    print(f"   {len(f)} dihedral classes in f; {len(cert['terms'])} squares {nl}; weights all > 0")
    print(f"   exact identity f == sum of terms: {'OK' if ok else 'FAILED'}")
    if ok:
        dom = "all Hermitian X, Y" if herm else "all X, Y >= 0"
        print(f"   => tau f(X,Y) >= 0 for {dom}, in every tracial von Neumann algebra (all matrix sizes).")
    else:
        diff = {k: f.get(k, 0) - s.get(k, 0) for k in set(f) | set(s) if f.get(k, 0) != s.get(k, 0)}
        print("   mismatch on", len(diff), "classes, e.g.", list(diff.items())[:3])
    return ok


if __name__ == "__main__":
    sys.set_int_max_str_digits(0)          # certificates may contain rationals with many digits
    res = [verify(p) for p in sys.argv[1:]]
    print("ALL OK" if all(res) else "SOME FAILED")
    sys.exit(0 if all(res) else 1)
