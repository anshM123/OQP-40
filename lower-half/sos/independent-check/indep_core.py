"""Independent core utilities for the internal check of the OQP 40 SOS certificates.

Written from scratch; does not import or copy anything from the authors' code.

Conventions
-----------
* A word is a Python string over the letters 'x', 'y' (X, Y Hermitian).  For Hermitian letters the adjoint of the
  matrix word u(X,Y) is the reversed word, u* = u[::-1].
* The PRIMARY equivalence used here is plain cyclic rotation only (always valid for traces): cyc(w) is the
  lexicographically least rotation of w, computed with Booth's algorithm (the authors use min over all rotations
  and reversals; we use a different algorithm and a finer equivalence).
* dih(w) = min(cyc(w), cyc(w[::-1])) is only used for diagnostics (reversal = adjoint is valid only for real parts).
* Polynomials are dicts {cyclic class: rational}.  Rationals are fractions.Fraction (exact).
"""
import itertools
import math
import sys
from fractions import Fraction

sys.set_int_max_str_digits(0)


# ----------------------------------------------------------------------------------------------------------------
# words
# ----------------------------------------------------------------------------------------------------------------
def least_rotation(s):
    """Booth's algorithm: start index of the lexicographically least rotation of s (O(len s))."""
    S = s + s
    f = [-1] * len(S)
    k = 0
    for j in range(1, len(S)):
        sj = S[j]
        i = f[j - k - 1]
        while i != -1 and sj != S[k + i + 1]:
            if sj < S[k + i + 1]:
                k = j - i - 1
            i = f[i]
        if sj != S[k + i + 1]:          # here i == -1
            if sj < S[k]:
                k = j
            f[j - k] = -1
        else:
            f[j - k] = i + 1
    return k


def cyc(w):
    """canonical representative of the rotation class of w."""
    k = least_rotation(w)
    return w[k:] + w[:k]


def dih(w):
    """canonical representative of the rotation+reversal class (diagnostics only)."""
    a, b = cyc(w), cyc(w[::-1])
    return a if a <= b else b


def bideg(w):
    return (w.count('x'), w.count('y'))


def all_words(nx, ny):
    """all words with nx letters x and ny letters y (positions of y chosen by combinations)."""
    L = nx + ny
    out = []
    for pos in itertools.combinations(range(L), ny):
        s = ['x'] * L
        for p in pos:
            s[p] = 'y'
        out.append(''.join(s))
    return out


# ----------------------------------------------------------------------------------------------------------------
# targets, built from the definitions in SOS_RESULTS.md section 0 / OQP40_RESULTS.md section 0
# ----------------------------------------------------------------------------------------------------------------
def add_to(poly, key, c):
    v = poly.get(key, 0) + c
    if v == 0:
        poly.pop(key, None)
    else:
        poly[key] = v


def p_words(n, m):
    """all words over {A,B} with exactly n letters A and m letters B (choose the A positions)."""
    L = n + m
    for posA in itertools.combinations(range(L), n):
        s = ['B'] * L
        for p in posA:
            s[p] = 'A'
        yield ''.join(s)


def substitute(wordAB, ea, eb):
    """A -> X^ea, B -> Y^eb."""
    return ''.join(('x' * ea) if c == 'A' else ('y' * eb) for c in wordAB)


def poly_p(n, m, ea, eb):
    """p_{n,m}(X^ea, Y^eb) = C(n+m,n)^{-1} sum over words with n A's and m B's, as cyclic classes."""
    tot = math.comb(n + m, n)
    cnt = 0
    acc = {}
    for w in p_words(n, m):
        cnt += 1
        add_to(acc, cyc(substitute(w, ea, eb)), 1)
    assert cnt == tot
    return {k: Fraction(v, tot) for k, v in acc.items()}


def weak_compositions(n, parts):
    if parts == 1:
        yield (n,)
        return
    for first in range(n + 1):
        for rest in weak_compositions(n - first, parts - 1):
            yield (first,) + rest


def poly_pmult(n, m, ea, eb):
    """p^mult_{n,m}(A,B) = m^{-n} sum_{J in [m]^n} tr prod_{j=1}^m (B A^{N_j(J)}).
    Computed via weak compositions N of n into m parts with multinomial multiplicity n!/prod N_j! (= #J with counts N)."""
    acc = {}
    tot = 0
    for N in weak_compositions(n, m):
        mult = math.factorial(n)
        for Nj in N:
            mult //= math.factorial(Nj)
        tot += mult
        w = ''.join(('y' * eb) + ('x' * (ea * Nj)) for Nj in N)
        add_to(acc, cyc(w), mult)
    assert tot == m ** n
    return {k: Fraction(v, m ** n) for k, v in acc.items()}


def poly_pmult_bruteforce(n, m, ea, eb):
    """same as poly_pmult but literally enumerating J in [m]^n (cross-check)."""
    acc = {}
    for J in itertools.product(range(m), repeat=n):
        N = [0] * m
        for l in J:
            N[l] += 1
        w = ''.join(('y' * eb) + ('x' * (ea * Nj)) for Nj in N)
        add_to(acc, cyc(w), 1)
    return {k: Fraction(v, m ** n) for k, v in acc.items()}


def frac_word(n, m, ea, eb):
    """word of (A^{n/m} B)^m with A = X^ea, B = Y^eb; requires ea*n/m to be an integer."""
    assert (ea * n) % m == 0, "A^{n/m} is not a polynomial in X"
    k = ea * n // m
    return ('x' * k + 'y' * eb) * m


def poly_sub(a, b):
    out = dict(a)
    for k, v in b.items():
        add_to(out, k, -v)
    return out


def is_reversal_symmetric(poly):
    """coefficient of a cyclic class equals that of its reversed class."""
    for k, v in poly.items():
        if poly.get(cyc(k[::-1]), 0) != v:
            return False
    return True


def to_dihedral(poly):
    out = {}
    for k, v in poly.items():
        add_to(out, dih(k), v)
    return out


# ----------------------------------------------------------------------------------------------------------------
# exact PSD tests
# ----------------------------------------------------------------------------------------------------------------
def ldl_pd_exact(S):
    """Exact LDL^T without pivoting on a symmetric rational matrix (list of lists of Fraction or flint fmpq).
    Returns (is_PD, pivots).  S is PD iff every pivot is > 0."""
    r = len(S)
    A = [list(row) for row in S]
    pivots = []
    for k in range(r):
        piv = A[k][k]
        pivots.append(piv)
        if not piv > 0:
            return False, pivots
        rowk = A[k]
        for i in range(k + 1, r):
            aki = rowk[i]
            if aki == 0:
                continue
            l = aki / piv
            rowi = A[i]
            for j in range(i, r):          # maintain the upper triangle of the Schur complement
                rowi[j] = rowi[j] - l * rowk[j]
    return True, pivots


def psd_exact(S):
    """Exact PSD test of a symmetric rational matrix (any rank): symmetric elimination; a zero pivot requires the
    whole remaining row to vanish.  Returns (is_PSD, rank)."""
    r = len(S)
    A = [list(row) for row in S]
    alive = list(range(r))
    rank = 0
    while alive:
        k = alive.pop(0)
        piv = A[k][k]
        if piv < 0:
            return False, rank
        if piv == 0:
            if any(A[k][j] != 0 for j in alive):
                return False, rank
            continue
        rank += 1
        for i in alive:
            aki = A[k][i]
            if aki == 0:
                continue
            l = aki / piv
            for j in alive:
                A[i][j] = A[i][j] - l * A[k][j]
    return True, rank


def components(n, edges):
    """connected components of an undirected graph on range(n)."""
    parent = list(range(n))

    def find(a):
        while parent[a] != a:
            parent[a] = parent[parent[a]]
            a = parent[a]
        return a
    for a, b in edges:
        ra, rb = find(a), find(b)
        if ra != rb:
            parent[ra] = rb
    comp = {}
    for a in range(n):
        comp.setdefault(find(a), []).append(a)
    return list(comp.values())
