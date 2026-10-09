"""Referee helper module (independent of the authors' code).

Ball-arithmetic (python-flint acb_mat) matrix utilities for the (3,3) inequality
    f(A,B) := tr(A^3 B^3) + 2 Re tr(A^2 B A B^2) - 3 tr((AB)^3)  >= 0.
All inputs are converted exactly from float64 (or from Python ints / Fractions), so every enclosure produced here
is a rigorous enclosure of the exact value for the exact (converted) matrices.
"""
import itertools
import numpy as np
from flint import arb, acb, arb_mat, acb_mat, ctx

ctx.prec = 256


def set_prec(bits):
    ctx.prec = bits


def to_acb(M):
    """Exact conversion of a numpy (complex) float64 array to acb_mat."""
    M = np.asarray(M)
    n, m = M.shape
    rows = []
    for i in range(n):
        row = []
        for j in range(m):
            z = complex(M[i, j])
            row.append(acb(arb(z.real), arb(z.imag)))
        rows.append(row)
    return acb_mat(rows)


def ctrans(M):
    """Conjugate transpose of an acb_mat."""
    return M.transpose().conjugate()


def herm_from_factor(X, delta=0.0):
    """Exact X X^* + delta I (as an acb_mat), X float64 array. PSD exactly; PD if delta > 0 or X invertible."""
    Xa = to_acb(X)
    M = Xa * ctrans(Xa)
    if delta:
        n = M.nrows()
        D = acb_mat([[acb(arb(delta)) if i == j else acb(0) for j in range(n)] for i in range(n)])
        M = M + D
    return M


def congruence(U, lam):
    """Exact U diag(lam) U^*: PD whenever U is invertible and lam > 0 (congruence of a PD diagonal)."""
    Ua = to_acb(U)
    n = len(lam)
    D = acb_mat([[acb(arb(float(lam[i]))) if i == j else acb(0) for j in range(n)] for i in range(n)])
    return Ua * D * ctrans(Ua)


def diag_acb(vals):
    n = len(vals)
    return acb_mat([[acb(vals[i]) if i == j else acb(0) for j in range(n)] for i in range(n)])


def tr(M):
    return M.trace()


def f33(A, B):
    """Returns (f, lhs, rhs) as acb: lhs = tr A^3B^3 + 2 Re tr A^2BAB^2, rhs = 3 tr (AB)^3, f = lhs - rhs."""
    A2 = A * A
    A3 = A2 * A
    B2 = B * B
    B3 = B2 * B
    AB = A * B
    t1 = tr(A3 * B3)
    t2 = tr(A2 * B * A * B2)
    t3 = tr(AB * AB * AB)
    lhs = t1.real + 2 * t2.real
    rhs = 3 * t3.real
    return lhs - rhs, lhs, rhs, (t1, t2, t3)


def words33():
    out = []
    for pos in itertools.combinations(range(6), 3):
        w = ['B'] * 6
        for p in pos:
            w[p] = 'A'
        out.append(''.join(w))
    return out


def word_trace(word, A, B):
    M = None
    for ch in word:
        X = A if ch == 'A' else B
        M = X if M is None else M * X
    return tr(M)


def p33_direct(A, B):
    """Average of tr W over the 20 words with 3 A's and 3 B's (computed word by word)."""
    s = acb(0)
    for w in words33():
        s += word_trace(w, A, B)
    return s / 20


def kappa(x, y, z):
    return (x + y + z) * (x * x + y * y + z * z) - 9 * x * y * z


def arb_lower(x):
    """Lower endpoint of an arb as a Python float (rounded down conservatively by flint's lower())."""
    return float(x.lower())


def arb_upper(x):
    return float(x.upper())
