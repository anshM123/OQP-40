"""Exact tools: rational polynomial matrices, leading principal minors (Bareiss over Q[s]), and a rigorous
positivity test for univariate polynomials on (0,1) (Descartes' rule of signs with bisection, Vincent-Collins-
Akritas).  All arithmetic is exact (python-flint fmpq / fmpq_poly / fmpz)."""
from fractions import Fraction

import flint

ONE_MINUS_S = flint.fmpq_poly([1, -1])
S_POLY = flint.fmpq_poly([0, 1])


def fq(x):
    if isinstance(x, Fraction):
        return flint.fmpq(x.numerator, x.denominator)
    return flint.fmpq(x)


def bareiss_minors(M):
    """leading principal minors Delta_1..Delta_m of a square matrix of fmpq_poly (exact Bareiss).
    Raises ZeroDivisionError if a pivot vanishes identically."""
    m = len(M)
    A = [[M[i][j] for j in range(m)] for i in range(m)]
    minors = []
    prev = flint.fmpq_poly([1])
    for k in range(m):
        piv = A[k][k]
        minors.append(piv)
        if k == m - 1:
            break
        if piv == 0:
            raise ZeroDivisionError(f"pivot {k} vanishes identically")
        for i in range(k + 1, m):
            for j in range(k + 1, m):
                num = piv * A[i][j] - A[i][k] * A[k][j]
                q, r = divmod(num, prev)
                if r != 0:
                    raise ArithmeticError("Bareiss division not exact")
                A[i][j] = q
        prev = piv
    return minors


def strip_endpoints(p):
    """p = s^a (1-s)^b q with q(0) q(1) != 0; returns (a, b, q)."""
    a = 0
    while p != 0 and p(0) == 0:
        p, r = divmod(p, S_POLY)
        assert r == 0
        a += 1
    b = 0
    while p != 0 and p(1) == 0:
        p, r = divmod(p, ONE_MINUS_S)
        assert r == 0
        b += 1
    return a, b, p


def _to_fmpz(p):
    """primitive integer polynomial with the same sign as p (positive denominator)."""
    coeffs = p.coeffs()
    den = 1
    for c in coeffs:
        den = den * c.q // flint.fmpz.gcd(den, c.q) if hasattr(flint.fmpz, 'gcd') else _lcm(den, c.q)
    return flint.fmpz_poly([int(c * den) for c in coeffs])


def _lcm(a, b):
    from math import gcd
    a, b = int(a), int(b)
    return a * b // gcd(a, b)


def _intpoly(p):
    coeffs = p.coeffs()
    den = 1
    for c in coeffs:
        den = _lcm(den, int(c.q))
    return [int(c.p) * (den // int(c.q)) for c in coeffs]


def _variations(coeffs):
    sg = [1 if c > 0 else -1 for c in coeffs if c != 0]
    return sum(1 for i in range(len(sg) - 1) if sg[i] != sg[i + 1])


def _mobius(p, a, b, d):
    """coefficients of (1+u)^d p((a + b u)/(1+u)) for the fmpq_poly p of degree <= d (a, b fmpq)."""
    r = p(flint.fmpq_poly([a, b - a]))           # r(sigma) = p(a + (b-a) sigma)
    rc = r.coeffs() + [flint.fmpq(0)] * (d + 1 - len(r.coeffs()))
    R = flint.fmpq_poly(rc[::-1])                 # R(v) = v^d r(1/v)
    R1 = R(flint.fmpq_poly([1, 1]))               # R(1 + w)
    qc = R1.coeffs() + [flint.fmpq(0)] * (d + 1 - len(R1.coeffs()))
    return qc[::-1]                               # Q(u) = u^d R1(1/u)


def positive_on_open01(p, maxdepth=80):
    """rigorous: True iff p > 0 on (0,1) given p(0) != 0 != p(1) is NOT required (endpoints are stripped).
    Returns (ok, info)."""
    if p == 0:
        return False, "identically zero"
    a0, b0, q = strip_endpoints(p)
    d = q.degree()
    half = flint.fmpq(1, 2)
    if q(half) <= 0:
        return False, "nonpositive at 1/2"
    if d <= 0:
        return True, dict(s_order=a0, one_minus_s_order=b0, degree=d, intervals=1)
    stack = [(flint.fmpq(0), flint.fmpq(1), 0)]
    nint = 0
    while stack:
        a, b, depth = stack.pop()
        nint += 1
        V = _variations(_mobius(q, a, b, d))
        if V == 0:
            continue
        if depth > maxdepth:
            return False, f"max depth at [{a},{b}]"
        mid = (a + b) / 2
        if q(mid) <= 0:
            return False, f"nonpositive at {mid}"
        stack.append((a, mid, depth + 1))
        stack.append((mid, b, depth + 1))
    # endpoints of the stripped polynomial are nonzero; positivity at 1/2 and no roots in (0,1) => positive
    return True, dict(s_order=a0, one_minus_s_order=b0, degree=d, intervals=nint)
