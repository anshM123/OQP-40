"""High-precision check of the gap identity D1 for d = 3, 4 (independent code).

    gap(n,m) := A_{n,m}(A,B) - Tr(A^n E_A(B)^m)  =?=  m(m-1) int int s^{m-2} tau^n rho_{B,A}(s,tau) ds dtau,
    rho_{B,A}(s,tau) = (1/2pi) sum_i |Im xi_i|,  xi_i the roots of det(B - s - xi (A - tau)).

Left side: exact rational (word-sum recursion over Q).
Right side: nested composite Gauss-Legendre quadrature in arb arithmetic (python-flint, 160-bit):
  - exact pencil polynomial p(xi; s, tau) in Q[xi, s, tau] (sympy determinant, converted to flint mpoly);
  - D(s, tau) = product of the s-dependent irreducible factors of disc_xi(p). For fixed tau, the real roots
    of D(., tau) cut the s-line into intervals on which the number of non-real xi is constant; rho is
    analytic inside, with square-root behaviour at the ends;
  - every interval is subdivided geometrically around ALL complex roots of D(., tau) (the branch points
    of xi(s)), so each piece is at a distance >= its half-length from every singularity;
  - each piece: x = a + (b-a)(1-cos th)/2, then N-point Gauss-Legendre in th;
  - tau: gaps of spec A, cut at the real roots of T = disc_s(D) * lc_s(D) and graded around its
    complex roots, same rule.
Convergence is shown by running N and 2N. Also checked through the same quadrature: the slice formula
int rho(s,tau) ds = m(tau) at every tau node.

usage: python c2_quad_D1.py CASE N   (CASE in 0..7)
"""
import sys
import time
from math import comb

import flint
import sympy as sp
from flint import acb, acb_poly, arb, fmpq, fmpq_mat, fmpq_mpoly_ctx, fmpq_poly

flint.ctx.prec = 160
PI = arb.pi()
TWO = arb(2)

CASES = {
    0: ("d=3 generic, singular A, PSD B", [0, fmpq(1, 2), 1],
        [[2, 1, fmpq(1, 2)], [1, fmpq(3, 2), -1], [fmpq(1, 2), -1, 2]]),
    1: ("d=3 repeated eigenvalue + singular A: A=diag(0,1,1), PSD B", [0, 1, 1],
        [[fmpq(3, 2), fmpq(1, 2), -1], [fmpq(1, 2), 2, fmpq(1, 3)], [-1, fmpq(1, 3), fmpq(5, 4)]]),
    2: ("d=3 repeated eigenvalue A=diag(1/4,1/4,1), rank-one B", [fmpq(1, 4), fmpq(1, 4), 1],
        "rank1:1,2,-1"),
    3: ("d=3 indefinite A and B (Hermitian D1)", [fmpq(-1, 2), fmpq(1, 3), 1],
        [[1, 2, -1], [2, -1, fmpq(1, 2)], [-1, fmpq(1, 2), fmpq(-1, 3)]]),
    4: ("d=4 A=diag(0,1/3,1/3,1), PSD rank-3 B", [0, fmpq(1, 3), fmpq(1, 3), 1],
        "rank3"),
    5: ("d=3 complex Hermitian B, A=diag(0,2/5,1)", [0, fmpq(2, 5), 1],
        "complex"),
    6: ("d=4 projection A=diag(0,0,1,1), PSD B", [0, 0, 1, 1],
        "rank4"),
    7: ("d=4 generic A=diag(0,1/4,3/5,1), PSD B", [0, fmpq(1, 4), fmpq(3, 5), 1],
        "rank4"),
}


def build_B(spec, d):
    if isinstance(spec, list):
        return sp.Matrix([[sp.Rational(int(fmpq(x).p), int(fmpq(x).q)) for x in row] for row in spec]), False
    if spec.startswith("rank1"):
        v = sp.Matrix([sp.Integer(int(x)) for x in spec.split(":")[1].split(",")])
        return v * v.T, False
    if spec == "rank3":
        X = sp.Matrix([[1, 0, 2], [-1, 1, 1], [2, 1, -1], [0, 1, 1]]) / 2
        return X * X.T, False
    if spec == "rank4":
        X = sp.Matrix([[1, 0, 2, 1], [-1, 1, 1, 0], [2, 1, -1, 1], [0, 1, 1, -2]]) / 2
        return X * X.T, False
    if spec == "complex":
        Z = sp.Matrix([[1 + sp.I, 2, -sp.I], [0, 1 - 2 * sp.I, 1], [sp.I, -1, 1 + sp.I]]) / 2
        return (Z * Z.H).applyfunc(sp.expand), True
    raise ValueError(spec)


def q_of(x):
    x = sp.expand(x)
    if not getattr(x, "is_Rational", False):
        x = sp.nsimplify(x, rational=True)
    x = sp.Rational(x)
    return fmpq(int(x.p), int(x.q))


def exact_gaps(levels, Bsym, cplx, Nmax):
    d = len(levels)
    if not cplx:
        A = fmpq_mat(d, d, [levels[i] if i == j else 0 for i in range(d) for j in range(d)])
        B = fmpq_mat(d, d, [q_of(Bsym[i, j]) for i in range(d) for j in range(d)])
        dd, fac = d, 1
    else:
        dd, fac = 2 * d, 2
        A = fmpq_mat(dd, dd, [0] * (dd * dd))
        B = fmpq_mat(dd, dd, [0] * (dd * dd))
        for i in range(d):
            A[i, i] = levels[i]
            A[i + d, i + d] = levels[i]
            for j in range(d):
                re, im = q_of(sp.re(Bsym[i, j])), q_of(sp.im(Bsym[i, j]))
                B[i, j] = re
                B[i + d, j + d] = re
                B[i, j + d] = -im
                B[i + d, j] = im
    lev2 = list(levels) + (list(levels) if cplx else [])
    E = fmpq_mat(dd, dd, [B[i, j] if lev2[i] == lev2[j] else 0 for i in range(dd) for j in range(dd)])
    I = fmpq_mat(dd, dd, [1 if i == j else 0 for i in range(dd) for j in range(dd)])

    def tr(M):
        s = fmpq(0)
        for i in range(dd):
            s += M[i, i]
        return s

    coeffs, ws = [I], {(0, 0): tr(I)}
    for N in range(1, Nmax + 1):
        new = [None] * (N + 1)
        for j, C in enumerate(coeffs):
            CA, CB = C * A, C * B
            new[j] = CA if new[j] is None else new[j] + CA
            new[j + 1] = CB if new[j + 1] is None else new[j + 1] + CB
        coeffs = new
        for m in range(N + 1):
            ws[(N - m, m)] = tr(coeffs[m])
    Ap, Ep = [I], [I]
    for _ in range(Nmax):
        Ap.append(Ap[-1] * A)
        Ep.append(Ep[-1] * E)
    gaps = {(n, m): (v / comb(n + m, n) - tr(Ap[n] * Ep[m])) / fac for (n, m), v in ws.items()}
    alphas = sorted(set(levels))
    w = {}
    for a in range(len(alphas)):
        for b in range(a + 1, len(alphas)):
            tot = fmpq(0)
            for i in range(dd):
                for j in range(dd):
                    if lev2[i] == alphas[a] and lev2[j] == alphas[b]:
                        tot += B[i, j] * B[i, j]
            w[(a, b)] = tot / fac
    return gaps, alphas, w


def pencil_poly(levels, Bsym):
    xi, s, tau = sp.symbols("xi s tau")
    d = len(levels)
    Asym = sp.diag(*[sp.Rational(int(fmpq(x).p), int(fmpq(x).q)) for x in levels])
    p = sp.expand((Bsym - s * sp.eye(d) - xi * (Asym - tau * sp.eye(d))).det(method="berkowitz"))
    P = sp.Poly(p, xi, s, tau)
    ctx = fmpq_mpoly_ctx.get(("xi", "s", "tau"), "lex")
    dct = {}
    for monom, c in P.terms():
        c = sp.nsimplify(c)
        assert sp.im(c) == 0, "pencil polynomial must have real coefficients"
        dct[monom] = q_of(sp.re(c))
    return ctx.from_dict(dct), ctx


def nested(Pm):
    out = {}
    for (j, k, l), c in Pm.to_dict().items():
        out.setdefault(j, {}).setdefault(k, {})[l] = c
    return out


def coeffs_in_s(nest_j, t):
    if not nest_j:
        return [arb(0)]
    K = max(nest_j)
    out = []
    for k in range(K + 1):
        acc = arb(0)
        for l, c in nest_j.get(k, {}).items():
            acc += arb(c) * t ** l
        out.append(acc)
    return out


def horner(cs, x):
    acc = arb(0)
    for c in reversed(cs):
        acc = acc * x + c
    return acc


def roots_robust(coeffs):
    """all complex roots of a polynomial with arb coefficients (low -> high)"""
    while len(coeffs) > 1 and abs(coeffs[-1]) < TWO ** -140:
        coeffs = coeffs[:-1]
    if len(coeffs) <= 1:
        return []
    for tol_bits in (110, 80):
        try:
            return acb_poly([acb(c) for c in coeffs]).roots(tol=TWO ** -tol_bits, maxprec=8000)
        except ValueError:
            continue
    # fallback (flint's simultaneous iteration can stall on close roots): mpmath Durand-Kerner at 70 digits
    import mpmath as mp
    with mp.workdps(70):
        cc = [mp.mpf(c.mid().str(60, radius=False)) for c in coeffs]
        rts, err = mp.polyroots(cc[::-1], maxsteps=2000, extraprec=600, error=True)
        if err > mp.mpf(10) ** -40:
            raise ValueError(f"root isolation failed (mpmath error {err})")
        FALLBACKS[0] += 1
        return [acb(arb(mp.nstr(mp.re(r), 60)), arb(mp.nstr(mp.im(r), 60))) for r in rts]


FALLBACKS = [0]


def sum_abs_im(cs_xi, s):
    rts = roots_robust([horner(cs, s) for cs in cs_xi])
    tot = arb(0)
    for r in rts:
        tot += abs(r.imag).mid()
    return tot


def graded_pieces(a, b, sing, max_depth=80):
    """split [a,b] (floats) into pieces, each at distance >= half its length from every point in sing
    (complex numbers; points coinciding with a or b are ignored)"""
    out = []
    stack = [(a, b, 0)]
    L0 = b - a
    while stack:
        x, y, dep = stack.pop()
        L = y - x
        dmin = float("inf")
        for z in sing:
            if abs(z - a) < 1e-14 * L0 or abs(z - b) < 1e-14 * L0:
                continue
            zr = min(max(z.real, x), y)
            dist = abs(complex(zr, 0) - z)
            dmin = min(dmin, dist)
        if dmin >= 0.5 * L or dep >= max_depth:
            out.append((x, y))
        else:
            mid = 0.5 * (x + y)
            stack.append((x, mid, dep + 1))
            stack.append((mid, y, dep + 1))
    out.sort()
    return out


_RULES = {}


def gl_rule(N):
    if N not in _RULES:
        _RULES[N] = [arb.legendre_p_root(N, k, weight=True) for k in range(N)]
    return _RULES[N]


def cos_rule(u, v, N):
    """nodes and weights on [u,v] (arb) after x = u + (v-u)(1-cos th)/2"""
    out = []
    for (x, wx) in gl_rule(N):
        th = (x + 1) * PI / 2
        out.append((u + (v - u) * (1 - th.cos()) / 2, (v - u) * th.sin() / 2 * PI / 2 * wx))
    return out


def as_arb_endpoints(pieces, a_arb, b_arb):
    """convert float pieces into arb pieces, keeping the exact outer endpoints"""
    res = []
    for i, (x, y) in enumerate(pieces):
        xa = a_arb if i == 0 else arb(x)
        yb = b_arb if i == len(pieces) - 1 else arb(y)
        res.append((xa, yb))
    return res


def inner_moments(nestP, degxi, nestD, t, K, N):
    """F_k(t) = int s^k rho(s,t) ds, k = 0..K"""
    cs_xi = [coeffs_in_s(nestP.get(j, {}), t) for j in range(degxi + 1)]
    dco = coeffs_in_s(nestD.get(0, {}), t)
    rts = roots_robust(dco)
    allz = [complex(float(r.real.mid()), float(r.imag.mid())) for r in rts]
    real = sorted([r.real.mid() for r in rts if r.imag.contains(0) or abs(r.imag) < TWO ** -90],
                  key=lambda x: float(x))
    F = [arb(0)] * (K + 1)
    nev = 0
    for sa, sb in zip(real[:-1], real[1:]):
        if float(sb - sa) <= 0:
            continue
        if sum_abs_im(cs_xi, (sa + sb) / 2) < TWO ** -80:
            continue
        pieces = graded_pieces(float(sa), float(sb), allz)
        for (u, v) in as_arb_endpoints(pieces, sa, sb):
            for (s, wgt) in cos_rule(u, v, N):
                val = sum_abs_im(cs_xi, s) / (2 * PI) * wgt
                nev += 1
                sk = arb(1)
                for k in range(K + 1):
                    F[k] += val * sk
                    sk *= s
    return F, nev


def main():
    case = int(sys.argv[1]) if len(sys.argv) > 1 else 0
    N = int(sys.argv[2]) if len(sys.argv) > 2 else 24
    name, levels, Bspec = CASES[case]
    levels = [fmpq(x) for x in levels]
    d = len(levels)
    Bsym, cplx = build_B(Bspec, d)
    t0 = time.time()
    print(f"case {case}: {name}; N = {N} nodes per piece; prec = {flint.ctx.prec} bits")
    print(f"  A = diag{tuple(str(x) for x in levels)}; B = {Bsym.tolist()}")
    Nmax = 12
    gaps, alphas, w = exact_gaps(levels, Bsym, cplx, Nmax)

    Pm, ctx = pencil_poly(levels, Bsym)
    content, facs = Pm.discriminant("xi").factor()
    D = ctx.from_dict({(0, 0, 0): 1})
    for f, e in facs:
        if f.degrees()[1] > 0:
            D = D * f
    print(f"  disc_xi(p) factors (deg_s, deg_tau, mult): {[(f.degrees()[1], f.degrees()[2], e) for f, e in facs]}")
    nestP, nestD = nested(Pm), nested(D)
    degxi, degD_s = Pm.degrees()[0], D.degrees()[1]
    # tau singular set: roots of disc_s(D) * lc_s(D)
    T = D.discriminant("s")
    lcD = ctx.from_dict({(0, 0, l): c for (j, k, l), c in D.to_dict().items() if k == degD_s})
    t_real, t_all = [], []
    for poly in (T, lcD):
        dct = poly.to_dict()
        if not dct:
            continue
        L = max(l for (_, _, l) in dct)
        cf = [fmpq(0)] * (L + 1)
        for (_, _, l), c in dct.items():
            cf[l] += c
        fp = fmpq_poly(cf)
        if fp.degree() <= 0:
            continue
        for f, e in fp.factor()[1]:
            for r, mult in f.complex_roots():
                t_all.append(complex(float(r.real.mid()), float(r.imag.mid())))
                if r.imag.contains(0):
                    t_real.append(r.real.mid())
    tsegs = []
    for a, b in zip(alphas[:-1], alphas[1:]):
        inner = sorted([x for x in t_real if arb(a) < x < arb(b)], key=lambda x: float(x))
        pts = [arb(a)] + inner + [arb(b)]
        for (ta, tb) in zip(pts[:-1], pts[1:]):
            pieces = graded_pieces(float(ta), float(tb), t_all)
            tsegs += as_arb_endpoints(pieces, ta, tb)
    print(f"  tau: {len(tsegs)} pieces; real singular tau inside spectrum hull: "
          f"{sorted(round(float(x), 6) for x in t_real if arb(alphas[0]) < x < arb(alphas[-1]))}")

    K = Nmax - 2
    M = [[arb(0) for _ in range(Nmax + 1)] for _ in range(K + 1)]
    slice_err, nevals = 0.0, 0
    for (ta, tb) in tsegs:
        for (t, wt) in cos_rule(ta, tb, N):
            F, nev = inner_moments(nestP, degxi, nestD, t, K, N)
            nevals += nev
            mt = arb(0)
            for (a, b), wab in w.items():
                if arb(alphas[a]) < t < arb(alphas[b]):
                    mt += arb(wab) / (alphas[b] - alphas[a])
            slice_err = max(slice_err, abs(float((F[0] - mt).mid())))
            tn = arb(1)
            for n in range(Nmax + 1):
                for k in range(K + 1):
                    M[k][n] += wt * F[k] * tn
                tn *= t
    print(f"  rho evaluations: {nevals}; time {time.time() - t0:.1f}s; mpmath root fallbacks: {FALLBACKS[0]}")
    print(f"  slice formula: max over tau nodes of |int rho ds - m(tau)| = {slice_err:.3e}")
    worst, rows = 0.0, []
    for (n, m) in sorted(gaps):
        if m < 2 or n + m > Nmax:
            continue
        g = gaps[(n, m)]
        rhs = m * (m - 1) * M[m - 2][n]
        err = abs(float((rhs - arb(g)).mid()))
        rel = err / abs(float(g)) if g != 0 else err
        worst = max(worst, rel)
        rows.append((n, m, g, rhs, rel))
    for (n, m, g, rhs, rel) in rows[:: max(1, len(rows) // 12)]:
        print(f"   (n,m)=({n:2d},{m:2d})  exact gap = {float(g): .16e}   m(m-1)*integral = "
              f"{rhs.mid().str(22, radius=False)}   rel.err {rel:.1e}")
    print(f"  D1: worst relative error over {len(rows)} pairs (n,m), 2 <= m, n+m <= {Nmax}: {worst:.3e}")
    print(f"  total time {time.time() - t0:.1f}s")


if __name__ == "__main__":
    main()
