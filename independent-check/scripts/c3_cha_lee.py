"""Cha-Lee family (arXiv:2603.19927, Sec. II and App. A, Prop. 6; Dinh arXiv:2605.17782, Sec. 4):

    A_x = [[1,0,0],[0,x,-x],[0,-x,x]] = 1 (+) xC,   B_x = [[x,-x,0],[-x,x,0],[0,0,1]] = xC (+) 1,
    C = [[1,-1],[-1,1]],  x > 0.

Checks (exact, polynomials in x over Q):
  [C1] Cha-Lee Prop. 1 / Dinh (4.5): Tr(A^5 B^5) = 32x^5 + 256x^10;
       Dinh (4.7) = Cha-Lee R(x): A_{5,5}(A_x,B_x) = x^4/126 (5 + 1422x + 1675x^2 + 3130x^3 + 4875x^4 + 5930x^5 + 4881x^6);
       Dinh (4.3): Tr(A^5 E(B)^5) = x^5 (1 + (1+x)^5), with E = E_{A_x} for x != 1/2.
  [C2] exact values at x = 1e-3, 1e-6, 1e-9, 1e-12, 1e-15; Dinh's decimals (4.4), (4.8).
  [C3] for all 0 <= n, m <= 12: gap_{n,m}(x) = A_{n,m}(A_x,B_x) - Tr(A_x^n E^m) is a polynomial in x;
       count its roots in (0, oo) (exact isolation) and its sign: the conjecture on the whole family.
       Also the two-sided bound D3 (l_min(B_x) = 0, l_max(B_x) = max(1, 2x)) as polynomial inequalities,
       and the m = 2 equality gap = 2 S_n.
  [C4] x = 1/2, where A_x has the double eigenvalue 1 and the pinching is coarser: exact check.
  [C5] D1 by high-precision quadrature (c2 machinery) at x = 1/1000 and x = 1/10^6.
"""
import sys
import time
from math import comb

import flint
import sympy as sp
from flint import arb, fmpq, fmpq_mat, fmpq_poly, fmpq_mpoly_ctx

sys.path.insert(0, __file__.rsplit("\\", 1)[0] if "\\" in __file__ else ".")
import c2_quad_D1 as Q2  # noqa: E402  (own quadrature code)

X = fmpq_poly([0, 1])
ONE = fmpq_poly([1])
ZERO = fmpq_poly([0])


def pm(rows):
    return [[r if isinstance(r, fmpq_poly) else fmpq_poly([r]) for r in row] for row in rows]


def mmul(P, Qm):
    n = len(P)
    return [[sum((P[i][k] * Qm[k][j] for k in range(n)), ZERO) for j in range(n)] for i in range(n)]


def madd(P, Qm):
    return [[P[i][j] + Qm[i][j] for j in range(len(P))] for i in range(len(P))]


def mtr(P):
    return sum((P[i][i] for i in range(len(P))), ZERO)


def eye3():
    return pm([[1, 0, 0], [0, 1, 0], [0, 0, 1]])


A = pm([[1, 0, 0], [0, X, -X], [0, -X, X]])
B = pm([[X, -X, 0], [-X, X, 0], [0, 0, 1]])
# eigenprojections of A_x (x-independent): e1 (eig 1), v2 = (0,1,-1)/sqrt2 (eig 2x), v3 = (0,1,1)/sqrt2 (eig 0)
h = fmpq(1, 2)
Q1 = pm([[1, 0, 0], [0, 0, 0], [0, 0, 0]])
Q2m = pm([[0, 0, 0], [0, h, -h], [0, -h, h]])
Q3 = pm([[0, 0, 0], [0, h, h], [0, h, h]])
PROJ = [Q3, Q2m, Q1]                     # eigenvalues 0, 2x, 1 (ordered for x < 1/2)
EIG = [ZERO, 2 * X, ONE]


def pinch(Bm, projs):
    out = [[ZERO] * 3 for _ in range(3)]
    for P in projs:
        out = madd(out, mmul(mmul(P, Bm), P))
    return out


def word_sums(Am, Bm, Nmax):
    coeffs, ws = [eye3()], {(0, 0): mtr(eye3())}
    for N in range(1, Nmax + 1):
        new = [None] * (N + 1)
        for j, Cm in enumerate(coeffs):
            CA, CB = mmul(Cm, Am), mmul(Cm, Bm)
            new[j] = CA if new[j] is None else madd(new[j], CA)
            new[j + 1] = CB if new[j + 1] is None else madd(new[j + 1], CB)
        coeffs = new
        for m in range(N + 1):
            ws[(N - m, m)] = mtr(coeffs[m])
    return ws


def mpow(Pm, k):
    R = eye3()
    for _ in range(k):
        R = mmul(R, Pm)
    return R


def positive_roots(p):
    """real roots of p in (0, oo) via exact isolation (after removing the factor x^k)"""
    if p == 0:
        return "identically zero"
    cf = p.coeffs()
    k = 0
    while cf[k] == 0:
        k += 1
    q = fmpq_poly(cf[k:])
    out = []
    if q.degree() <= 0:
        return out
    for f, e in q.factor()[1]:
        for r, mult in f.complex_roots():
            if r.imag.contains(0) and r.real > 0:
                out.append((float(r.real.mid()), e))
            elif r.imag.contains(0) and r.real.contains(0):
                out.append(("ambiguous", e))
    return out


def lowest_term(p):
    cf = p.coeffs()
    k = 0
    while k < len(cf) and cf[k] == 0:
        k += 1
    return k, cf[k] if k < len(cf) else None


def main():
    t0 = time.time()
    Nmax = 24
    ws = word_sums(A, B, Nmax)
    E = pinch(B, PROJ)
    print("[C0] E_{A_x}(B_x) in the eigenbasis (v3, v2, e1) of A_x:",
          [str(sum((mmul(mmul(P, E), P)[i][i] for i in range(3)), ZERO)) for P in PROJ])
    # [C1]
    tr55 = mtr(mmul(mpow(A, 5), mpow(B, 5)))
    p55 = ws[(5, 5)] / comb(10, 5)
    dinh47 = fmpq_poly([0, 0, 0, 0, 5, 1422, 1675, 3130, 4875, 5930, 4881]) / 126
    pin55 = mtr(mmul(mpow(A, 5), mpow(E, 5)))
    dinh43 = X ** 5 * (1 + (1 + X) ** 5)
    print(f"[C1] Tr(A^5B^5) = {tr55};  == 32x^5+256x^10: {tr55 == 32 * X**5 + 256 * X**10}")
    print(f"     A_55(A_x,B_x) == Dinh (4.7) / Cha-Lee R(x): {p55 == dinh47}")
    print(f"     Tr(A^5 E^5) == x^5(1+(1+x)^5) (Dinh 4.3): {pin55 == dinh43}")
    gap55 = p55 - pin55
    print(f"     gap_55(x) = {gap55}")
    print(f"     L-R (Cha-Lee) = {tr55 - p55}")
    # [C2]
    for e in (3, 6, 9, 12, 15):
        xv = fmpq(1, 10 ** e)
        a, pv, tv = p55(xv), pin55(xv), tr55(xv)
        print(f"[C2] x=1e-{e}: A_55 = {float(a):.10e}, Tr(A^5E^5) = {float(pv):.10e}, Tr(A^5B^5) = {float(tv):.10e}, "
              f"gap = {float(a - pv):.10e} (>0: {a - pv > 0}), A_55/Tr(A^5B^5) = {float(a / tv):.6e}")
    # [C3]
    bad, rows = [], 0
    lo_bad, hi_bad, eq_bad = 0, 0, 0
    Epow = [eye3()]
    Apow = [eye3()]
    for _ in range(12):
        Epow.append(mmul(Epow[-1], E))
        Apow.append(mmul(Apow[-1], A))
    # weights w_jk = ||Q_j B Q_k||_F^2 for the three eigenprojections (polynomials in x)
    wjk = {}
    for j in range(3):
        for k in range(j + 1, 3):
            M = mmul(mmul(PROJ[j], B), PROJ[k])
            wjk[(j, k)] = sum((M[i][l] * M[i][l] for i in range(3) for l in range(3)), ZERO)
    print(f"[C3] w_jk (pairs of eigenvalues 0,2x,1): " + ", ".join(f"{k}: {v}" for k, v in wjk.items()))
    for n in range(0, 13):
        for m in range(0, 13):
            g = ws[(n, m)] / comb(n + m, n) - mtr(mmul(Apow[n], Epow[m]))
            rows += 1
            pr = positive_roots(g)
            k, c = lowest_term(g)
            if m >= 2:
                if g == 0 or pr or c is None or c <= 0:
                    bad.append((n, m, str(g)[:80], pr))
                # D3 for 0 < x < 1/2: l_min(B_x) = 0, l_max(B_x) = 1  -> 0 <= gap <= m(m-1) S_n (m > 2), = 2 S_n (m = 2)
                Sn = ZERO
                for (j, kk), wv in wjk.items():
                    xj, xk = EIG[j], EIG[kk]
                    Sn += wv * sum((xj ** r * xk ** (n - r) for r in range(n + 1)), ZERO) / (n + 1)
                if m == 2:
                    eq_bad += (g != 2 * Sn)
                else:
                    diff = m * (m - 1) * Sn - g          # must be >= 0 on (0, 1/2)
                    roots = [r for r in positive_roots(diff) if isinstance(r[0], float) and r[0] < 0.5]
                    kk2, c2 = lowest_term(diff)
                    if diff != 0 and (roots or (c2 is not None and c2 < 0)):
                        hi_bad += 1
            else:
                if g != 0:
                    bad.append((n, m, "m<=1 but gap != 0", pr))
    print(f"[C3] gap_(n,m)(x) for 0<=n,m<=12 ({rows} polynomials): problems = {len(bad)}  "
          f"(problem = zero polynomial for m>=2, a root in (0,oo), or negative lowest coefficient)")
    for b in bad[:10]:
        print("     ", b)
    print(f"     D3 on 0<x<1/2: m=2 equality failures {eq_bad}; upper-bound failures {hi_bad}")
    # [C4] x = 1/2: A has double eigenvalue 1 -> coarser pinching
    xv = fmpq(1, 2)
    Ah = fmpq_mat(3, 3, [1, 0, 0, 0, xv, -xv, 0, -xv, xv])
    Bh = fmpq_mat(3, 3, [xv, -xv, 0, -xv, xv, 0, 0, 0, 1])
    # eigenvalue 1: span{e1, v2}; eigenvalue 0: v3
    P1 = fmpq_mat(3, 3, [1, 0, 0, 0, h, -h, 0, -h, h])
    P0 = fmpq_mat(3, 3, [0, 0, 0, 0, h, h, 0, h, h])
    assert Ah * P1 == P1 and Ah * P0 == fmpq_mat(3, 3, [0] * 9)
    Eh = P1 * Bh * P1 + P0 * Bh * P0
    I3 = fmpq_mat(3, 3, [1, 0, 0, 0, 1, 0, 0, 0, 1])
    worst = None
    cnt = 0
    for n in range(0, 11):
        for m in range(0, 11):
            # exact word sum at x = 1/2 from the polynomial word sums
            val = ws[(n, m)](xv) / comb(n + m, n)
            Mpow = I3
            for _ in range(n):
                Mpow = Mpow * Ah
            for _ in range(m):
                Mpow = Mpow * Eh
            pv = sum((Mpow[i, i] for i in range(3)), fmpq(0))
            g = val - pv
            cnt += 1
            if m >= 2 and (worst is None or g < worst):
                worst = g
    print(f"[C4] x = 1/2 (coarser pinching, A has eigenvalue 1 twice): {cnt} (n,m) with n,m<=10; min gap over m>=2: "
          f"{float(worst):.6e} (>0: {worst > 0})")
    print(f"     time so far {time.time() - t0:.1f}s")
    # [C5] D1 by quadrature at x = 1/1000 (and 1/10^6) with the c2 machinery, general (non-diagonal) A
    for xv, N in ((fmpq(1, 1000), 32), (fmpq(1, 1000), 48), (fmpq(1, 10 ** 6), 48)):
        d1_quadrature(xv, N, ws)
    print(f"total time {time.time() - t0:.1f}s")


def d1_quadrature(xv, N, ws):
    t0 = time.time()
    xs = sp.Rational(int(xv.p), int(xv.q))
    Asym = sp.Matrix([[1, 0, 0], [0, xs, -xs], [0, -xs, xs]])
    Bsym = sp.Matrix([[xs, -xs, 0], [-xs, xs, 0], [0, 0, 1]])
    xi, s, tau = sp.symbols("xi s tau")
    p = sp.expand((Bsym - s * sp.eye(3) - xi * (Asym - tau * sp.eye(3))).det(method="berkowitz"))
    P = sp.Poly(p, xi, s, tau)
    ctx = fmpq_mpoly_ctx.get(("xi", "s", "tau"), "lex")
    Pm = ctx.from_dict({mon: Q2.q_of(c) for mon, c in P.terms()})
    content, facs = Pm.discriminant("xi").factor()
    D = ctx.from_dict({(0, 0, 0): 1})
    for f, e in facs:
        if f.degrees()[1] > 0:
            D = D * f
    nestP, nestD = Q2.nested(Pm), Q2.nested(D)
    degxi, degD_s = Pm.degrees()[0], D.degrees()[1]
    T = D.discriminant("s")
    t_real, t_all = [], []
    dct = T.to_dict()
    if dct:
        L = max(l for (_, _, l) in dct)
        cf = [fmpq(0)] * (L + 1)
        for (_, _, l), c in dct.items():
            cf[l] += c
        fp = fmpq_poly(cf)
        if fp.degree() > 0:
            for f, e in fp.factor()[1]:
                for r, mult in f.complex_roots():
                    t_all.append(complex(float(r.real.mid()), float(r.imag.mid())))
                    if r.imag.contains(0):
                        t_real.append(r.real.mid())
    alphas = [fmpq(0), 2 * xv, fmpq(1)]
    tsegs = []
    for a, b in zip(alphas[:-1], alphas[1:]):
        inner = sorted([z for z in t_real if arb(a) < z < arb(b)], key=lambda z: float(z))
        pts = [arb(a)] + inner + [arb(b)]
        for (ta, tb) in zip(pts[:-1], pts[1:]):
            tsegs += Q2.as_arb_endpoints(Q2.graded_pieces(float(ta), float(tb), t_all), ta, tb)
    K, Nn = 8, 8
    M = [[arb(0) for _ in range(Nn + 1)] for _ in range(K + 1)]
    for (ta, tb) in tsegs:
        for (t, wt) in Q2.cos_rule(ta, tb, N):
            F, nev = Q2.inner_moments(nestP, degxi, nestD, t, K, N)
            tn = arb(1)
            for n in range(Nn + 1):
                for k in range(K + 1):
                    M[k][n] += wt * F[k] * tn
                tn *= t
    # exact gaps at xv
    pin = {}
    E = [xv, (1 + xv) / 2, (1 + xv) / 2]     # E in the eigenbasis (e1, v2, v3), eigenvalues (1, 2x, 0)
    eig = [fmpq(1), 2 * xv, fmpq(0)]
    worst = 0.0
    out = []
    for n in range(0, 9):
        for m in range(2, 9):
            g = ws[(n, m)](xv) / comb(n + m, n) - sum((eig[i] ** n * E[i] ** m for i in range(3)), fmpq(0))
            rhs = m * (m - 1) * M[m - 2][n]
            rel = abs(float((rhs - arb(g)).mid())) / abs(float(g))
            worst = max(worst, rel)
            if (n, m) in ((5, 5), (0, 2), (3, 4), (8, 8), (1, 6)):
                out.append(f"(n,m)=({n},{m}) gap={float(g):.12e} quad={rhs.mid().str(16, radius=False)} rel {rel:.1e}")
    print(f"[C5] D1 quadrature at x = {xv} (N={N}, {len(tsegs)} tau pieces, {time.time() - t0:.1f}s): worst rel. error "
          f"over 0<=n<=8, 2<=m<=8: {worst:.3e}")
    for o in out:
        print("      ", o)


if __name__ == "__main__":
    main()
