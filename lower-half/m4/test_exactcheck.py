"""Unit tests of exactcheck.py against sympy: (1) positivity on (0,1) vs sympy real-root isolation for random
integer polynomials (with planted roots inside/outside (0,1), double roots, roots at rational points);
(2) Bareiss leading principal minors vs sympy determinants for random polynomial matrices."""
import random
import sympy as sp
import flint
from exactcheck import positive_on_open01, bareiss_minors

s = sp.symbols('s')
random.seed(7)
bad = 0
for trial in range(300):
    deg = random.randint(1, 12)
    # random polynomial, sometimes with planted roots
    roots = []
    for _ in range(random.randint(0, 3)):
        roots.append(sp.Rational(random.randint(-5, 25), random.randint(1, 20)))
    P = sp.Integer(random.choice([1, -1, 3]))
    for r_ in roots:
        P *= (s - r_) ** random.choice([1, 1, 2])
    P *= sp.Poly([random.randint(-9, 9) for _ in range(deg)] + [random.randint(1, 9)], s).as_expr()
    if random.random() < 0.3:
        P = P ** 2 + sp.Rational(random.randint(0, 3), 1000)
    P = sp.expand(P)
    if P == 0:
        continue
    # truth: positive on (0,1)?
    Q = sp.Poly(P, s)
    truth_has_root = False
    for fac, mult in sp.factor_list(P)[1]:
        F = sp.Poly(fac, s)
        if F.degree() == 0:
            continue
        cnt = F.count_roots(0, 1)            # closed interval
        cnt -= int(F.eval(0) == 0) + int(F.eval(1) == 0)
        if cnt > 0:
            truth_has_root = True
    truth = (not truth_has_root) and Q.eval(sp.Rational(1, 2)) > 0
    # strip endpoints for truth too: positive on OPEN interval allows zeros at 0, 1
    fp = flint.fmpq_poly([flint.fmpq(int(c.p), int(c.q)) for c in reversed(Q.all_coeffs())])
    ok, info = positive_on_open01(fp)
    if ok != truth:
        bad += 1
        print("MISMATCH", P, ok, truth, info)
print("positivity tests: mismatches", bad)

# Bareiss vs sympy
bad = 0
for trial in range(30):
    m = random.randint(2, 6)
    M = [[None] * m for _ in range(m)]
    Ms = sp.zeros(m, m)
    for i in range(m):
        for j in range(i, m):
            cs = [sp.Rational(random.randint(-5, 5), random.randint(1, 4)) for _ in range(random.randint(1, 4))]
            e = sum(c * s ** k for k, c in enumerate(cs))
            Ms[i, j] = Ms[j, i] = e
            fp = flint.fmpq_poly([flint.fmpq(int(c.p), int(c.q)) for c in cs])
            M[i][j] = M[j][i] = fp
    try:
        mins = bareiss_minors(M)
    except ZeroDivisionError:
        continue
    for k in range(1, m + 1):
        d = sp.Poly(sp.expand(Ms[:k, :k].det()), s)
        fd = flint.fmpq_poly([flint.fmpq(int(c.p), int(c.q)) for c in reversed(d.all_coeffs())]) if d.degree() >= 0 else flint.fmpq_poly([0])
        if mins[k - 1] != fd:
            bad += 1
            print("MINOR MISMATCH", k)
print("Bareiss tests: mismatches", bad)
