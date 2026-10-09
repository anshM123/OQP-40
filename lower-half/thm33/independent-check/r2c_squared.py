"""Referee: third route for (II), (III) from the cleared forms of r2b_closed_forms.py.
(II) numerator = a + d PQ, a > 0 (positive coefficients). If d < 0 one needs a^2 - d^2 (C+5)(C+4B+5) > 0.
(III) numerator = b P + c Q, b > 0. If c < 0 one needs b^2 (C+5) - c^2 (C+4B+5) > 0.
We test whether these polynomials (in B, C > 0) have only positive coefficients (sufficient)."""
import sympy as sp
B, C = sp.symbols('B C', positive=True)
a2 = 2*(12*B**2*C + 60*B**2 + 7*B*C**2 + 150*B*C + 375*B + 11*C**3 + 45*C**2 + 225*C + 375)
d2 = 2*(6*B**2 + 5*B*C + 45*B - C**2 + 30*C + 75)
b3 = 4*(144*B**4 + 232*B**3*C + 1320*B**3 + 121*B**2*C**2 + 1370*B**2*C + 3825*B**2 + 18*B*C**3 + 420*B*C**2 + 2550*B*C + 4500*B + 5*C**4 + 60*C**3 + 400*C**2 + 1500*C + 1875)
c3 = 4*(108*B**3*C + 540*B**3 + 75*B**2*C**2 + 870*B**2*C + 2475*B**2 - 28*B*C**3 + 290*B*C**2 + 2100*B*C + 3750*B + 5*C**4 + 60*C**3 + 400*C**2 + 1500*C + 1875)
S2 = sp.Poly(sp.expand(a2**2 - d2**2 * (C + 5) * (C + 4*B + 5)), B, C)
S3 = sp.Poly(sp.expand(b3**2 * (C + 5) - c3**2 * (C + 4*B + 5)), B, C)
for name, S in (('II: a^2 - d^2 P^2 Q^2', S2), ('III: b^2 P^2 - c^2 Q^2', S3)):
    neg = [(m, c) for m, c in zip(S.monoms(), S.coeffs()) if c < 0]
    print(name, ': degree', S.total_degree(), ', #terms', len(S.terms()), ', negative coefficients:', neg if neg else 'none')
    print('   factor:', sp.factor(S.as_expr()))
