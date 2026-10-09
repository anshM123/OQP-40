"""Referee: explicit cleared closed forms of (I)-(III) in (B, C, P, Q), P = sqrt(C+5), Q = sqrt(C+4B+5)
(for display in the paper, fix M2). Derived from the referee's hand chain rule (validated in r2_symbolic.py)."""
import sympy as sp
B, C, P, Q = sp.symbols('B C P Q', positive=True)
k = 5
h = (P + Q)**-2; hB = -4 / (Q * (P + Q)**3); hC = -h / (P * Q); hBC = (2 * P + 6 * Q) / (P * Q**3 * (P + Q)**3)
G = 3 + (B + k) / C + 8 * (C - B) * h
GB = 1 / C + 8 * (-h + (C - B) * hB); GC = -(B + k) / C**2 + 8 * (h + (C - B) * hC)
GBC = -1 / C**2 + 8 * (-hC + hB + (C - B) * hBC)
conds = {'I': G + 2 * B * GB, 'II': G - 2 * C * GC, 'III': G + 2 * B * GB - 2 * C * GC - 4 * B * C * GBC}
def reduce_PQ(expr):
    Pp = sp.Poly(sp.expand(expr), P, Q); res = 0
    for (i, j), c in Pp.terms():
        res += c * (C + 5)**(i // 2) * P**(i % 2) * (C + 4 * B + 5)**(j // 2) * Q**(j % 2)
    return sp.expand(res)
lines = []
for key, e in conds.items():
    num, den = sp.fraction(sp.together(e))
    numr = sp.Poly(reduce_PQ(num), P, Q)
    parts = {str(m): sp.factor(numr.coeff_monomial(m)) for m in (1, P, Q, P * Q) if numr.coeff_monomial(m) != 0}
    lines.append(f'({key}) = [ ' + ' + '.join(f'({v})' + ('' if m == '1' else f'*{m}') for m, v in parts.items()) + f' ] / ( {sp.factor(den)} )')
    # numeric spot check against direct evaluation
    import random
    random.seed(1)
    for _ in range(5):
        Bv, Cv = random.uniform(0.01, 5), random.uniform(0.01, 5)
        sub = {B: Bv, C: Cv, P: (Cv + 5) ** 0.5, Q: (Cv + 4 * Bv + 5) ** 0.5}
        a = float(e.subs(sub)); b = float((numr.as_expr() / den).subs(sub))
        assert abs(a - b) < 1e-9 * abs(a), (key, a, b)
for l in lines:
    print(l)
open('r2b_closed_forms.log', 'w').write('\n'.join(lines) + '\n')
