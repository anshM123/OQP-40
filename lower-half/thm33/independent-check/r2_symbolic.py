"""Referee check, task 2: independent symbolic derivation of conditions (I)-(III) of Section 8.3.

G(B,C) = 3 + (B+k)/C + 8 (C-B) h,  h = (P+Q)^(-2),  P = sqrt(C+k), Q = sqrt(C+4B+k),  k = 5.
(I)   = G + 2B G_B,   (II) = G - 2C G_C,   (III) = G + 2B G_B - 2C G_C - 4BC G_BC.

Route (different from the authors'): differentiate directly in B and C.
  (1) sympy's own diff of the radical expression (k = 5);
  (2) the referee's hand chain rule:  h_B = -4/(Q (P+Q)^3),  h_C = -h/(PQ),  h_BC = (2P+6Q)/(P Q^3 (P+Q)^3),
      G_B = 1/C + 8(-h + (C-B) h_B),  G_C = -(B+k)/C^2 + 8(h + (C-B) h_C),  G_BC = -1/C^2 + 8(-h_C + h_B + (C-B) h_BC);
  (3) clear denominators in (B, C, P, Q) and reduce modulo P^2 = C+k, Q^2 = C+4B+k;
  (4) only then compare with the authors' printed N_I, N_II, N_III (transcribed by hand from OQP40_RESULTS.md 8.3)
      under C = p^2-5, B = (q^2-p^2)/4, q = p+v, x = p^2;
  (5) re-check the authors' sign arguments exactly.
"""
import random
import sympy as sp
import mpmath as mp

out = []
def say(*a):
    s = ' '.join(str(x) for x in a)
    print(s, flush=True)
    out.append(s)

B, C, k = sp.symbols('B C k', positive=True)
P, Q = sp.symbols('P Q', positive=True)

# (1) sympy diff on the radical expression
G_rad = 3 + (B + 5) / C + 8 * (C - B) / (sp.sqrt(C + 5) + sp.sqrt(C + 4 * B + 5))**2
GB_r, GC_r, GBC_r = sp.diff(G_rad, B), sp.diff(G_rad, C), sp.diff(G_rad, B, C)
cond_rad = {
    'I': G_rad + 2 * B * GB_r,
    'II': G_rad - 2 * C * GC_r,
    'III': G_rad + 2 * B * GB_r - 2 * C * GC_r - 4 * B * C * GBC_r,
}

# (2) hand chain rule, in symbols P, Q (general k)
h = (P + Q)**-2
hB = -4 / (Q * (P + Q)**3)
hC = -h / (P * Q)
hBC = (2 * P + 6 * Q) / (P * Q**3 * (P + Q)**3)
G_m = 3 + (B + k) / C + 8 * (C - B) * h
GB_m = 1 / C + 8 * (-h + (C - B) * hB)
GC_m = -(B + k) / C**2 + 8 * (h + (C - B) * hC)
GBC_m = -1 / C**2 + 8 * (-hC + hB + (C - B) * hBC)
cond_man = {
    'I': G_m + 2 * B * GB_m,
    'II': G_m - 2 * C * GC_m,
    'III': G_m + 2 * B * GB_m - 2 * C * GC_m - 4 * B * C * GBC_m,
}

# check the hand chain rule itself: total derivatives of h with P(C), Q(B,C)
def dB(e): return sp.diff(e, B) + sp.diff(e, Q) * (2 / Q)
def dC(e): return sp.diff(e, C) + sp.diff(e, P) / (2 * P) + sp.diff(e, Q) / (2 * Q)
say('== chain rule for h ==')
say('  h_B ok:', sp.simplify(dB(h) - hB) == 0, '  h_C ok:', sp.simplify(dC(h) - hC) == 0,
    '  h_BC ok (both orders):', sp.simplify(dC(dB(h)) - hBC) == 0 and sp.simplify(dB(dC(h)) - hBC) == 0)
say('  G_B ok:', sp.simplify(dB(G_m) - GB_m) == 0, '  G_C ok:', sp.simplify(dC(G_m) - GC_m) == 0,
    '  G_BC ok:', sp.simplify(dC(dB(G_m)) - GBC_m) == 0)

# compare (1) and (2) at random high-precision points
mp.mp.dps = 60
random.seed(7)
maxdiff = 0
fr = {key: sp.lambdify((B, C), e, 'mpmath') for key, e in cond_rad.items()}
fm = {key: sp.lambdify((B, C, k, P, Q), e, 'mpmath') for key, e in cond_man.items()}
for _ in range(400):
    Cv = mp.mpf(10) ** random.uniform(-4, 5)
    Bv = Cv * mp.mpf(10) ** random.uniform(-6, 0.5)
    for key in fr:
        a = fr[key](Bv, Cv)
        b = fm[key](Bv, Cv, 5, mp.sqrt(Cv + 5), mp.sqrt(Cv + 4 * Bv + 5))
        maxdiff = max(maxdiff, abs(a - b) / abs(a))
say('== sympy diff vs hand chain rule (400 random points, 60 digits): max rel diff', mp.nstr(maxdiff, 3))

# (3) clear denominators and reduce mod P^2 = C+5, Q^2 = C+4B+5
def reduce_PQ(expr, kk=5):
    Pp = sp.Poly(sp.expand(expr), P, Q)
    res = 0
    for (i, j), c in Pp.terms():
        res += c * (C + kk)**(i // 2) * P**(i % 2) * (C + 4 * B + kk)**(j // 2) * Q**(j % 2)
    return sp.expand(res)

say('== cleared forms in (B, C, P, Q), k = 5 ==')
cleared = {}
for key, e in cond_man.items():
    e5 = sp.together(e.subs(k, 5))
    num, den = sp.fraction(e5)
    numr = reduce_PQ(num)
    cleared[key] = (numr, sp.factor(den))
    parts = sp.Poly(numr, P, Q)
    say(f'  ({key}) denominator: {sp.factor(den)} ; numerator = a + b P + c Q + d PQ with polynomial a..d of degrees',
        [sp.Poly(parts.coeff_monomial(m), B, C).total_degree() if parts.coeff_monomial(m) != 0 else None for m in (1, P, Q, P * Q)])

# (4) map to the authors' parametrisation and compare with the printed polynomials
p, q, v, x = sp.symbols('p q v x', positive=True)
sub = {C: p**2 - 5, B: (q**2 - p**2) / 4, P: p, Q: q, k: 5}
mine = {key: sp.factor(sp.together(e.subs(sub, simultaneous=True))) for key, e in cond_man.items()}
X = p**2
cx = X**3 - 8 * X**2 + 50 * X - 100
N_I_doc = 3 * v**5 + 21 * p * v**4 + 58 * p**2 * v**3 + 80 * p**3 * v**2 + 40 * (X**2 + 6 * X - 20) * v + 80 * p * ((X - 3)**2 + 1)
N_II_doc = (3 * p * v**5 + 21 * p**2 * v**4 + 2 * p * (29 * X + 20) * v**3 + 40 * (2 * X**2 + 7 * X - 10) * v**2
            + 40 * p * (X - 2) * (X + 20) * v + 80 * cx)
c2 = 40 * (7 * X**3 + 85 * X**2 - 290 * X + 400)
c0 = 80 * X * cx
c1 = -40 * p * (X**3 - 86 * X**2 + 320 * X - 400)
N_III_doc = (9 * p * v**7 + 81 * X * v**6 + p * (301 * X + 40) * v**5 + 35 * X * (17 * X + 8) * v**4
             + 2 * p**3 * (343 * X + 340) * v**3 + c2 * v**2 + c1 * v + c0)
den_doc = {'I': 4 * q * (p + q)**2 * (p**2 - 5), 'II': 4 * p * q * (p + q)**2 * (p**2 - 5),
           'III': 4 * p * q**3 * (p + q)**2 * (p**2 - 5)}
N_doc = {'I': N_I_doc, 'II': N_II_doc, 'III': N_III_doc}
say('== comparison with the printed N_I, N_II, N_III (q = p + v) ==')
for key in ('I', 'II', 'III'):
    doc_expr = N_doc[key].subs(v, q - p) / den_doc[key]
    ok = sp.cancel(mine[key] - doc_expr) == 0
    say(f'  ({key}) referee rational function == printed N/den : {ok}')
    if not ok:
        say('     referee:', mine[key])
# referee's own numerators in (p, v)
say('== referee numerators in (p, v), denominators as printed ==')
for key in ('I', 'II', 'III'):
    Nm = sp.factor(sp.cancel(mine[key] * den_doc[key]))
    Nm_v = sp.Poly(sp.expand(Nm.subs(q, p + v)), v)
    coeffs = {deg: sp.factor(c) for (deg,), c in zip(Nm_v.monoms(), Nm_v.coeffs())}
    say(f'  N_{key}:')
    for deg in sorted(coeffs, reverse=True):
        say(f'     v^{deg}: {coeffs[deg]}')

# (5) sign arguments
say('== sign arguments ==')
y = sp.symbols('y', positive=True)
def shift(expr_in_X):
    return sp.Poly(sp.expand(expr_in_X.subs(p, sp.sqrt(y + 5))), y)
for key in ('I', 'II', 'III'):
    Nm_v = sp.Poly(sp.expand(N_doc[key]), v)
    for (deg,), cf in zip(Nm_v.monoms(), Nm_v.coeffs()):
        # cf = p^e * poly(x); strip the p-power parity, then shift x = y + 5
        cf_f = sp.factor(cf)
        even = sp.expand(cf_f.subs(p, sp.sqrt(y + 5)))
        if even.has(sp.sqrt(y + 5)):
            even_core = sp.expand(sp.simplify(even / sp.sqrt(y + 5)))
            tag = 'p * '
        else:
            even_core = even; tag = ''
        poly_y = sp.Poly(even_core, y)
        allpos = all(c > 0 for c in poly_y.coeffs())
        say(f'  N_{key} v^{deg}: {tag}[{poly_y.as_expr()}] (y = x-5)  all coefficients > 0: {allpos}')
# c(x) and c_2 in y, the discriminant
cxs = sp.expand((x**3 - 8 * x**2 + 50 * x - 100).subs(x, y + 5))
say('  c(x) at x = 5+y:', cxs, '  == y^3+7y^2+45y+75:', sp.expand(cxs - (y**3 + 7 * y**2 + 45 * y + 75)) == 0)
c2s = sp.expand((7 * x**3 + 85 * x**2 - 290 * x + 400).subs(x, y + 5))
say('  c2/40 at x = 5+y:', c2s, '  == 7y^3+190y^2+1085y+1950:', sp.expand(c2s - (7 * y**3 + 190 * y**2 + 1085 * y + 1950)) == 0)
disc = sp.expand((4 * c0 * c2 - c1**2).subs(p, sp.sqrt(x)))
disc_red = sp.factor(disc)
say('  4 c0 c2 - c1^2 =', disc_red)
inner = sp.expand(sp.cancel(disc / (1600 * x)))
inner_y = sp.Poly(sp.expand(inner.subs(x, y + 5)), y)
say('  (4 c0 c2 - c1^2)/(1600 x) at x = 5+y:', inner_y.as_expr())
claimed = 55 * y**6 + 2054 * y**5 + 17729 * y**4 + 84580 * y**3 + 280425 * y**2 + 585750 * y + 489375
say('  == printed polynomial:', sp.expand(inner_y.as_expr() - claimed) == 0, '  all coefficients > 0:', all(c > 0 for c in inner_y.coeffs()))
roots = [sp.N(r_, 12) for r_ in sp.real_roots(sp.Poly(x**3 - 86 * x**2 + 320 * x - 400, x))]
say('  real roots of x^3-86x^2+320x-400 (c1 < 0 beyond the largest):', roots)
open('r2_symbolic.log', 'w').write('\n'.join(out) + '\n')
