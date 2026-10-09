"""Referee check: exact verification of the single-word counterexample of OQP40_RESULTS section 7
(the authors' perword33_example.py is NOT used; exact arithmetic with sympy Rationals).

Claims checked:
  (i)  A = diag(1, 10^5, 9*10^5), B = [[130001,1400,-100],[1400,50,28],[-100,28,26]] are positive definite;
       tr(A^2 B A B^2) = -2.85e22 < 0 < tr((AB)^3) = 1.90e22; Theorem-4 combination = +1.20e27.
  (ii) A = diag(89/10^6, 1, 9), same B: |tr(A^2BAB^2)| < tr((AB)^3) (ratio about -0.0013).
  (iii) the mechanism formula of section 7: with A = diag(0, y, z) (letters W_0 = u u^*, W_y, W_z),
        Re tr(A^2BAB^2) = <u, H u> + (terms free of W_0),  H = y^3 W_y^2 + z^3 W_z^2 + (yz(y+z)/2)(W_y W_z + W_z W_y).
"""
import sympy as sp

out = []
def say(*a):
    s = ' '.join(str(x) for x in a)
    print(s, flush=True)
    out.append(s)

def report(A, B, tag):
    t_word = (A**2 * B * A * B**2).trace()
    t_word_rev = (A**2 * B**2 * A * B).trace()
    t3 = ((A * B)**3).trace()
    t_a3b3 = (A**3 * B**3).trace()
    comb = t_a3b3 + t_word + t_word_rev - 3 * t3          # = tr A^3B^3 + 2 Re tr A^2BAB^2 - 3 tr (AB)^3 (real matrices)
    say(f'{tag}:')
    say(f'   A PD (leading minors): {[A[:k, :k].det() for k in (1, 2, 3)]}')
    say(f'   B PD (leading minors): {[B[:k, :k].det() for k in (1, 2, 3)]}  eigenvalues ~ {[sp.N(e, 8) for e in B.eigenvals()]}')
    say(f'   tr(A^2BAB^2) = {t_word}  (~{sp.N(t_word, 6)});  equals tr(A^2B^2AB): {t_word == t_word_rev}')
    say(f'   tr((AB)^3)   = {t3}  (~{sp.N(t3, 6)})')
    say(f'   tr(A^3B^3)   = {t_a3b3}  (~{sp.N(t_a3b3, 6)})')
    say(f'   Theorem 4 combination = {comb}  (~{sp.N(comb, 6)}) > 0: {comb > 0}')
    say(f'   single word < 0: {t_word < 0};  tr(A^2BAB^2)/tr((AB)^3) = {sp.N(t_word / t3, 8)};  |word| < tr((AB)^3): {abs(t_word) < t3}')
    return t_word, t3, comb

B = sp.Matrix([[130001, 1400, -100], [1400, 50, 28], [-100, 28, 26]])
A1 = sp.diag(1, 10**5, 9 * 10**5)
w1, t1, c1 = report(A1, B, 'integer example')
say('   matches printed values (-2.85e22, 1.90e22, +1.20e27):',
    abs(sp.N(w1) / sp.Float(-2.85e22) - 1) < 0.005, abs(sp.N(t1) / sp.Float(1.90e22) - 1) < 0.005, abs(sp.N(c1) / sp.Float(1.20e27) - 1) < 0.005)
A2 = sp.diag(sp.Rational(89, 10**6), 1, 9)
w2, t2, c2 = report(A2, B, 'rational example eps = 89/10^6')

# (iii) mechanism formula, symbolic in y, z and generic real symmetric B (3x3): A = diag(0, y, z)
y, z = sp.symbols('y z', positive=True)
b = sp.symbols('b11 b12 b13 b22 b23 b33', real=True)
Bs = sp.Matrix([[b[0], b[1], b[2]], [b[1], b[3], b[4]], [b[2], b[4], b[5]]])
As = sp.diag(0, y, z)
lhs = sp.expand((As**2 * Bs * As * Bs**2).trace())
# letters: W_l = B^{1/2} Q_l B^{1/2}. Use tr(W_i W_j W_k) = tr(B Q_i B Q_j B Q_k) so no square root is needed.
Qs = [sp.diag(1, 0, 0), sp.diag(0, 1, 0), sp.diag(0, 0, 1)]
al = [0, y, z]
def T(i, j, k): return (Bs * Qs[i] * Bs * Qs[j] * Bs * Qs[k]).trace()
# tr(A^2BAB^2) = tr(B A B^2 A^2) = tr(B A^1 B A^0 B A^2) = sum al_i al_k^2 T(i,j,k)
full = sp.expand(sum(al[i] * al[k]**2 * T(i, j, k) for i in range(3) for j in range(3) for k in range(3)))
say('(iii) cycle expansion tr(A^2BAB^2) = sum al_i al_k^2 T(i,j,k):', sp.expand(full - lhs) == 0)
# terms containing W_0 (index 0 in some slot): only j = 0 survives (al_0 = 0); <u,Hu> with u = B^{1/2} e_0:
# <u, W_k W_i u> = tr(W_i W_0 W_k) = T(i,0,k)
withW0 = sp.expand(sum(al[i] * al[k]**2 * T(i, 0, k) for i in (1, 2) for k in (1, 2)))
Hform = sp.expand(y**3 * T(1, 0, 1) + z**3 * T(2, 0, 2) + (y * z * (y + z) / 2) * (T(2, 0, 1) + T(1, 0, 2)))
say('     W_0-part equals <u, H u> with the printed H:', sp.expand(withW0 - Hform) == 0)
open('r6_perword.log', 'w').write('\n'.join(out) + '\n')
