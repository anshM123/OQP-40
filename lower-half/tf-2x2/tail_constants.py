"""RIGOROUS (Arb) verification of every numerical constant used in the tail lemma (PROOF.md Section 6).
Ansh Mishra, Aryan Senthilkumar.

Each line is one claim of Section 6, tagged
  [Arb]       inequality between explicit numbers, decided with ball arithmetic (python-flint, 200 bits); claims about
              a function of theta on [0, 1/2] are decided on 4096 subintervals (interval enclosure of the whole
              expression; used only where the expression has no cancellation);
  [exact]     identity or inequality between rationals, decided with fractions.Fraction;
  [analytic]  elementary fact whose one-line proof is printed (no computation).
Prints 'ALL CONSTANTS VERIFIED' if every computed claim holds.
"""
from fractions import Fraction as Q
from flint import arb, ctx

ctx.prec = 200
ok_all = True


def claim(kind, name, cond):
    global ok_all
    print(('OK   ' if cond else 'FAIL ') + f'[{kind}] ' + name)
    ok_all = ok_all and bool(cond)


def over_theta(f, bound, lo=0.0, hi=0.5, n=4096):
    """sup over theta in [lo, hi] of f(theta) <= bound, by interval enclosures on n subintervals."""
    for k in range(n):
        T = arb(lo + (hi - lo) * k / n).union(arb(lo + (hi - lo) * (k + 1) / n))
        if not (f(T).upper() <= bound):
            return False
    return True


E3 = arb(3).exp()
shc = lambda x: arb(x).sinh() / arb(x)
cosh1 = arb(1).cosh()
t39 = arb(39)

# ---- Lemma 6.2(d)
claim('Arb', '4/(4-th^2) <= 1.07 on [0,1/2]', over_theta(lambda t: 4 / (4 - t * t), 1.07))
claim('Arb', '2[1/(1-th)+1/(1+th)+1/(3-th)] <= 6.8 on [0,1/2]',
      over_theta(lambda t: 2 * (1 / (1 - t) + 1 / (1 + t) + 1 / (3 - t)), 6.8))
claim('Arb', '48/(9-th^2) <= 5.49 on [0,1/2]', over_theta(lambda t: 48 / (9 - t * t), 5.49))
claim('Arb', '8/(4-th)+8/(1-th)+8/(2+th) <= 22.3 on [0,1/2]',
      over_theta(lambda t: 8 / (4 - t) + 8 / (1 - t) + 8 / (2 + t), 22.3))
claim('analytic', '2 sinh(x)/th <= e^x min(1/th, 2d) for x = th d: sinh x <= e^x/2 and sinh x <= x cosh x <= x e^x', True)
claim('analytic', 's_th = sin(pi th)/pi <= th: sin y <= y for y >= 0', True)
claim('analytic', 'th/(1-th) <= 2 th on (0,1/2]: 1/(1-th) <= 2 iff th <= 1/2', True)

# ---- Region F2
h0 = arb(40) / 41
eta0 = arb(1) / 2 - (-h0).exp()
claim('exact', 'h = mM/(m+M) >= 40/41 at m = 1, M = 40 (h increasing in m and M)', Q(1 * 40, 41) >= Q(40, 41))
claim('Arb', 'eta0 = 1/2 - e^{-40/41} >= 0.123', eta0.lower() >= arb('0.123'))
claim('Arb', 'eta0 e^{41} >= 1  (E0 >= eta0 e^{a+c} >= 1 for a + c >= 41)', (eta0 * arb(41).exp()).lower() >= 1)
claim('analytic', 'x e^{-x} decreasing for x >= 1 and x^2 e^{-x} decreasing for x >= 2 (used at x = a + c >= 41)', True)
claim('Arb', '41 e^{-41}/(2 eta0) <= 2.8e-16  (delta <= 2h/E0 <= (a+c)e^{-(a+c)}/(2 eta0))',
      (41 * arb(-41).exp() / (2 * eta0)).upper() <= arb('2.8e-16'))
claim('Arb', '41^2 e^{-41}/(2 eta0) <= 1  (2ac/E0 <= 1, hence R2 <= |a-c| + 1)',
      (41 ** 2 * arb(-41).exp() / (2 * eta0)).upper() <= 1)
claim('Arb', 'e^{-2.8e-16}(1 - e^{-80}) >= 1 - 3e-16',
      ((arb('-2.8e-16')).exp() * (1 - arb(-80).exp())).lower() >= 1 - arb('3e-16'))
claim('exact', '1.07 + 3.4 = 4.47 (Step 3 constant)', Q('1.07') + Q('3.4') == Q('4.47'))
claim('analytic', '(4.47 + 2D) e^{-D} decreasing on D >= 0: derivative (2 - 4.47 - 2D) e^{-D} < 0', True)
claim('Arb', 'e^{th delta} <= 1 + 1e-15 (th <= 1/2, delta <= 2.8e-16)', (arb('1.4e-16')).exp().upper() <= 1 + arb('1e-15'))
claim('Arb', '4.47 (1 + 1e-15) <= 4.48', (arb('4.47') * (1 + arb('1e-15'))).upper() <= arb('4.48'))
claim('Arb', '1/2 (41 - 2.8e-16)((1 - 3e-16)(40/41) - 1/2) >= 9.7',
      (arb(1) / 2 * (41 - arb('2.8e-16')) * ((1 - arb('3e-16')) * h0 - arb(1) / 2)).lower() >= arb('9.7'))
claim('exact', 'h >= 20*40/60 = 40/3 for m >= 20, M >= 40', Q(20 * 40, 60) == Q(40, 3))
claim('Arb', '(1 - 3e-16)(40/3) - 1/2 >= 4.48', ((1 - arb('3e-16')) * arb(40) / 3 - arb(1) / 2).lower() >= arb('4.48'))
claim('Arb', '(4.47 + 40) e^{-20}(1 + 1e-15) <= 1e-7  (m < 20: Delta > 20)',
      ((arb('4.47') + 40) * arb(-20).exp() * (1 + arb('1e-15'))).upper() <= arb('1e-7'))
claim('Arb', '(1 - 3e-16)(40/41) - 1/2 >= 0.47', ((1 - arb('3e-16')) * h0 - arb(1) / 2).lower() >= arb('0.47'))
claim('Arb', 'shc(4)(shc(1)(1 - e^{-80}) - 1) >= 1.19  (case M - m >= 3)',
      (shc(4) * (shc(1) * (1 - arb(-80).exp()) - 1)).lower() >= arb('1.19'))
claim('Arb', 'shc(37)(1 - e^{-80}) - 1 >= 1  (case M - m < 3)', (shc(37) * (1 - arb(-80).exp()) - 1).lower() >= 1)

# ---- Region F1
claim('Arb', 'shc(1)^2 <= 1.3811', (shc(1) ** 2).upper() <= arb('1.3811'))
claim('exact', '4 * 1.3811 <= 5.525', 4 * Q('1.3811') <= Q('5.525'))
claim('exact', '5.49 + 22.3 = 27.79', Q('5.49') + Q('22.3') == Q('27.79'))
claim('exact', '22.3/4 = 5.575', Q('22.3') / 4 == Q('5.575'))
claim('analytic', 'case a = M: e^{-th t} e^{3a - (3-th) d} <= e^{th c + 3 - th} <= e^3 and e^{-th t} e^{2a - (2+th) d} <= e^{2+th} '
      '(d >= a - 1, t = a - c, c < 1)', True)
c776 = arb('5.525') * E3 / 4 * (arb('0.5') * (arb('5.49') + arb('22.3') * cosh1) + 8)
claim('Arb', '(5.525 e^3/4)[(1/2)(5.49 + 22.3 cosh 1) + 8] <= 776  (bracket increasing in theta)', c776.upper() <= 776)
c258 = arb('1.3811') * arb('5.525') * cosh1 * (arb('27.79') * arb('0.5') + 8)
claim('Arb', '1.3811 * 5.525 * cosh(1) * (27.79/2 + 8) <= 258  (theta^2 (27.79 theta + 8), theta <= 1/2)', c258.upper() <= 258)
c193 = arb('1.3811') * (cosh1 * E3 / 4 * (arb('5.49') * arb('0.5') + 8) + arb('5.575') * arb('0.5') * E3)
claim('Arb', '1.3811 [cosh(1)(e^3/4)(5.49/2 + 8) + 5.575 (1/2) e^3] <= 193  (increasing in theta)', c193.upper() <= 193)
claim('Arb', '... and the same quantity is > 192.3 (so 193, not 192.3, is the constant)', c193.lower() > arb('192.3'))
claim('exact', '(c - 1)/(c + 1) >= 39/41 >= 0.951 for c >= 40', Q(39, 41) >= Q('0.951'))
claim('analytic', '(t-1)e^t/(4t) increasing for t >= 1; (t-1)e^t/(4t^2), (t-1)e^t/(4t^3) increasing for t >= 3 '
      '(log-derivatives 1/(t-1) + 1 - k/t > 0)', True)
claim('Arb', '776 <= (t-1)e^t/(4t) at t = 39 (hence also <= (t-1)e^t/4)', ((t39 - 1) * t39.exp() / (4 * t39)).lower() >= 776)
claim('Arb', '258 <= (t-1)e^t/(4t^3) at t = 39 (hence also <= (t-1)e^t/(4t^2))',
      ((t39 - 1) * t39.exp() / (4 * t39 ** 3)).lower() >= 258)
claim('Arb', '193 <= 0.951 (t-1) e^t/(4t) at t = 39', (arb('0.951') * (t39 - 1) * t39.exp() / (4 * t39)).lower() >= 193)
print('ALL CONSTANTS VERIFIED' if ok_all else 'SOME CONSTANT FAILED')
