"""Independent check of the tail lemma (PROOF.md Section 6), written from its statements only.

Exact quantities (mpmath, 60 digits) from closed forms: U_t(cosh x) = sinh(t x)/sinh x and its C-derivatives
(differentiated numerically by mpmath in C), V = U_th cosh a + U_{1-th} cosh b, G = 2V(C), P = Tr(A B^r).
Checks at random points of the far region (theta in (0, 1/2], M = max(a, c) in [40, 300]):
  F2 (m = min(a, c) >= 1): E0 >= 1, (L+) and (L-) of Lemma 6.3;
  F1 (0 < m < 1): (T) of Lemma 6.4;
  both: the slope facts of Lemma 6.2(b) at random w (-d eps_G/dw <= K+, d eps_G/dw <= 2 th^2 a c shc(th R_E)),
        and F >= 0 itself at random w, including layers 1 -/+ w = 10^-k.
usage: python tail_independent.py seed n"""
import sys
import random
import mpmath as mp

mp.mp.dps = 150
seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
n = int(sys.argv[2]) if len(sys.argv) > 2 else 100
rng = random.Random(seed)


def U(t, C):
    if C == 1:
        return mp.mpf(t)
    x = mp.acosh(C)
    return mp.sinh(t * x) / mp.sinh(x)


def shc(x):
    return mp.sinh(x) / x if x != 0 else mp.mpf(1)


def psi(R):
    return R / (1 - mp.exp(-R)) if R != 0 else mp.mpf(1)


def quantities(th, a, c, w):
    b = th * c / (1 - th)
    RE = mp.sqrt(a * a + c * c + 2 * a * c * w)
    P = 2 * (mp.cosh(a) * mp.cosh(c) + w * mp.sinh(a) * mp.sinh(c))
    C = mp.cosh(a) * mp.cosh(b) - w * mp.sinh(a) * mp.sinh(b)
    G = 2 * (U(th, C) * mp.cosh(a) + U(1 - th, C) * mp.cosh(b))
    epsP = P - 2 * mp.cosh(RE)
    epsG = 2 * mp.cosh(th * RE) - G
    return b, RE, epsP, epsG


def F(th, a, c, w):
    b, RE, epsP, epsG = quantities(th, a, c, w)
    return th * mp.log(1 + mp.exp(RE) * epsP) + mp.log(1 - mp.exp(-th * RE) * epsG)


def Uder(t, delta, k):
    """k-th derivative in C of U_t(C) at C = cosh(delta), from closed forms in delta (delta > 0):
    U' = N/sinh^3, N = t cosh(t x) sinh x - sinh(t x) cosh x;  U'' = [(t^2-1) sinh(t x) sinh^2 x - 3 N cosh x]/sinh^5."""
    x = max(delta, mp.mpf(10) ** -30)     # U is even and analytic in x; the error of this floor is O(1e-60)
    N = t * mp.cosh(t * x) * mp.sinh(x) - mp.sinh(t * x) * mp.cosh(x)
    if k == 1:
        return N / mp.sinh(x) ** 3
    return ((t * t - 1) * mp.sinh(t * x) * mp.sinh(x) ** 2 - 3 * N * mp.cosh(x)) / mp.sinh(x) ** 5


def Vder(th, a, b, delta, k):
    return Uder(th, delta, k) * mp.cosh(a) + Uder(1 - th, delta, k) * mp.cosh(b)


bad = []
worst = {'L+': 0, 'L-': mp.inf, 'T': 0, 'slope+': 0, 'slope-': 0}
minF = mp.inf
for i in range(n):
    th = mp.mpf(rng.choice([0.5, 0.25, 1e-3, rng.uniform(1e-4, 0.5)]))
    M = mp.mpf(rng.uniform(40, 300))
    region = 'F2' if rng.random() < 0.6 else 'F1'
    m = mp.mpf(rng.uniform(1, float(M))) if region == 'F2' else mp.mpf(10) ** rng.uniform(-6, -0.0001)
    a, c = (m, M) if rng.random() < 0.5 else (M, m)
    b = th * c / (1 - th)
    d = abs(a - b)
    K = 2 * abs(Vder(th, a, b, d, 1)) * mp.sinh(a) * mp.sinh(b)
    if region == 'F2':
        E0 = quantities(th, a, c, mp.mpf(0))[2]
        w1, w2 = 1 - 1 / E0, -1 + 1 / E0
        R1 = mp.sqrt(a * a + c * c + 2 * a * c * w1)
        R2 = mp.sqrt(a * a + c * c + 2 * a * c * w2)
        Pp = 2 * a * c * (shc(R1) - shc(a) * shc(c))
        lhs = mp.exp(-th * R1) * K
        rhs = mp.mpf(1) / 2 * min(1, th * psi(R1)) * Pp
        ok_plus = Pp > 0 and lhs <= rhs
        Lm = shc(a) * shc(c) - shc(R2)
        ok_minus = Lm >= 2 * th
        worst['L+'] = max(worst['L+'], lhs / rhs)
        worst['L-'] = min(worst['L-'], Lm / (2 * th))
        if not (E0 >= 1 and ok_plus and ok_minus):
            bad.append(('F2', th, a, c, E0 >= 1, ok_plus, ok_minus))
    else:
        t = abs(a - c)
        MP = (t * mp.cosh(t) - mp.sinh(t)) / t ** 3
        MG = (mp.sinh(a) / a) ** 2 * (mp.sinh(b) / b) ** 2 * Vder(th, a, b, d, 2)
        lhs = mp.exp(-th * t) * (th / (1 - th)) ** 2 * MG
        rhs = mp.mpf(1) / 2 * min(1, th * psi(t)) * MP
        worst['T'] = max(worst['T'], lhs / rhs)
        if not lhs <= rhs:
            bad.append(('F1', th, a, c))
    # slope facts and F itself at random w and in the layers
    ws = [mp.mpf(rng.uniform(-1, 1)) for _ in range(3)]
    ws += [1 - mp.mpf(10) ** (-rng.randint(1, 40)), -1 + mp.mpf(10) ** (-rng.randint(1, 40))]
    for w in ws:
        RE = quantities(th, a, c, w)[1]
        Cw = mp.cosh(a) * mp.cosh(b) - w * mp.sinh(a) * mp.sinh(b)
        dG = 2 * th ** 2 * a * c * shc(th * RE) - 2 * abs(Vder(th, a, b, mp.acosh(Cw), 1)) * mp.sinh(a) * mp.sinh(b)
        up = 2 * th ** 2 * a * c * shc(th * RE)
        worst['slope+'] = max(worst['slope+'], -dG / K)
        worst['slope-'] = max(worst['slope-'], dG / up)
        if -dG > K * (1 + mp.mpf(10) ** -30) or dG > up * (1 + mp.mpf(10) ** -30):
            bad.append(('slope', th, a, c, w))
        f = F(th, a, c, w)
        minF = min(minF, f)
        if f < 0:
            bad.append(('F<0', th, a, c, w, f))
print(f'{n} far-region points (seed {seed}); violations: {len(bad)}')
for x in bad[:10]:
    print('  VIOLATION', [mp.nstr(y, 8) if isinstance(y, mp.mpf) else y for y in x])
print('max (L+) ratio lhs/rhs:', mp.nstr(worst['L+'], 6), '| min (L-) ratio /(2 theta):', mp.nstr(worst['L-'], 6),
      '| max (T) ratio:', mp.nstr(worst['T'], 6))
print('max -d eps_G/dw / K+:', mp.nstr(worst['slope+'], 6), '| max d eps_G/dw / (2 th^2 ac shc):', mp.nstr(worst['slope-'], 6))
print('min F over the sampled w:', mp.nstr(minF, 6))

# the exact derivative formula of eps_G in w (used above) against a numerical derivative, at moderate sizes
dev = 0
for i in range(20):
    th = mp.mpf(rng.uniform(0.01, 0.5)); a = mp.mpf(rng.uniform(0.1, 8)); c = mp.mpf(rng.uniform(0.1, 8))
    w = mp.mpf(rng.uniform(-0.95, 0.95)); b = th * c / (1 - th)
    num = mp.diff(lambda x: quantities(th, a, c, x)[3], w)
    RE = quantities(th, a, c, w)[1]
    Cw = mp.cosh(a) * mp.cosh(b) - w * mp.sinh(a) * mp.sinh(b)
    ex = 2 * th ** 2 * a * c * shc(th * RE) - 2 * abs(Vder(th, a, b, mp.acosh(Cw), 1)) * mp.sinh(a) * mp.sinh(b)
    dev = max(dev, abs(num - ex) / (abs(ex) + abs(num)))
print('derivative formula of eps_G vs numerical derivative, 20 points: max rel. deviation', mp.nstr(dev, 3))

