"""NUMERICAL sanity check of the derivative bounds used in Lemma 3.7 (independent of the Arb code):
   -d eps_G/dw <= 2 |V'(C-)| sinh a sinh b   and   d eps_G/dw <= 4 theta^2 a c Ch'(theta^2 RE^2),
with eps_G from hyp.py (closed forms of Lemma 3.1), derivatives by central differences at 60 digits,
V'(C) = U_th'(C) cosh a + U_{1-th}'(C) cosh b, U_t(cosh d) = sinh(t d)/sinh d.
Ansh Mishra, Aryan Senthilkumar.  Usage: python check_lemma37.py seed n"""
import sys, random
import mpmath as mp
from hyp import parts
mp.mp.dps = 60
random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
n = int(sys.argv[2]) if len(sys.argv) > 2 else 300


def epsG(th, a, c, w):
    b = th * c / (1 - th)
    return parts(th, a, b, w)['epsG']


def Uprime(t, C):
    f = lambda x: mp.sinh(t * mp.acosh(x)) / mp.sinh(mp.acosh(x))
    if C - 1 < mp.mpf('1e-20'):
        return -t * (1 - t * t) / 3
    return mp.diff(f, C)


worst1 = mp.inf; worst2 = mp.inf; bad = 0
for i in range(n):
    th = mp.mpf(random.uniform(0.02, 0.5)); a = mp.mpf(random.uniform(0.05, 8)); c = mp.mpf(random.uniform(0.05, 8))
    w = mp.mpf(random.uniform(-0.999, 0.999))
    b = th * c / (1 - th)
    h = mp.mpf(10) ** -20
    d = (epsG(th, a, c, w + h) - epsG(th, a, c, w - h)) / (2 * h)
    Cm = mp.cosh(a - b)
    Vp = abs(Uprime(th, Cm)) * mp.cosh(a) + abs(Uprime(1 - th, Cm)) * mp.cosh(b)
    K1 = 2 * Vp * mp.sinh(a) * mp.sinh(b)
    RE2 = a * a + c * c + 2 * a * c * w
    x = th * th * RE2
    Chp = mp.sinh(mp.sqrt(x)) / (2 * mp.sqrt(x)) if x > 0 else mp.mpf(1) / 2
    K2 = 4 * th * th * a * c * Chp
    r1 = (K1 - (-d)) / max(K1, mp.mpf(1e-300)); r2 = (K2 - d) / max(K2, mp.mpf(1e-300))
    worst1 = min(worst1, r1); worst2 = min(worst2, r2)
    if -d > K1 * (1 + mp.mpf(10) ** -15) or d > K2 * (1 + mp.mpf(10) ** -15):
        bad += 1
        print('VIOLATION', th, a, c, w, mp.nstr(d, 10), mp.nstr(K1, 10), mp.nstr(K2, 10))
print(f'{n} points: violations {bad}; min relative slack: upper bound {mp.nstr(worst1, 5)}, lower bound {mp.nstr(worst2, 5)}')
