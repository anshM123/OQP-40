"""Numerical evidence (mpmath, 40 digits): constants of the stationary limit f_inf of the min-apex certificate."""
import mpmath as mp
mp.mp.dps = 40
def kap(d): return 2*(mp.expm1(d) - d)/d**2 - mp.e**(d/3)
def f(d):
    if d == 0: return mp.mpf(1)
    return ((d - 1 + mp.e**(-d))/d**2 + mp.e**(d/3)/2)/(2*mp.sinh(d/2)/d + mp.sqrt(kap(d)/2))
print("slope at 0+: -f'(0+) =", mp.nstr(-mp.diff(f, mp.mpf('1e-12')), 12), " vs 1/(6 sqrt 2) =", mp.nstr(1/(6*mp.sqrt(2)), 12))
I = mp.quad(f, [0, 1, 5, 10, 20, 40, 80, 160, 320, mp.inf])
print("int_0^inf f_inf =", mp.nstr(I, 12), "  budget bound (1/(6 sqrt2))/int =", mp.nstr(1/(6*mp.sqrt(2))/I, 8))
g = lambda d: mp.diff(f, d, 2)/f(d)
d0 = mp.findroot(lambda x: mp.diff(g, x), mp.mpf('8.377'))
print("min f''/f =", mp.nstr(g(d0), 12), "at d* =", mp.nstr(d0, 12))
h = lambda d: -mp.diff(f, d)/f(d)
d1 = mp.findroot(lambda x: mp.diff(h, x), mp.mpf('5.3'))
print("min -f'/f =", mp.nstr(h(d1), 12), "at d =", mp.nstr(d1, 12))
print("f''/f at d->0+:", mp.nstr(g(mp.mpf('1e-6')), 10), "; as d->inf (d=200):", mp.nstr(g(mp.mpf(200)), 10), "(1/36 =", mp.nstr(mp.mpf(1)/36, 6), ")")
