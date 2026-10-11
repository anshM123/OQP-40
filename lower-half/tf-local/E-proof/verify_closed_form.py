"""Step 0: compare the closed form E = E_GT + E_m1 with the integral definition
   E = int_0^1 [N0 e^{N0 l(u)} + e^{-l(u)}] K(u) du
at random points (theta, X, Y), Delta = theta X + (1-theta) Y > 0, in high precision (mpmath, 50 digits)."""
import random
import mpmath as mp

mp.mp.dps = 50


def E_closed(th, X, Y):
    th, X, Y = mp.mpf(th), mp.mpf(X), mp.mpf(Y)
    r = (1 - th) / th
    x, y = X, r * Y
    p, q = mp.expm1(X), mp.expm1(Y)
    s = x + y
    EGT = th * (x * y * mp.expm1(s) / s - mp.expm1(x) * mp.expm1(y))
    Em1 = th * x * y * (-mp.expm1(-th * s)) / s + p * q / (p - q) ** 2 * (
        (1 - th) * p * mp.expm1(th * (Y - X)) + th * q * mp.expm1((1 - th) * (X - Y)))
    return EGT + Em1


def E_integral(th, X, Y):
    th, X, Y = mp.mpf(th), mp.mpf(X), mp.mpf(Y)
    p, q = mp.expm1(X), mp.expm1(Y)
    N0 = 1 / th
    al, be = th * X, (1 - th) * Y
    De = al + be

    def f(u):
        Qa, Qb = 1 + u * p, 1 + u * q
        l = th * mp.log(Qa) + (1 - th) * mp.log(Qb)
        Ap, Bp = th * p / Qa, (1 - th) * q / Qb
        K = (al * be / De) * (Ap + Bp) - Ap * Bp
        return (N0 * mp.e ** (N0 * l) + mp.e ** (-l)) * K
    return mp.quad(f, [0, mp.mpf(1) / 4, mp.mpf(1) / 2, mp.mpf(3) / 4, 1])


if __name__ == '__main__':
    rng = random.Random(20261010)
    worst = 0
    n = 0
    while n < 60:
        th = rng.choice([rng.uniform(0.01, 0.5), 0.5, rng.uniform(0.3, 0.5)])
        X = rng.uniform(-5, 5)
        Y = rng.uniform(-5, 5)
        if th * X + (1 - th) * Y <= 0:
            continue
        n += 1
        c = E_closed(th, X, Y)
        i = E_integral(th, X, Y)
        rel = abs(c - i) / max(abs(c), mp.mpf('1e-40'))
        worst = max(worst, rel)
        if n <= 12:
            print(f"theta={th:.4f} X={X:+.4f} Y={Y:+.4f}: closed={mp.nstr(c, 20)}  integral={mp.nstr(i, 20)}  rel.diff={mp.nstr(rel, 3)}")
    print(f"{n} random points: max relative difference = {mp.nstr(worst, 3)}")
