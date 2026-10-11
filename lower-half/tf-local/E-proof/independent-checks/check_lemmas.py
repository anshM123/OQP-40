"""Independent checks (mpmath, 60 digits) of the analytic lemmas in E_proof/PROOF.md, written from the statements only."""
import mpmath as mp, random
mp.mp.dps = 60
phi = lambda z: mp.expm1(z) / z if z != 0 else mp.mpf(1)
def ee(a, b, c):  # second divided difference of exp
    a, b, c = mp.mpf(a), mp.mpf(b), mp.mpf(c)
    return mp.quad(lambda t1: mp.quad(lambda t2: mp.exp((1 - t1 - t2) * a + t1 * b + t2 * c), [0, 1 - t1]), [0, 1])

def E_closed(th, X, Y):
    r = (1 - th) / th; x, y = X, r * Y; s = x + y
    p, q = mp.expm1(X), mp.expm1(Y)
    EGT = th * (x * y * mp.expm1(s) / s - mp.expm1(x) * mp.expm1(y))
    Em1 = th * x * y * (-mp.expm1(-th * s)) / s + p * q / (p - q) ** 2 * ((1 - th) * p * mp.expm1(th * (Y - X)) + th * q * mp.expm1((1 - th) * (X - Y)))
    return EGT + Em1

def E_integral(th, X, Y):
    N0 = 1 / th
    p, q = mp.expm1(X), mp.expm1(Y)
    al, be = th * X, (1 - th) * Y; De = al + be
    Qa = lambda u: 1 + u * p; Qb = lambda u: 1 + u * q
    l = lambda u: th * mp.log(Qa(u)) + (1 - th) * mp.log(Qb(u))
    Ap = lambda u: th * p / Qa(u); Bp = lambda u: (1 - th) * q / Qb(u)
    K = lambda u: (al * be / De) * (Ap(u) + Bp(u)) - Ap(u) * Bp(u)
    return mp.quad(lambda u: (N0 * mp.exp(N0 * l(u)) + mp.exp(-l(u))) * K(u), [0, 1])

rng = random.Random(11)
worst = {k: 0 for k in ['closed_vs_int', 'L21a', 'L21b', 'L21c', 'L22', 'L24']}
for _ in range(25):
    th = mp.mpf(rng.uniform(0.02, 0.5)); r = (1 - th) / th
    X = mp.mpf(rng.uniform(-3, 3)); Y = mp.mpf(rng.uniform(-3, 3))
    if th * X + (1 - th) * Y <= 0.05: continue
    x, y = X, r * Y; s = x + y; D = X - Y
    p, q = mp.expm1(X), mp.expm1(Y)
    Ec, Ei = E_closed(th, X, Y), E_integral(th, X, Y)
    worst['closed_vs_int'] = max(worst['closed_vs_int'], abs(Ec - Ei) / abs(Ei))
    V = lambda u: (1 + u * p) ** (-1 - th) * (1 + u * q) ** (-2 + th)
    J = mp.quad(V, [0, 1]); J1 = mp.quad(lambda u: u * V(u), [0, 1])
    lhs = p * q / (p - q) ** 2 * ((1 - th) * p * mp.expm1(-th * D) + th * q * mp.expm1((1 - th) * D))
    worst['L21a'] = max(worst['L21a'], abs(lhs + th * (1 - th) * p * q * J) / abs(lhs))
    Jb = (mp.exp(Y) * ee(0, (1 - th) * D, D) + ee(0, -th * D, (1 - th) * D)) / (mp.exp(2 * Y) * phi(D) ** 2)
    worst['L21b'] = max(worst['L21b'], abs(Jb - J) / J)
    J1b = ee(0, -th * D, (1 - th) * D) / (mp.exp(2 * Y) * phi(D) ** 2)
    worst['L21c'] = max(worst['L21c'], abs(J1b - J1) / J1)
    CGT = phi(s) - phi(x) * phi(y); Cm1 = phi(-th * s) - phi(x) * phi(Y) * J
    worst['L22'] = max(worst['L22'], abs(th * x * y * (CGT + th * Cm1) - Ec) / abs(Ec))
    psi = lambda z: 1 / z - 1 / mp.expm1(z)
    ustar = th * psi(Y) + (1 - th) * psi(x)
    kap = th / (1 - th)
    tm1 = -th * Cm1 / (x * y)
    tm2 = kap * phi(x) * phi(Y) * (ustar * J - J1) / s
    worst['L24'] = max(worst['L24'], abs(tm1 - tm2) / abs(tm1))
print({k: mp.nstr(v, 3) for k, v in worst.items()})

# Theorem 3.1: boundary s = 0, H(theta,x,-x) = [phi(x)phi(-x) - 1 - theta(1 - R^2)]/x^2, compare with E/(theta x^4) by limit
def H_boundary_formula(th, x):
    kap = th / (1 - th)
    R = phi(x) * phi(kap * x) / phi((1 + kap) * x)
    return (phi(x) * phi(-x) - 1 - th * (1 - R ** 2)) / x ** 2
worst31 = 0
for _ in range(15):
    th = mp.mpf(rng.uniform(0.03, 0.5)); x = mp.mpf(rng.uniform(-4, 4)); r = (1 - th) / th
    eps = mp.mpf('1e-25')
    # point with s = eps: y = -x + eps, Y = y / r
    X, Y = x, (-x + eps) / r
    Hn = E_closed(th, X, Y) / (th * x ** 2 * (-x + eps) ** 2)
    worst31 = max(worst31, abs(Hn - H_boundary_formula(th, x)) / abs(H_boundary_formula(th, x)))
    t = x / 2
    half = (2 * mp.sinh(t) ** 2 + mp.tanh(t) ** 2 - 3 * t ** 2) / (8 * t ** 4)
    assert H_boundary_formula(mp.mpf(1) / 2, x) - half < mp.mpf('1e-40') * abs(half) + mp.mpf('1e-50')
    assert H_boundary_formula(th, x) >= half * (1 - mp.mpf('1e-40'))
print('Thm 3.1 formula vs limit of closed form: max rel diff', mp.nstr(worst31, 3), '; monotonicity in theta and theta=1/2 formula: OK')
# corner value H(theta,0,0) = (1+theta)(1-2theta)/(12(1-theta))
for th in [mp.mpf('0.1'), mp.mpf('0.3'), mp.mpf('0.5')]:
    r = (1 - th) / th; h = mp.mpf('1e-12')
    Hc = E_closed(th, h, 2 * h / r) / (th * h ** 2 * (2 * h) ** 2)
    print('H(theta,0,0) at theta', th, ':', mp.nstr(Hc, 10), 'formula', mp.nstr((1 + th) * (1 - 2 * th) / (12 * (1 - th)), 10))
