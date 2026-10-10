"""Exact identities that factor out the (s-1)^2 of the min-apex kernel near s = 1 (checked here numerically with
50 digits for n = 6, 7, 9; they are polynomial identities, proof in RESULTS.md 8.4):
  phi = K_n(1,s,t), psi = K_n(t,s,s), k = K_n(t,1,1), h_m = complete homogeneous symmetric polynomial, C = C(n+2,2):
  phi - k = (s-1) h_{n-1}(1,1,s,t)/C - t^{n/3}(s^{n/3} - 1),
  2 phi - psi - k = -(s-1)^2 h_{n-2}(1,1,s,s,t)/C + t^{n/3}(s^{n/3} - 1)^2,
  phi^2 - k psi = (phi - k)^2 + k (2 phi - psi - k),   E_old = phi - sqrt(k psi) = (phi^2 - k psi)/(phi + sqrt(k psi)).
Usage: python tb_identity_strip.py > tb_identity_strip.log"""
import mpmath as mp
mp.mp.dps = 50


def h(m, xs):
    if m < 0:
        return mp.mpf(0)
    if len(xs) == 1:
        return xs[0] ** m
    return sum(xs[-1] ** j * h(m - j, xs[:-1]) for j in range(m + 1))


worst = 0
for n in (6, 7, 9):
    C = mp.binomial(n + 2, 2)
    for (s, t) in ((mp.mpf('1.3'), mp.mpf('2.1')), (mp.mpf('1.01'), mp.mpf('5')), (mp.mpf('2'), mp.mpf('2.5')), (mp.mpf('1.0001'), mp.mpf('1.5'))):
        K = lambda x, y, z: h(n, [x, y, z]) / C - (x * y * z) ** (mp.mpf(n) / 3)
        phi, psi, k = K(1, s, t), K(t, s, s), K(t, 1, 1)
        r1 = (phi - k) - ((s - 1) * h(n - 1, [1, 1, s, t]) / C - t ** (mp.mpf(n) / 3) * (s ** (mp.mpf(n) / 3) - 1))
        r2 = (2 * phi - psi - k) - (-(s - 1) ** 2 * h(n - 2, [1, 1, s, s, t]) / C + t ** (mp.mpf(n) / 3) * (s ** (mp.mpf(n) / 3) - 1) ** 2)
        r3 = (phi ** 2 - k * psi) - ((phi - k) ** 2 + k * (2 * phi - psi - k))
        scale = abs(phi) + abs(psi) + abs(k)
        worst = max(worst, abs(r1) / scale, abs(r2) / scale, abs(r3) / scale ** 2)
        print(n, mp.nstr(s, 6), mp.nstr(t, 4), mp.nstr(r1, 3), mp.nstr(r2, 3), mp.nstr(r3, 3))
print(f"max relative residual {mp.nstr(worst, 3)}")
