"""Co-ordered reduction: E(a,b,theta) = N0 J_{N0} + J_{-1} >= 0 for a, b > 1, theta in (0,1/2]  (P2 = (1,1), P1 = (a,b)).
Closed form (x = log a, y = r log b, r = (1-theta)/theta, p = a-1, q = b-1):
 E = theta[xy(e^{x+y}-1)/(x+y) - (e^x-1)(e^y-1)] + theta xy/(x+y) (1 - e^{-theta(x+y)})
     + pq/(p-q)^2 [(1-theta) p ((b/a)^theta - 1) + theta q ((a/b)^{1-theta} - 1)]."""
import numpy as np
import mpmath as mp
from t2_explicit import T2
mp.mp.dps = 40

def E(a, b, th):
    a, b, th = mp.mpf(a), mp.mpf(b), mp.mpf(th)
    r = (1 - th) / th
    x, y = mp.log(a), r * mp.log(b)
    p, q = a - 1, b - 1
    t1 = th * (x * y * mp.expm1(x + y) / (x + y) - mp.expm1(x) * mp.expm1(y))
    t2 = th * x * y / (x + y) * (-mp.expm1(-th * (x + y)))
    t3 = p * q / (p - q) ** 2 * ((1 - th) * p * ((b / a) ** th - 1) + th * q * ((a / b) ** (1 - th) - 1))
    return t1 + t2 + t3

# consistency with the quadrature: (N0+1) T2(1) = E
for (a, b, th) in [(2.0, 3.0, 0.5), (5.0, 1.5, 0.3), (1.3, 7.0, 0.2)]:
    N0 = 1 / th
    print(f"check a={a} b={b} th={th}: E = {float(E(a,b,th)):.10g}, (N0+1)T2(1) = {(N0+1)*T2(1.0, a, b, 1.0, 1.0, th):.10g}")
# scan, normalised by (log a)^2 (log b)^2 (the natural degeneracy scale)
worst = (mp.inf, None)
for th in ['0.5', '0.4', '0.3', '0.2', '0.1', '0.05', '0.02']:
    for la in np.exp(np.linspace(np.log(1e-3), np.log(8), 25)):
        for lb in np.exp(np.linspace(np.log(1e-3), np.log(8), 25)):
            a, b = mp.e ** la, mp.e ** lb
            if abs(a - b) < mp.mpf('1e-20'):
                continue
            v = E(a, b, mp.mpf(th))
            scale = (la * lb) ** 2 * max(1, float(a * b))
            if v / scale < worst[0]:
                worst = (v / scale, (th, la, lb, float(v)))
print("min of E/((log a log b)^2 max(1,ab)) over the grid:", float(worst[0]), "at (theta, log a, log b, E) =", worst[1])
