"""NUMERICAL scan of inequality (C) in the far region max(a, c) > 4 (not covered by the certified compact core).
Ansh Mishra, Aryan Senthilkumar.
120-digit mpmath evaluation of F = theta log(1+X_P) + log(1-Y_G) (hyp.py formulas), sampling a, c log-uniformly up
to 30, theta in (0, 1/2] (including near 0 and 1/2), and w in the bulk and in thin layers 1 -+ w = 10^{-k}.
Reports the number of samples, the minimum of R = F/(theta (1-w^2) a^2 c^2) and of F, and any F < 0.
Usage: python scan_far.py seed n [amin amax [digits]]"""
import sys, random
import mpmath as mp
from hyp import F as F_mp

mp.mp.dps = int(sys.argv[5]) if len(sys.argv) > 5 else 120
random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
n = int(sys.argv[2]) if len(sys.argv) > 2 else 2000
LO = float(sys.argv[3]) if len(sys.argv) > 3 else 4.0
HI = float(sys.argv[4]) if len(sys.argv) > 4 else 30.0
neg = 0
minR = (mp.inf, None)
minF = (mp.inf, None)
for i in range(n):
    th = random.choice([random.uniform(1e-3, 0.5), 0.5, 0.5 - 10 ** random.uniform(-6, -1), 10 ** random.uniform(-4, -1)])
    import math
    big = math.exp(random.uniform(math.log(LO), math.log(HI)))
    small = random.choice([math.exp(random.uniform(math.log(1e-4), math.log(HI))), big * random.uniform(0.8, 1.2)])
    a, c = (big, small) if random.random() < 0.5 else (small, big)
    k = random.uniform(0, 1.2 * HI)
    w = random.choice([mp.mpf(random.uniform(-1, 1)), 1 - mp.mpf(10) ** (-k), -1 + mp.mpf(10) ** (-k)])
    w_print = float(w) if abs(abs(w) - 1) > 1e-15 else ("1-" if w > 0 else "-1+") + mp.nstr(1 - abs(w), 3)
    thm = mp.mpf(th)
    b = thm * c / (1 - thm)
    Fv = F_mp(thm, a, b, w)
    R = Fv / (thm * (1 - mp.mpf(w) ** 2) * mp.mpf(a) ** 2 * mp.mpf(c) ** 2)
    if Fv < 0:
        neg += 1
        print('NEGATIVE', th, a, c, w, mp.nstr(Fv, 10), flush=True)
    if R < minR[0]:
        minR = (R, (th, a, c, w_print))
    if Fv < minF[0]:
        minF = (Fv, (th, a, c, w_print))
print(f'samples {n}: F < 0 in {neg}; min R = {mp.nstr(minR[0], 8)} at {minR[1]}; min F = {mp.nstr(minF[0], 8)} at {minF[1]}')
