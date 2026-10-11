"""NUMERICAL: random and adversarial test of inequality (C):  Dc = P - e^{N0 zeta_2} - c^{-N0} >= 0,
c = G - e^{-zeta_2}; also records whether u_c < v_min (the case where (C) is needed).
Normalised ratio R = Dc / (al^2 be^2 sin^2 ga) is reported.
Ansh Mishra, Aryan Senthilkumar."""
import sys
import numpy as np
import mpmath as mp
mp.mp.dps = 60
from cf2x2 import quantities, Dc, vmin_vmax

rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 0)
n = int(sys.argv[2]) if len(sys.argv) > 2 else 2000
worst = (mp.inf, None)
worst_raw = (mp.inf, None)
cnt_needed = 0
for k in range(n):
    mode = k % 4
    if mode == 0:
        th = rng.uniform(0.001, 0.5); al, be = rng.uniform(0, 1, 2); ga = rng.uniform(0, np.pi)
    elif mode == 1:
        th = 0.5 - 10 ** rng.uniform(-6, -0.5); al, be = 10 ** rng.uniform(-4, 0, 2) * 0.999; ga = rng.uniform(0, np.pi)
    elif mode == 2:
        th = rng.choice([0.5, 0.49, 0.45, 0.3, 0.1, 0.01]); al, be = 1 - 10 ** rng.uniform(-6, 0, 2); ga = rng.uniform(0, np.pi)
    else:
        th = rng.uniform(0.001, 0.5); al, be = rng.uniform(0, 1, 2); ga = rng.choice([1e-3, np.pi - 1e-3, 1e-2, np.pi - 1e-2])
    q = quantities(th, al, be, ga, dps=60)
    d = Dc(q)
    R = d / (q['al'] ** 2 * q['be'] ** 2 * mp.sin(q['ga']) ** 2)
    if R < worst[0]:
        worst = (R, (th, al, be, ga, float(d)))
    if d < worst_raw[0]:
        worst_raw = (d, (th, al, be, ga))
print('worst R =', mp.nstr(worst[0], 8), worst[1])
print('worst raw Dc =', mp.nstr(worst_raw[0], 8), worst_raw[1])
