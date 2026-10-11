"""NUMERICAL: F as a function of w at fixed (theta, a, c), c = r b. Concavity test (second differences), and the
normalised ratio F/((1-w^2) a^2 c^2).
Ansh Mishra, Aryan Senthilkumar."""
import numpy as np
import mpmath as mp
mp.mp.dps = 40
from hyp import F


def Fc(th, a, c, w):
    r = (1 - mp.mpf(th)) / mp.mpf(th)
    return F(th, a, c / r, w)


for th in (0.5, 0.45, 0.3, 0.1, 0.02):
    for (a, c) in ((0.05, 0.05), (0.3, 0.3), (1.0, 1.0), (1.0, 0.2), (0.2, 1.0), (3.0, 3.0), (3.0, 0.5), (6.0, 6.0)):
        ws = [mp.mpf(-1) + mp.mpf(2) * k / 200 for k in range(201)]
        vals = [Fc(th, a, c, w) for w in ws]
        d2 = [vals[k - 1] - 2 * vals[k] + vals[k + 1] for k in range(1, 200)]
        npos = sum(1 for v in d2 if v > 0)
        firstpos = [float(ws[k + 1]) for k in range(199) if d2[k] > 0]
        R = [vals[k] / ((1 - ws[k] ** 2) * a ** 2 * c ** 2) for k in range(1, 200)]
        print(f"th={th:.2f} a={a:4.2f} c={c:4.2f}: min F={mp.nstr(min(vals[1:-1]), 5)}  #convex 2nd diffs={npos:3d} "
              f"(w-range {min(firstpos) if firstpos else None},{max(firstpos) if firstpos else None})  "
              f"Rnorm range [{mp.nstr(min(R), 5)}, {mp.nstr(max(R), 5)}]")
