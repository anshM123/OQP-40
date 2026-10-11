"""Check: bottom-level TF value at theta = 1/2 near the identity equals
  (h^5/48) Tr((S - s_min) K) + O(h^6),  S = (X+Y)/2,  K = -[X,Y]^2 >= 0."""
import mpmath as mp, random, sys
from ni_lib import herm, tbot_half
mp.mp.dps = 60
rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 5)
h1, h2 = mp.mpf('1e-4'), mp.mpf('5e-5')
worst = 0
for trial in range(12):
    d = [2, 3, 3, 4, 5][trial % 5]
    X, Y = herm(d, rng), herm(d, rng)
    r = [tbot_half(X, Y, h) / h ** 5 for h in (h1, h2)]
    c5 = 2 * r[1] - r[0]
    S = (X + Y) / 2
    smin = min(mp.eighe(S)[0][i] for i in range(d))
    C = X * Y - Y * X
    K = -(C * C)
    pred = mp.re(sum(((S - smin * mp.eye(d)) * K)[i, i] for i in range(d))) / 48
    rel = abs(c5 / pred - 1)
    worst = max(worst, rel)
    print(f"d={d}  c5={mp.nstr(c5, 12)}  pred={mp.nstr(pred, 12)}  rel.diff={mp.nstr(rel, 3)}")
print('max rel diff', mp.nstr(worst, 3))
