"""NUMERICAL: landscape of Rhat = F/(a^2 b^2 (1-w^2)) in hyperbolic coordinates; consistency with cf2x2.
Ansh Mishra, Aryan Senthilkumar."""
import sys
import numpy as np
import mpmath as mp
mp.mp.dps = 50
from hyp import parts, F, Rhat
from cf2x2 import quantities, Dc

# 1. consistency with the matrix closed forms (cf2x2): (C) <=> Dc >= 0 <=> F >= 0, same sign; compare G, P
rng = np.random.default_rng(0)
for k in range(5):
    th = rng.uniform(0.05, 0.5); al, be = rng.uniform(0.05, 0.95, 2); ga = rng.uniform(0.1, 3.0)
    q = quantities(th, al, be, ga, dps=50)
    a, b, w = mp.atanh(al), mp.atanh(be), mp.cos(ga)
    h = parts(th, a, b, w)
    # scale: cf2x2 has A = I + al sz = sqrt(1-al^2) e^{a sz}; P scales by (1-al^2)^{1/2} (1-be^2)^{r/2}; G by ^{-th/2}...
    sP = mp.sqrt(1 - al ** 2) * (1 - be ** 2) ** (q['r'] / 2)
    sG = (1 - al ** 2) ** (-th / 2) * (1 - be ** 2) ** (-(1 - th) / 2)
    print(f"P ratio {mp.nstr(q['P'] / (sP * h['P']), 15)}  G ratio {mp.nstr(q['G'] / (sG * h['G']), 15)}  "
          f"sign Dc {mp.sign(Dc(q))} F {mp.nstr(F(th, a, b, w), 6)}")

# 2. landscape
def scan(ths, As, Bs, Ws):
    worst = (mp.inf, None)
    for th in ths:
        for a in As:
            for b in Bs:
                for w in Ws:
                    v = Rhat(th, a, b, w)
                    if v < worst[0]:
                        worst = (v, (th, a, b, w))
    return worst

ths = [0.5, 0.49, 0.45, 0.4, 1 / 3, 0.25, 0.1, 0.03]
As = [0.01, 0.1, 0.3, 1.0, 2.0, 4.0, 8.0]
Ws = [-0.999, -0.9, -0.5, 0.0, 0.5, 0.9, 0.999]
for th in ths:
    w_ = scan([th], As, As, Ws)
    print(f"theta={th:.3f}: min Rhat = {mp.nstr(w_[0], 6)} at {w_[1]};  identity value (1-t)(1-2t)(1+t)/(3t) = "
          f"{(1 - th) * (1 - 2 * th) * (1 + th) / (3 * th):.6f}")
