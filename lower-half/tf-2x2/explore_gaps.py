"""NUMERICAL: concavity in w of the AH gap eps_G and GT gap eps_P (at fixed theta, a, c); ratio eps_G/eps_P;
the sufficient condition (C'): Y_G (1 + X_P) <= theta X_P, with X_P = e^{R_E} eps_P, Y_G = e^{-theta R_E} eps_G.
Ansh Mishra, Aryan Senthilkumar."""
import mpmath as mp
mp.mp.dps = 40
from hyp import parts

def gaps(th, a, c, w):
    th = mp.mpf(th); r = (1 - th) / th
    q = parts(th, a, c / r, w)
    RE = q['N0'] * q['rho']
    return q['epsP'], q['epsG'], mp.exp(RE) * q['epsP'], mp.exp(-th * RE) * q['epsG']

for th in (0.5, 0.45, 0.3, 0.1):
    worst_conc = 0; worst_ratio = 0; worst_Cp = mp.inf; where = None; whereCp = None
    for a in (0.05, 0.3, 1.0, 2.0, 4.0):
        for c in (0.05, 0.3, 1.0, 2.0, 4.0):
            ws = [mp.mpf(-1) + mp.mpf(2) * k / 100 for k in range(101)]
            G = [gaps(th, a, c, w) for w in ws]
            eG = [g[1] for g in G]
            d2 = [eG[k - 1] - 2 * eG[k] + eG[k + 1] for k in range(1, 100)]
            # relative convexity measure
            m = max(d2) / max(abs(x) for x in d2)
            if m > worst_conc:
                worst_conc = m; where = (a, c)
            for k in range(1, 100):
                eP, eGk, XP, YG = G[k]
                rat = eGk / (th * eP)
                if rat > worst_ratio: worst_ratio = rat
                cp = th * XP - YG * (1 + XP)   # (C') margin
                if eP < 1:
                    val = cp / (th * XP)
                    if val < worst_Cp:
                        worst_Cp = val; whereCp = (a, c, float(ws[k]))
    print(f"theta={th}: max positive 2nd diff of eps_G (relative) = {mp.nstr(worst_conc, 4)} at {where}; "
          f"max eps_G/(theta eps_P) = {mp.nstr(worst_ratio, 5)}; min relative (C') margin where eps_P<1: "
          f"{mp.nstr(worst_Cp, 5)} at {whereCp}")
