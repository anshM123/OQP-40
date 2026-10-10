"""Numerical sanity check of Theorem A (stationary limit): F^R_n(s, s e^{d/n}) -> f_R(d) as n -> infinity,
for R = 1 (f_inf) and for the Gaussian design (f_R = (1-eta) f_inf + eta e^{-lam d}), at sigma = log s in {0.5, 3}.
Direct evaluation from the definitions (closed forms of h_n), mpmath with enough digits for the cancellation."""
import mpmath as mp
import explore_markov as em
import explore_gauss as eg
lam, eta = mp.mpf(7) / 100, mp.mpf(7) / 10
rr = em.make_rr('0.07')
def Phi(d):
    v = 1 - eta * (1 - rr(d))
    return mp.mpf(0) if v >= 1 else -mp.sqrt(-mp.log(v))
def f_inf(d): return 2 * mp.sinh(d / 2) / d - mp.sqrt(em.kap(d) / 2)
for sigma in (0.5, 3.0):
    for d in (1.0, 8.36, 20.0):
        row = []
        for n in (100, 1000, 3000):
            a = sigma * n
            mp.mp.dps = int(40 + 1.2 * (a + d) / 2.3)
            F1 = mp.e**em.setup(str(n), em.make_rr(0))(mp.mpf(a), mp.mpf(a + d))
            FR = mp.e**eg.setup(str(n), Phi)(mp.mpf(a), mp.mpf(a + d))
            row.append((n, F1, FR))
        mp.mp.dps = 30
        fi = f_inf(mp.mpf(d)); fr = (1 - eta) * fi + eta * mp.e**(-lam * d)
        print(f"sigma={sigma} d={d}: " + "; ".join(f"n={n}: F={mp.nstr(F1, 7)}, F^R={mp.nstr(FR, 7)}" for n, F1, FR in row)
              + f"  | limits f_inf={mp.nstr(fi, 7)}, f_R={mp.nstr(fr, 7)}", flush=True)
