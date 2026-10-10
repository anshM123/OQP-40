"""Numerical evidence only (mpmath, numerical differentiation): Lemma 4 margins of the Gaussian-design certificate in
the open strip a < 3 (s < e^{3/n}) for n = 37, 50, 100 and the limit kernel, in the normalised form
a L1, L2, a L3 (which stay bounded as a -> 0).  Usage: python tb_scan_strip.py > tb_scan_strip.log"""
import mpmath as mp
from tb_check_arb import ref_margins

A = [0.001, 0.003, 0.01, 0.03, 0.1, 0.3, 0.6, 1.0, 1.5, 2.0, 2.5, 3.0]
D = [0.001, 0.01, 0.05, 0.2, 0.5, 1, 2, 3, 5, 8, 12, 20, 40, 80, 160, 320]
for n in (37, 50, 100, 'inf'):
    worst = [None] * 3
    for a in A:
        for d in D:
            nn = 1000 if n == 'inf' else n
            mp.mp.dps = int(60 + (a + d) / 2.3 + 3 * nn / 10)
            L1, L2, L3 = ref_margins(n, mp.mpf(a), mp.mpf(a) + mp.mpf(d))
            vals = (a * L1, L2, a * L3)
            for k in range(3):
                v = float(vals[k])
                if worst[k] is None or v < worst[k][0]:
                    worst[k] = (v, a, d)
    print(f"n = {n}: min a*L1 = {worst[0][0]:.4f} at (a,d) = {worst[0][1:]}, min L2 = {worst[1][0]:.4f} at {worst[1][1:]}, "
          f"min a*L3 = {worst[2][0]:.5f} at {worst[2][1:]}", flush=True)
