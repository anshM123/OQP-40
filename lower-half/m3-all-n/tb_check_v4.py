"""Numerical check (not a proof) of the version-4 forms of tb_arb.py against the definitions (tb_formulas_mp)."""
import random
import mpmath as mp
from flint import arb
import tb_arb as T
from tb_check_arb import ref_margins

random.seed(11)
cases = []
for n in (37, 50, 100, 1000, 'inf'):
    for _ in range(4):
        cases.append((n, round(10 ** random.uniform(-0.7, 2.3), 6), round(random.uniform(3, 8), 6), 'nu4'))
        cases.append((n, round(10 ** random.uniform(-0.7, 2.3), 6), round(10 ** random.uniform(0.9, 2.0), 6), 'nu5'))
        cases.append((n, round(10 ** random.uniform(-0.7, 2.3), 6), round(10 ** random.uniform(-3, 0.5), 6), 'mixed5'))
    cases += [(n, 0.25, 0.05, 'mixed5'), (n, 0.5, 3.0, 'mixed5'), (n, 0.5, 3.0, 'nu4'), (n, 0.3, 8.0, 'nu4'),
              (n, 0.3, 8.0, 'nu5'), (n, 7.9, 2.0, 'mixed5'), (n, 8.1, 2.0, 'mixed5')]
forms = {'nu4': T.logF_nu4, 'nu5': T.logF_nu5, 'mixed5': T.logF_mixed5}
worst = {}
for (n, a, d, form) in cases:
    nn = 1000 if n == 'inf' else n
    mp.mp.dps = int(60 + (a + d) / 2.3 + 3 * nn / 10)
    r = ref_margins(n, mp.mpf(str(a)), mp.mpf(str(a)) + mp.mpf(str(d)))
    eps = arb(0) if n == 'inf' else arb(1) / n
    cx = T.Ctx(eps)
    A = T.J.var(arb(str(a)), 0, T.MP)
    B = T.J.var(arb(str(a)) + arb(str(d)), 1, T.MP)
    (L1, L2, L3), _ = T.margins_from_logF(forms[form](A, B, cx))
    for k, (x, y) in enumerate(zip((L1, L2, L3), r)):
        rel = abs(mp.mpf(x.mid().str(40, radius=False)) - y) / max(abs(y), mp.mpf('1e-30'))
        key = (form, k)
        if key not in worst or rel > worst[key][0]:
            worst[key] = (rel, n, a, d, float(y), float(x.rad()))
for key in sorted(worst):
    rel, n, a, d, y, rad = worst[key]
    print(f"form {key[0]:6s} L{key[1] + 1}: max rel. deviation {float(rel):.2e} (n={n}, a={a}, d={d}, value {y:.6g}, radius {rad:.1e})")
