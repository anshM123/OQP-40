"""Referee check, task 3 (extension): Theorem 4 at large dimension d = 50, 80, 100, exact pairs, ball arithmetic.
Includes clustered spectra of A (few distinct eigenvalues with high multiplicity) and spread spectra."""
import sys, time
import numpy as np
from flint import arb, ctx
sys.path.insert(0, '.')
from refutil import to_acb, ctrans, diag_acb, f33

ctx.prec = 256
rng = np.random.default_rng(404)
out = []
def say(*a):
    s = ' '.join(str(x) for x in a); print(s, flush=True); out.append(s)

def cong(U, lam):
    Ua = to_acb(U); D = diag_acb([arb(float(v)) for v in lam]); return Ua * D * ctrans(Ua)

t0 = time.time()
minratio = (np.inf, None); viol = 0; n = 0
for d in (50, 80, 100):
    for rep in range(8):
        U = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))
        V = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))
        if rep % 2 == 0:
            la = np.exp(rng.choice([-3.0, 0.0, 2.0, 4.0], size=d))     # A with 4 distinct eigenvalues, high multiplicity
        else:
            la = 10.0 ** rng.uniform(-8, 0, size=d)                    # spread spectrum
        lb = 10.0 ** rng.uniform(-6, 0, size=d)
        f, lhs, rhs, _ = f33(cong(U, la), cong(V, lb))
        n += 1
        if f.upper() < 0: viol += 1
        r = float((lhs / rhs).mid())
        if r < minratio[0]: minratio = (r, f'd={d} rep={rep}')
        say(f'd={d} rep={rep}: ratio = {r:.10g}, f > 0 certified: {f.lower() > 0}  ({time.time() - t0:.0f}s)')
say(f'SUMMARY: {n} pairs, certified violations {viol}, min ratio {minratio[0]:.10g} at {minratio[1]}')
open('r4b_large_d.log', 'w').write('\n'.join(out) + '\n')
