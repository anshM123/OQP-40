"""Referee check, task 1 (g): Fact 0.5 (Araki-Lieb-Thirring + Lie-Trotter) for the last step of Theorem 4:
    tr((AB)^3) = tr (A^{1/2} B A^{1/2})^3 >= tr exp(3 log A + 3 log B) = L_33,   so p_33 >= tr((AB)^3) >= L_33.
Numerical sanity check at 40 digits (mpmath eigendecompositions), including the monotone ALT family
    r -> tr (B^{r/2} A^r B^{r/2})^{3/r},  r in (0, 1],  which should increase with r and tend to L_33 as r -> 0.
"""
import random
import mpmath as mp

mp.mp.dps = 40
out = []
def say(*a):
    s = ' '.join(str(x) for x in a)
    print(s, flush=True)
    out.append(s)

def hfun(M, fn):
    E, V = mp.eighe(M)
    return V * mp.diag([fn(e) for e in E]) * V.H

def trc(M): return mp.re(sum(M[i, i] for i in range(M.rows)))

def rand_pd(d, s):
    X = mp.matrix([[mp.mpc(random.gauss(0, 1), random.gauss(0, 1)) for _ in range(d)] for _ in range(d)])
    H = (X + X.H) / 2
    return hfun(H * s, mp.exp)

random.seed(17)
min_frac_over_L = mp.inf; min_p_over_L = mp.inf; mono_ok = True; max_lim_err = mp.mpf(0)
for trial in range(150):
    d = random.choice([2, 3, 4, 5, 6])
    A = rand_pd(d, random.choice([0.3, 1, 2])); B = rand_pd(d, random.choice([0.3, 1, 2]))
    AB = A * B
    t3 = trc(AB * AB * AB)
    L = trc(hfun(3 * hfun(A, mp.log) + 3 * hfun(B, mp.log), mp.exp))
    t1 = trc(A * A * A * B * B * B); t2 = trc(A * A * B * A * B * B)
    p33 = (6 * t1 + 12 * t2 + 2 * t3) / 20
    min_frac_over_L = min(min_frac_over_L, t3 / L); min_p_over_L = min(min_p_over_L, p33 / L)
    # ALT family
    vals = []
    for r in (mp.mpf(1), mp.mpf('0.5'), mp.mpf('0.1'), mp.mpf('0.01'), mp.mpf('0.001')):
        Br = hfun(B, lambda e: e**(r / 2)); Ar = hfun(A, lambda e: e**r)
        vals.append(trc(hfun(Br * Ar * Br, lambda e: e**(3 / r))))
    if any(vals[i] < vals[i + 1] * (1 - mp.mpf(10)**-30) for i in range(len(vals) - 1)):
        mono_ok = False
    max_lim_err = max(max_lim_err, abs(vals[-1] - L) / L)
    if abs(vals[0] - t3) > mp.mpf(10)**-25 * abs(t3):
        mono_ok = False
say(f'150 random PD pairs (d = 2..6, complex):')
say(f'  min tr((AB)^3) / L_33 = {mp.nstr(min_frac_over_L, 8)}   min p_33 / L_33 = {mp.nstr(min_p_over_L, 8)}')
say(f'  ALT family r = 1, .5, .1, .01, .001 nonincreasing and equal to tr((AB)^3) at r = 1: {mono_ok}')
say(f'  rel. distance of the r = 0.001 member from L_33: max {mp.nstr(max_lim_err, 3)} (Lie-Trotter limit, O(r))')
open('r8_alt.log', 'w').write('\n'.join(out) + '\n')
