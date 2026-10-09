"""Referee check, task 2 (independent positivity proof): verified interval arithmetic (python-flint arb) for
conditions (I), (II), (III) of Section 8.3 on the whole needed domain 0 < B <= C < infinity.

No rational parametrisation and no use of the authors' polynomials: the conditions are evaluated from the referee's
direct chain-rule formulas in (B, C) (validated against sympy's diff in r2_symbolic.py), split as
    Cond_j = S_j + T_j,   S_j from 3 + (B+k)/C (explicitly positive),   T_j from 8 (C-B) h, h = (sqrt(C+k)+sqrt(C+4B+k))^-2.
Homogeneity: Cond_j(B, C; k) is homogeneous of degree 0 in (B, C, k) jointly, so with t = B/C in [0, 1]:
    chart 1 (C >= 1/2):  Cond_j(B, C; 5) = Cond_j(t, 1; kk),          kk = 5/C in [0, 10]  (kk = 0 is the limit C -> inf);
    chart 2 (C <= 1/2):  Cond_j(B, C; 5) = Cond_j(t*eta, eta; 1),     eta = C/5 in (0, 0.1];  we certify eta*Cond_j > 0
                          using an algebraically rewritten form of eta*Cond_j that is analytic at eta = 0.
Each box is accepted only when the arb enclosure of every condition has a strictly positive lower endpoint.
"""
import sys, time, random
import mpmath as mp
from flint import arb, ctx

ctx.prec = 128
out = []
def say(*a):
    s = ' '.join(str(x) for x in a)
    print(s, flush=True)
    out.append(s)


def hparts(P, Q):
    S = P + Q
    h = 1 / (S * S)
    hB = -4 / (Q * S**3)
    hC = -h / (P * Q)
    hBC = (2 * P + 6 * Q) / (P * Q**3 * S**3)
    return h, hB, hC, hBC


def chart1(t, kk):
    """Cond_j(t, 1; kk) for j = I, II, III (C = 1, B = t)."""
    P = (1 + kk).sqrt(); Q = (1 + 4 * t + kk).sqrt()
    h, hB, hC, hBC = hparts(P, Q)
    u = 1 - t
    TI = 8 * (u * h + 2 * t * (-h + u * hB))
    TII = 8 * (u * h - 2 * (h + u * hC))
    TIII = 8 * (u * h + 2 * t * (-h + u * hB) - 2 * (h + u * hC) - 4 * t * (-hC + hB + u * hBC))
    return (3 + 3 * t + kk + TI, 3 + 3 * (t + kk) + TII, 3 + 9 * t + 3 * kk + TIII)


def chart2(t, eta):
    """eta * Cond_j(t*eta, eta; 1) for j = I, II, III, written without division by eta."""
    P = (1 + eta).sqrt(); Q = (1 + eta * (1 + 4 * t)).sqrt()
    h, hB, hC, hBC = hparts(P, Q)
    u = 1 - t
    e2 = eta * eta
    TI = 8 * e2 * (u * h - 2 * t * h + 2 * t * eta * u * hB)
    TII = 8 * e2 * (u * h - 2 * h - 2 * eta * u * hC)
    TIII = 8 * e2 * (u * h + 2 * t * (-h + eta * u * hB) - 2 * (h + eta * u * hC) - 4 * t * eta * (-hC + hB + eta * u * hBC))
    return (3 * eta + 3 * t * eta + 1 + TI, 3 * eta + 3 * t * eta + 3 + TII, 3 * eta + 9 * t * eta + 3 + TIII)


# ---------- consistency of the chart formulas with the direct formula Cond(B, C; 5) (non-rigorous sanity, 50 digits)
mp.mp.dps = 50
def cond_direct(Bv, Cv, kv=5):
    P = mp.sqrt(Cv + kv); Q = mp.sqrt(Cv + 4 * Bv + kv)
    S = P + Q; h = 1 / S**2; hB = -4 / (Q * S**3); hC = -h / (P * Q); hBC = (2 * P + 6 * Q) / (P * Q**3 * S**3)
    G = 3 + (Bv + kv) / Cv + 8 * (Cv - Bv) * h
    GB = 1 / Cv + 8 * (-h + (Cv - Bv) * hB)
    GC = -(Bv + kv) / Cv**2 + 8 * (h + (Cv - Bv) * hC)
    GBC = -1 / Cv**2 + 8 * (-hC + hB + (Cv - Bv) * hBC)
    return (G + 2 * Bv * GB, G - 2 * Cv * GC, G + 2 * Bv * GB - 2 * Cv * GC - 4 * Bv * Cv * GBC)

def mp_from_arb(a): return mp.mpf(a.mid().str(40, radius=False))
random.seed(11)
maxrel = 0
for _ in range(300):
    Cv = mp.mpf(10) ** random.uniform(-4, 5); tv = mp.mpf(random.random())
    d = cond_direct(tv * Cv, Cv)
    a1 = chart1(arb(mp.nstr(tv, 45)), arb(mp.nstr(5 / Cv, 45)))
    eta = Cv / 5
    a2 = chart2(arb(mp.nstr(tv, 45)), arb(mp.nstr(eta, 45)))
    for j in range(3):
        maxrel = max(maxrel, abs(mp_from_arb(a1[j]) - d[j]) / abs(d[j]), abs(mp_from_arb(a2[j]) / eta - d[j]) / abs(d[j]))
say(f'chart formulas vs direct Cond(B,C;5): max rel diff {mp.nstr(maxrel, 3)} over 300 random points (should be ~1e-35)')

# ---------- rigorous subdivision
def box_arb(lo, hi):
    """arb ball containing [lo, hi] (lo, hi Python floats exactly representable as dyadics)."""
    a = arb(lo); b = arb(hi)
    return a.union(b)

def certify(chart, t0, t1, s0, s1, max_boxes=2_000_000):
    stack = [(t0, t1, s0, s1)]
    n_ok = 0; n_eval = 0
    minlow = [float('inf')] * 3
    while stack:
        a0, a1, b0, b1 = stack.pop()
        vals = chart(box_arb(a0, a1), box_arb(b0, b1))
        n_eval += 1
        lows = [v.lower() for v in vals]
        if all(lw > 0 for lw in lows):
            n_ok += 1
            for j in range(3):
                minlow[j] = min(minlow[j], float(lows[j]))
            continue
        if n_eval > max_boxes:
            return False, n_ok, n_eval, minlow, (a0, a1, b0, b1)
        am = (a0 + a1) / 2; bm = (b0 + b1) / 2
        stack += [(a0, am, b0, bm), (am, a1, b0, bm), (a0, am, bm, b1), (am, a1, bm, b1)]
    return True, n_ok, n_eval, minlow, None

t_start = time.time()
ok1, n1, e1, m1, bad1 = certify(chart1, 0.0, 1.0, 0.0, 10.0)
say(f'chart 1 (t in [0,1], kk = 5/C in [0,10], i.e. C >= 1/2 incl. C = inf): certified={ok1}, boxes={n1}, evaluations={e1}, '
    f'min certified lower bounds (I,II,III) = {[round(v, 4) for v in m1]}', '' if ok1 else f' FAILED BOX {bad1}')
ok2, n2, e2, m2, bad2 = certify(chart2, 0.0, 1.0, 0.0, 0.1)
say(f'chart 2 (t in [0,1], eta = C/5 in [0,0.1], i.e. 0 < C <= 1/2, scaled by eta): certified={ok2}, boxes={n2}, evaluations={e2}, '
    f'min certified lower bounds = {[round(v, 4) for v in m2]}', '' if ok2 else f' FAILED BOX {bad2}')
say(f'time {time.time() - t_start:.1f}s; precision {ctx.prec} bits')
say('CONCLUSION: (I), (II), (III) > 0 on all of {0 <= B <= C, C > 0}' if (ok1 and ok2) else 'CONCLUSION: certification incomplete')

# ---------- bonus: where are the conditions smallest? (non-rigorous scan, chart 1 and chart 2)
best = [(float('inf'), None)] * 3
for i in range(201):
    for jj in range(201):
        tv = i / 200; kv = 10 * jj / 200
        vals = chart1(arb(tv), arb(kv))
        for j in range(3):
            fv = float(vals[j].mid())
            if fv < best[j][0]:
                best[j] = (fv, (tv, 5 / kv if kv > 0 else float('inf')))
say('smallest values on a 201x201 chart-1 grid (value, (t, C)):', [(round(b[0], 4), b[1]) for b in best])
open('r3_interval.log', 'w').write('\n'.join(out) + '\n')
