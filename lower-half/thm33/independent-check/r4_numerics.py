"""Referee check, task 3: adversarial numerics for Theorem 4 with rigorous ball arithmetic (python-flint).

For each pair (A, B) the matrices are built EXACTLY (from float64 data by exact arithmetic: congruences
U diag(lam) U^*, or I + eps*N built in arb), so every enclosure below is a rigorous enclosure of the exact
quantities for that exact pair. Quantities:
    ratio = (tr A^3B^3 + 2 Re tr A^2BAB^2) / (3 tr (AB)^3)          (Theorem 4  <=>  ratio >= 1)
    f     = tr A^3B^3 + 2 Re tr A^2BAB^2 - 3 tr (AB)^3
    J     = f / tr(A Y B Y),  Y = -i[A,B]                           (scale-invariant; J >= 0 <=> Theorem 4 for non-commuting pairs)
A violation would be certified by f.upper() < 0.  Precision adapts (256 -> 1024 -> 4096 bits) until the sign of f is
decided (or f is certified 0 for exactly commuting data).
Also checks the identity f = tr(AYBY) + 2 tr((AB+BA) Y^2) (OQP40_RESULTS section 6) on every sample.
"""
import sys, time, math
import numpy as np
from flint import arb, acb, acb_mat, ctx
sys.path.insert(0, '.')
from refutil import to_acb, ctrans, f33, tr, diag_acb

out = []
def say(*a):
    s = ' '.join(str(x) for x in a)
    print(s, flush=True)
    out.append(s)

I_ = acb(0, 1)

def eval_pair(build, label_stats, max_bits=4096):
    """build(prec) -> (A, B) acb_mat. Returns dict with ratio/J as floats and sign info, using adaptive precision."""
    bits = 256
    while True:
        ctx.prec = bits
        A, B = build()
        f, lhs, rhs, (t1, t2, t3) = f33(A, B)
        AB = A * B; BA = B * A
        Y = (AB - BA) * (-I_)
        tAYBY = tr(A * Y * B * Y).real
        ident = tAYBY + 2 * tr((AB + BA) * Y * Y).real
        decided = (f.lower() > 0) or (f.upper() < 0)
        if decided or bits >= max_bits:
            break
        bits *= 4
    res = {'bits': bits, 'f_lo': f.lower(), 'f_hi': f.upper(), 'decided': decided}
    res['ratio'] = float((lhs / rhs).mid()) if rhs.lower() > 0 else float('nan')
    res['ratio_m1'] = (lhs / rhs - 1)                  # arb
    if tAYBY.lower() > 0:
        Jv = f / tAYBY
        res['J'] = float(Jv.mid()); res['J_lo'] = float(Jv.lower())
    else:
        res['J'] = float('nan'); res['J_lo'] = float('nan')
    scale = abs(t1.real).upper()
    res['ident_rel'] = float((abs(ident - f) / scale).upper()) if scale > 0 else 0.0
    return res

class Stats:
    def __init__(self, name):
        self.name = name; self.n = 0; self.viol = 0; self.undec = 0; self.min_ratio = (math.inf, None)
        self.min_J = (math.inf, None); self.max_ident = 0.0; self.bits_hist = {}
    def add(self, res, tag):
        self.n += 1
        if res['f_hi'] < 0: self.viol += 1
        if not res['decided']: self.undec += 1
        if res['ratio'] < self.min_ratio[0]: self.min_ratio = (res['ratio'], tag, float(res['ratio_m1'].mid()))
        if not math.isnan(res['J']) and res['J'] < self.min_J[0]: self.min_J = (res['J'], tag)
        self.max_ident = max(self.max_ident, res['ident_rel'])
        self.bits_hist[res['bits']] = self.bits_hist.get(res['bits'], 0) + 1
    def report(self):
        say(f'[{self.name}] pairs={self.n}  certified violations (f<0)={self.viol}  undecided={self.undec}  precision use={self.bits_hist}')
        say(f'    min ratio = {self.min_ratio[0]:.15g} (ratio-1 = {self.min_ratio[2] if self.min_ratio[1] else float("nan"):.3e}) at {self.min_ratio[1]}')
        say(f'    min J = f/tr(AYBY) = {self.min_J[0]:.6g} at {self.min_J[1]}')
        say(f'    identity f = tr(AYBY) + 2tr((AB+BA)Y^2): max rel err {self.max_ident:.2e}')

rng = np.random.default_rng(91)

def rand_U(d, cplx=True):
    U = rng.normal(size=(d, d))
    if cplx:
        U = U + 1j * rng.normal(size=(d, d))
    return U

def cong(U, lam):
    Ua = to_acb(U)
    D = diag_acb([arb(float(v)) for v in lam])
    return Ua * D * ctrans(Ua)

T0 = time.time()
# ---------------------------------------------------------------- 1. random PD pairs, d = 2..30
S1 = Stats('random PD pairs d=2..30 (complex and real, log-normal spectra)')
for d in range(2, 31):
    for rep in range(60 if d <= 12 else 25):
        cplx = rep % 3 != 0
        sa, sb = rng.choice([0.3, 1, 2, 4]), rng.choice([0.3, 1, 2, 4])
        U, V = rand_U(d, cplx), rand_U(d, cplx)
        la, lb = np.exp(sa * rng.normal(size=d)), np.exp(sb * rng.normal(size=d))
        res = eval_pair(lambda: (cong(U, la), cong(V, lb)), S1)
        S1.add(res, f'd={d} cplx={cplx} sa={sa} sb={sb}')
S1.report()

# ---------------------------------------------------------------- 2. extreme spectra (condition numbers up to 1e12 .. 1e16)
S2 = Stats('extreme spectra, condition numbers 1e6..1e16')
for rep in range(1500):
    d = int(rng.integers(2, 17))
    kind = rep % 4
    cond_exp = float(rng.choice([6, 9, 12, 16]))
    def spec():
        if kind == 0:   # log-uniform
            return 10.0 ** rng.uniform(-cond_exp, 0, size=d)
        if kind == 1:   # two clusters
            return np.where(rng.random(d) < 0.5, 10.0 ** (-cond_exp), 1.0) * np.exp(0.01 * rng.normal(size=d))
        if kind == 2:   # geometric
            return 10.0 ** (-cond_exp * np.arange(d) / max(d - 1, 1))
        return np.concatenate([[1.0], 10.0 ** (-cond_exp) * np.exp(rng.normal(size=d - 1))])  # one dominant eigenvalue
    la, lb = spec(), spec()
    U, V = rand_U(d), rand_U(d)
    res = eval_pair(lambda: (cong(U, la), cong(V, lb)), S2)
    S2.add(res, f'd={d} kind={kind} cond=1e{int(cond_exp)}')
S2.report()

# ---------------------------------------------------------------- 3. near-commuting pairs: A diagonal, B = V diag(beta) V^*, V = I + eps N
S3 = Stats('near-commuting pairs (A diagonal, B = (I+eps N) diag (I+eps N)^*), eps = 1e-1..1e-12')
for rep in range(1200):
    d = int(rng.integers(2, 13))
    eps = 10.0 ** (-float(rng.integers(1, 13)))
    al = np.exp(rng.uniform(-3, 3, size=d)); be = np.exp(rng.uniform(-3, 3, size=d))
    if rep % 5 == 0:
        al[: d // 2] = al[0]   # repeated eigenvalues of A
    N = rand_U(d)
    def build():
        A = diag_acb([arb(float(v)) for v in al])
        Na = to_acb(N)
        Id = diag_acb([arb(1)] * d)
        Vm = Id + Na * acb(arb(eps))
        B = Vm * diag_acb([arb(float(v)) for v in be]) * ctrans(Vm)
        return A, B
    res = eval_pair(build, S3)
    S3.add(res, f'd={d} eps={eps:g}')
S3.report()

# ---------------------------------------------------------------- 4. rank-deficient (exact zeros) and near-singular (1e-30)
S4 = Stats('rank-deficient / near-singular (PSD with exact zero eigenvalues, or 1e-30)')
for rep in range(1200):
    d = int(rng.integers(2, 13))
    la = np.exp(rng.normal(size=d)); lb = np.exp(rng.normal(size=d))
    ka = int(rng.integers(0, d)); kb = int(rng.integers(0, d))
    tiny = 0.0 if rep % 2 == 0 else 1e-30
    la[:ka] = tiny; lb[:kb] = tiny
    if rep % 7 == 0:          # rank one A or B
        la[:] = tiny; la[0] = 1.0
    U, V = rand_U(d), rand_U(d)
    res = eval_pair(lambda: (cong(U, la), cong(V, lb)), S4)
    S4.add(res, f'd={d} rankA={d - ka} rankB={d - kb} tiny={tiny:g}')
S4.report()

# ---------------------------------------------------------------- 5. Cha-Lee family (arXiv:2603.19927, Sec. II) and shifts
S5 = Stats('Cha-Lee family A_x + dA I, B_x + dB I (x = 1e-10..10, shifts 0..1), plus random conjugation of B')
def chalee(x, dA, dB, rot=None):
    xa = arb(x)
    A = acb_mat([[1 + arb(dA), 0, 0], [0, xa + arb(dA), -xa], [0, -xa, xa + arb(dA)]])
    B = acb_mat([[xa + arb(dB), -xa, 0], [-xa, xa + arb(dB), 0], [0, 0, 1 + arb(dB)]])
    if rot is not None:
        Vm = diag_acb([arb(1)] * 3) + to_acb(rot)
        B = Vm * B * ctrans(Vm)
    return A, B
xs = [10.0 ** e for e in np.linspace(-10, 1, 45)]
shifts = [0.0, 1e-12, 1e-8, 1e-4, 1e-2, 1e-1, 1.0]
for x in xs:
    for dA in shifts:
        for dB in shifts:
            res = eval_pair(lambda: chalee(x, dA, dB), S5)
            S5.add(res, f'x={x:.3g} dA={dA:g} dB={dB:g}')
    for rep in range(6):
        rot = 10.0 ** rng.uniform(-6, -1) * rand_U(3)
        res = eval_pair(lambda: chalee(x, 1e-6, 1e-6, rot), S5)
        S5.add(res, f'x={x:.3g} dA=dB=1e-6 perturbed B')
S5.report()
say(f'total time {time.time() - T0:.1f}s')
open('r4_numerics.log', 'w').write('\n'.join(out) + '\n')
