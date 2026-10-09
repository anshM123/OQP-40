"""Referee check, task 3: optimizer-driven search for violations of Theorem 4.
torch (CPU, complex128) L-BFGS (strong Wolfe) over A = e^H, B = e^K, H, K Hermitian, many random restarts, d = 2..8.
Objectives:  O1 = ratio (tr A^3B^3 + 2 Re tr A^2BAB^2) / (3 tr (AB)^3)    [Theorem 4 <=> O1 >= 1]
             O2 = J = f / tr(AYBY), Y = -i[A,B]                          [Theorem 4 <=> O2 >= 0 for non-commuting pairs]
Every final minimiser is re-evaluated EXACTLY (ball arithmetic, exact congruence A = V diag(e^w) V^*), so float
cancellation cannot produce a fake violation (or hide a real one).
"""
import sys, time, math
import numpy as np
import torch
from flint import arb, acb, ctx
sys.path.insert(0, '.')
from refutil import to_acb, ctrans, diag_acb, tr

torch.set_num_threads(2)
torch.set_default_dtype(torch.float64)
out = []
def say(*a):
    s = ' '.join(str(x) for x in a)
    print(s, flush=True)
    out.append(s)

def herm_t(p, d):
    re = p[: d * d].reshape(d, d); im = p[d * d:].reshape(d, d)
    M = torch.complex(re, im)
    return (M + M.conj().T) / 2

def mats(p, d):
    H = herm_t(p[: 2 * d * d], d); K = herm_t(p[2 * d * d:], d)
    return torch.linalg.matrix_exp(H), torch.linalg.matrix_exp(K)

def quantities(A, B):
    A2 = A @ A; B2 = B @ B; AB = A @ B; BA = B @ A
    t1 = torch.trace(A2 @ A @ B2 @ B).real
    t2 = torch.trace(A2 @ B @ A @ B2).real
    t3 = torch.trace(AB @ AB @ AB).real
    Y = -1j * (AB - BA)
    den = torch.trace(A @ Y @ B @ Y).real
    f = t1 + 2 * t2 - 3 * t3
    return f, t1 + 2 * t2, 3 * t3, den

def objective(p, d, which):
    A, B = mats(p, d)
    f, lhs, rhs, den = quantities(A, B)
    if which == 'ratio':
        return lhs / rhs
    return f / den

ctx.prec = 512
I_ = acb(0, 1)
def exact_eval(p, d):
    p = p.detach().numpy()
    def herm_np(q):
        M = (q[: d * d] + 1j * q[d * d:]).reshape(d, d); return (M + M.conj().T) / 2
    H, K = herm_np(p[: 2 * d * d]), herm_np(p[2 * d * d:])
    wh, Vh = np.linalg.eigh(H); wk, Vk = np.linalg.eigh(K)
    def cong(U, lam):
        Ua = to_acb(U); D = diag_acb([arb(float(x)) for x in lam]); return Ua * D * ctrans(Ua)
    A = cong(Vh, np.exp(wh)); B = cong(Vk, np.exp(wk))
    AB, BA = A * B, B * A
    t1 = tr(A * A * A * B * B * B).real; t2 = tr(A * A * B * A * B * B).real; t3 = tr(AB * AB * AB).real
    f = t1 + 2 * t2 - 3 * t3
    Y = (AB - BA) * (-I_)
    den = tr(A * Y * B * Y).real
    return f, (t1 + 2 * t2) / (3 * t3), f / den, np.exp(wh.max() - wh.min()), np.exp(wk.max() - wk.min())

rng = np.random.default_rng(2027)
t0 = time.time()
summary = {}
for which in ('ratio', 'J'):
    for d in range(2, 9):
        best = (math.inf, None)
        nrest = 40 if d <= 5 else 24
        for rs in range(nrest):
            sc = float(rng.choice([0.3, 1.0, 2.0, 4.0]))
            p = torch.tensor(sc * rng.normal(size=4 * d * d), requires_grad=True)
            opt = torch.optim.LBFGS([p], lr=1, max_iter=300, line_search_fn='strong_wolfe', tolerance_grad=1e-14, tolerance_change=1e-16)
            def closure():
                opt.zero_grad()
                val = objective(p, d, which)
                if not torch.isfinite(val):
                    val = torch.tensor(1e6, requires_grad=True)
                val.backward()
                return val
            try:
                opt.step(closure)
            except Exception:
                continue
            with torch.no_grad():
                val = float(objective(p, d, which))
            if math.isfinite(val) and val < best[0]:
                best = (val, p.detach().clone())
        if best[1] is None:
            say(f'[{which}] d={d}: no finite result'); continue
        f, ratio, J, ca, cb = exact_eval(best[1], d)
        summary[(which, d)] = (best[0], ratio, J, f)
        say(f'[{which}] d={d}: float min {best[0]:.10g} | exact: ratio-1 = {(ratio - 1).mid().str(6)}, J = {J.mid().str(8)}, '
            f'f>0 certified {f.lower() > 0}, f = {f.mid().str(5)} | cond A {ca:.2e}, cond B {cb:.2e}  ({time.time() - t0:.0f}s)')
open('r5b_optimizer.log', 'w').write('\n'.join(out) + '\n')
