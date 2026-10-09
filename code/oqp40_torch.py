"""Batched gradient search (torch, complex128) on the lower half of OQP 40:

    p_{n,m}(A,B) >= tr exp(n log A + m log B),   A = e^{H1}, B = e^{H2} > 0.

Minimises f = log p_{n,m} - log tr e^{n H1 + m H2} over Hermitian H1, H2 for a batch of random starts.
f < 0 (beyond rounding) would be a counterexample.

Usage: python oqp40_torch.py d n m [batch] [steps] [seed]"""
import sys
from math import comb

import torch

d, n, m = (int(v) for v in sys.argv[1:4])
batch = int(sys.argv[4]) if len(sys.argv) > 4 else 256
steps = int(sys.argv[5]) if len(sys.argv) > 5 else 3000
seed = int(sys.argv[6]) if len(sys.argv) > 6 else 0
torch.manual_seed(seed)
dev = "cuda" if torch.cuda.is_available() else "cpu"
cdt = torch.complex128


def herm(X):
    return (X + X.conj().transpose(-1, -2)) / 2


def word_average(A, B):
    I = torch.eye(d, dtype=cdt, device=dev).expand_as(A)
    coeffs = [I]
    for _ in range(n + m):
        new = [None] * (len(coeffs) + 1)
        for j, C in enumerate(coeffs):
            CA, CB = C @ A, C @ B
            new[j] = CA if new[j] is None else new[j] + CA
            new[j + 1] = CB
        coeffs = new
    return torch.diagonal(coeffs[m], dim1=-2, dim2=-1).sum(-1).real / comb(n + m, n)


def f(H1, H2):
    A, B = torch.linalg.matrix_exp(H1), torch.linalg.matrix_exp(H2)
    p = word_average(A, B)
    L = torch.diagonal(torch.linalg.matrix_exp(n * H1 + m * H2), dim1=-2, dim2=-1).sum(-1).real
    return torch.log(p) - torch.log(L), p, L


scales = torch.tensor([0.3, 1.0, 2.5, 5.0], dtype=torch.float64, device=dev)[torch.randint(0, 4, (batch,))]
X1 = (torch.randn(batch, d, d, dtype=cdt, device=dev) * scales[:, None, None]).requires_grad_(True)
X2 = (torch.randn(batch, d, d, dtype=cdt, device=dev) * scales[:, None, None]).requires_grad_(True)
opt = torch.optim.Adam([X1, X2], lr=0.02)
best = float("inf")
for it in range(steps):
    opt.zero_grad()
    val, p, L = f(herm(X1), herm(X2))
    bad = ~torch.isfinite(val)
    loss = torch.where(bad, torch.zeros_like(val), val).sum()
    loss.backward()
    opt.step()
    with torch.no_grad():
        # keep the overall scale bounded (f is invariant under H1 -> H1 + c, H2 -> H2 + c')
        for X in (X1, X2):
            tr = torch.diagonal(herm(X), dim1=-2, dim2=-1).sum(-1).real / d
            X -= tr[:, None, None] * torch.eye(d, dtype=cdt, device=dev)
            nrm = torch.linalg.matrix_norm(herm(X), ord=2)
            X *= torch.clamp(12.0 / nrm, max=1.0)[:, None, None]
    cur = torch.where(bad, torch.full_like(val, float("inf")), val).min().item()
    best = min(best, cur)
    if it % 500 == 0 or it == steps - 1:
        print(f"d={d} (n,m)=({n},{m}) step {it}: batch min {cur:+.3e}, best so far {best:+.3e}", flush=True)

with torch.no_grad():
    val, p, L = f(herm(X1), herm(X2))
    val = torch.where(torch.isfinite(val), val, torch.full_like(val, float("inf")))
    i = int(torch.argmin(val))
    print(f"FINAL d={d} (n,m)=({n},{m}): min log-ratio {val[i].item():+.6e}  p={p[i].item():.6e}  L={L[i].item():.6e}")
    if val[i].item() < -1e-8:
        torch.set_printoptions(precision=8, linewidth=200)
        print("H1 =", herm(X1)[i].cpu())
        print("H2 =", herm(X2)[i].cpu())
