"""Targeted search for a counterexample to the OQP 40 lower half at (n,m) = (3,3), starting in the region where the
non-nearly-symmetric necklace AABABB has negative trace (Hillar-Johnson; Garbe-Wei Thm 2.8).
p_{3,3} = (6 tr A^3B^3 + 12 Re tr A^2BAB^2 + 2 tr (AB)^3)/20.
Phase 1: minimise Re tr(A^2 B A B^2) / tr(A^3 B^3) (find negative-word pairs).
Phase 2: from there, minimise log p_{3,3} - log tr exp(3 log A + 3 log B).  Real symmetric and complex runs."""
import sys

import torch

d = int(sys.argv[1]) if len(sys.argv) > 1 else 3
batch = 512
torch.manual_seed(int(sys.argv[2]) if len(sys.argv) > 2 else 0)
dev = "cuda" if torch.cuda.is_available() else "cpu"
cdt = torch.complex128


def herm(X):
    return (X + X.conj().transpose(-1, -2)) / 2


def tr(X):
    return torch.diagonal(X, dim1=-2, dim2=-1).sum(-1).real


def mats(X1, X2):
    H1, H2 = herm(X1), herm(X2)
    return H1, H2, torch.linalg.matrix_exp(H1), torch.linalg.matrix_exp(H2)


def p33(A, B):
    A2, B2 = A @ A, B @ B
    t1 = tr(A2 @ A @ B2 @ B)
    t2 = tr(A2 @ B @ A @ B2)
    t3 = tr(torch.linalg.matrix_power(A @ B, 3))
    return (6 * t1 + 12 * t2 + 2 * t3) / 20, t2 / t1


for real in (True, False):
    X1 = torch.randn(batch, d, d, dtype=torch.float64, device=dev).to(cdt) * 2.5
    X2 = torch.randn(batch, d, d, dtype=torch.float64, device=dev).to(cdt) * 2.5
    if not real:
        X1 = X1 + 1j * 2.5 * torch.randn(batch, d, d, dtype=torch.float64, device=dev)
        X2 = X2 + 1j * 2.5 * torch.randn(batch, d, d, dtype=torch.float64, device=dev)
    X1.requires_grad_(True); X2.requires_grad_(True)
    opt = torch.optim.Adam([X1, X2], lr=0.03)
    for it in range(1500):                         # phase 1
        opt.zero_grad()
        H1, H2, A, B = mats(X1, X2)
        _, ratio = p33(A, B)
        ratio = torch.where(torch.isfinite(ratio), ratio, torch.zeros_like(ratio))
        ratio.sum().backward()
        opt.step()
        with torch.no_grad():
            for X in (X1, X2):
                nrm = torch.linalg.matrix_norm(herm(X), ord=2)
                X *= torch.clamp(10.0 / nrm, max=1.0)[:, None, None]
    with torch.no_grad():
        H1, H2, A, B = mats(X1, X2)
        _, ratio = p33(A, B)
    print(f"{'real' if real else 'complex'} d={d}: phase 1 min Re tr(A^2BAB^2)/tr(A^3B^3) = {ratio.min().item():+.4e}, "
          f"negative in {(ratio < 0).sum().item()}/{batch}", flush=True)
    opt = torch.optim.Adam([X1, X2], lr=0.01)
    best = float("inf")
    for it in range(3000):                         # phase 2
        opt.zero_grad()
        H1, H2, A, B = mats(X1, X2)
        p, _ = p33(A, B)
        L = tr(torch.linalg.matrix_exp(3 * H1 + 3 * H2))
        f = torch.log(p) - torch.log(L)
        bad = ~torch.isfinite(f)
        torch.where(bad, torch.zeros_like(f), f).sum().backward()
        opt.step()
        with torch.no_grad():
            for X in (X1, X2):
                nrm = torch.linalg.matrix_norm(herm(X), ord=2)
                X *= torch.clamp(10.0 / nrm, max=1.0)[:, None, None]
        cur = torch.where(bad, torch.full_like(f, float("inf")), f).min().item()
        best = min(best, cur)
    print(f"{'real' if real else 'complex'} d={d}: phase 2 min log(p33/L) = {best:+.4e}", flush=True)
