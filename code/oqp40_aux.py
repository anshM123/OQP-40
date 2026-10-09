"""Batched gradient search on auxiliary inequalities around the lower half of OQP 40 (A = e^{H1}, B = e^{H2} > 0).

  mode 'alt'   :  p_{n,n}(A,B) >= tr (AB)^n                         (average dominates the most alternating word)
  mode 'refine':  p_{n,m}(A,B) >= p_{kn,km}(A^{1/k}, B^{1/k})          (splitting letters lowers the average), k = 2
                  FALSE in general: the Cha-Lee family violates it badly (chalee_family.log)
  mode 'frac'  :  p_{n,m}(A,B) >= tr (A^{n/m} B)^m                     (implies the OQP 40 lower bound by Araki-Lieb-Thirring)
  mode 'pinch2':  p_{n,m}(A,B) >= max(Tr A^n E_A(B)^m, Tr E_B(A)^n B^m) >= tr exp(n log A + m log B)?
                  (minimises log max(pinched) - log L: negative means both pinched bounds fall below L)

Usage: python oqp40_aux.py mode d n m [batch] [steps] [seed]"""
import sys
from math import comb

import torch

mode = sys.argv[1]
d, n, m = (int(v) for v in sys.argv[2:5])
batch = int(sys.argv[5]) if len(sys.argv) > 5 else 256
steps = int(sys.argv[6]) if len(sys.argv) > 6 else 2000
seed = int(sys.argv[7]) if len(sys.argv) > 7 else 0
torch.manual_seed(seed)
dev = "cuda" if torch.cuda.is_available() else "cpu"
cdt = torch.complex128


def herm(X):
    return (X + X.conj().transpose(-1, -2)) / 2


def tr(X):
    return torch.diagonal(X, dim1=-2, dim2=-1).sum(-1).real


def word_average(A, B, n, m):
    I = torch.eye(d, dtype=cdt, device=dev).expand_as(A)
    coeffs = [I]
    for _ in range(n + m):
        new = [None] * (len(coeffs) + 1)
        for j, C in enumerate(coeffs):
            CA, CB = C @ A, C @ B
            new[j] = CA if new[j] is None else new[j] + CA
            new[j + 1] = CB
        coeffs = new
    return tr(coeffs[m]) / comb(n + m, n)


def fpow(H, a):
    w, V = torch.linalg.eigh(H)
    return (V * torch.exp(a * w).to(cdt)[..., None, :]) @ V.conj().transpose(-1, -2)


def pinch_power(H_ref, X, power):
    """Tr-ready matrix E_{ref}(X)^power where E is the pinching onto eigenvectors of H_ref (generic: simple spectrum)."""
    w, V = torch.linalg.eigh(H_ref)
    Xr = V.conj().transpose(-1, -2) @ X @ V
    diag = torch.diagonal(Xr, dim1=-2, dim2=-1).real
    return diag ** power, w


def f(H1, H2):
    A, B = fpow(H1, 1.0), fpow(H2, 1.0)
    if mode == "alt":
        lhs = word_average(A, B, n, n)
        rhs = tr(torch.linalg.matrix_power(A @ B, n))
    elif mode == "refine":
        lhs = word_average(A, B, n, m)
        rhs = word_average(fpow(H1, 0.5), fpow(H2, 0.5), 2 * n, 2 * m)
    elif mode == "frac":
        lhs = word_average(A, B, n, m)
        S = fpow(H1, n / (2 * m))
        rhs = tr(torch.linalg.matrix_power(S @ B @ S, m))
    elif mode == "pinch2":
        bm, wa = pinch_power(H1, B, m)                  # E_A(B)^m diagonal in A's eigenbasis
        t1 = (torch.exp(n * wa) * bm).sum(-1)
        an, wb = pinch_power(H2, A, n)
        t2 = (torch.exp(m * wb) * an).sum(-1)
        lhs = torch.maximum(t1, t2)
        rhs = tr(torch.linalg.matrix_exp(n * H1 + m * H2))
    return torch.log(lhs) - torch.log(rhs)


scales = torch.tensor([0.3, 1.0, 2.5, 5.0], dtype=torch.float64, device=dev)[torch.randint(0, 4, (batch,))]
X1 = (torch.randn(batch, d, d, dtype=cdt, device=dev) * scales[:, None, None]).requires_grad_(True)
X2 = (torch.randn(batch, d, d, dtype=cdt, device=dev) * scales[:, None, None]).requires_grad_(True)
opt = torch.optim.Adam([X1, X2], lr=0.02)
best = float("inf")
for it in range(steps):
    opt.zero_grad()
    val = f(herm(X1), herm(X2))
    bad = ~torch.isfinite(val)
    torch.where(bad, torch.zeros_like(val), val).sum().backward()
    opt.step()
    with torch.no_grad():
        for X in (X1, X2):
            t = torch.diagonal(herm(X), dim1=-2, dim2=-1).sum(-1).real / d
            X -= t[:, None, None] * torch.eye(d, dtype=cdt, device=dev)
            nrm = torch.linalg.matrix_norm(herm(X), ord=2)
            X *= torch.clamp(12.0 / nrm, max=1.0)[:, None, None]
    cur = torch.where(bad, torch.full_like(val, float("inf")), val).min().item()
    best = min(best, cur)
print(f"{mode} d={d} (n,m)=({n},{m}): min log-ratio {best:+.4e}", flush=True)
if best < -1e-8:
    with torch.no_grad():
        val = f(herm(X1), herm(X2))
        val = torch.where(torch.isfinite(val), val, torch.full_like(val, float("inf")))
        i = int(torch.argmin(val))
        torch.set_printoptions(precision=6, linewidth=200)
        print("  H1 =", herm(X1)[i].cpu(), "\n  H2 =", herm(X2)[i].cpu())
