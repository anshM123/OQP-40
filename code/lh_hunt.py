"""Counterexample hunt for the lower half of OQP 40 at cases not yet proved:
    p_{n,m}(A,B) >= tr exp(n log A + m log B),   A = e^{H1}, B = e^{H2}.
Batched Adam (torch, complex128, GPU) on f = log p - log L, with three kinds of starts:
  generic   - random Hermitian H1, H2 at several scales;
  chalee    - Cha-Lee-like: A, B close to [[1,0,0],[0,x,-x],[0,-x,x]] / [[x,-x,0],[-x,x,0],[0,0,1]] (embedded in d)
              with x in [1e-4, 0.3] and small shifts, randomly rotated;
  spread    - one dominant eigenvalue per matrix and widely spread small ones (near-singular regime).
Every final point with f < -1e-9 is written to a candidates file for high-precision re-verification.
Usage: python lh_hunt.py d n m [batch] [steps] [seed]"""
import json
import sys
from math import comb

import torch

d, n, m = (int(v) for v in sys.argv[1:4])
batch = int(sys.argv[4]) if len(sys.argv) > 4 else 384
steps = int(sys.argv[5]) if len(sys.argv) > 5 else 2500
seed = int(sys.argv[6]) if len(sys.argv) > 6 else 0
torch.manual_seed(seed)
dev = "cuda" if torch.cuda.is_available() else "cpu"
cdt = torch.complex128
I = torch.eye(d, dtype=cdt, device=dev)


def herm(X):
    return (X + X.conj().transpose(-1, -2)) / 2


def word_average(A, B):
    coeffs = [I.expand_as(A)]
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


def logm_pd(M):
    w, V = torch.linalg.eigh(herm(M))
    return (V * torch.log(torch.clamp(w.real, min=1e-300)).to(cdt)[..., None, :]) @ V.conj().transpose(-1, -2)


def rand_unitary(k):
    Z = torch.randn(k, d, d, dtype=cdt, device=dev)
    Q, R = torch.linalg.qr(Z)
    return Q


def init_batch():
    k1, k2 = batch // 2, batch // 4
    k3 = batch - k1 - k2
    scales = torch.tensor([0.3, 1.0, 2.5, 5.0], dtype=torch.float64, device=dev)[torch.randint(0, 4, (k1,))]
    G1 = torch.randn(k1, d, d, dtype=cdt, device=dev) * scales[:, None, None]
    G2 = torch.randn(k1, d, d, dtype=cdt, device=dev) * scales[:, None, None]
    # Cha-Lee-like starts, embedded in the first three coordinates, small identity shift elsewhere
    x = 10 ** (-4 * torch.rand(k2, device=dev, dtype=torch.float64))
    sh = 10 ** (-1 - 4 * torch.rand(k2, device=dev, dtype=torch.float64))
    A = torch.zeros(k2, d, d, dtype=cdt, device=dev)
    B = torch.zeros(k2, d, d, dtype=cdt, device=dev)
    A[:, 0, 0] = 1
    A[:, 1, 1] = x; A[:, 2, 2] = x; A[:, 1, 2] = -x; A[:, 2, 1] = -x
    B[:, 0, 0] = x; B[:, 1, 1] = x; B[:, 0, 1] = -x; B[:, 1, 0] = -x; B[:, 2, 2] = 1
    for j in range(3, d):
        A[:, j, j] = x * torch.rand(k2, device=dev, dtype=torch.float64)
        B[:, j, j] = x * torch.rand(k2, device=dev, dtype=torch.float64)
    A = A + sh[:, None, None] * I
    B = B + sh[:, None, None] * I
    U = rand_unitary(k2)
    small = 0.05 * (torch.randn(k2, d, d, dtype=cdt, device=dev))
    C1 = logm_pd(U @ A @ U.conj().transpose(-1, -2)) + small
    C2 = logm_pd(U @ B @ U.conj().transpose(-1, -2)) + small.conj().transpose(-1, -2)
    # spread starts: random eigenbases, log-eigenvalues 0 and down to -16
    U1, U2 = rand_unitary(k3), rand_unitary(k3)
    e1 = -16 * torch.rand(k3, d, device=dev, dtype=torch.float64); e1[:, 0] = 0
    e2 = -16 * torch.rand(k3, d, device=dev, dtype=torch.float64); e2[:, 0] = 0
    S1 = (U1 * e1.to(cdt)[:, None, :]) @ U1.conj().transpose(-1, -2)
    S2 = (U2 * e2.to(cdt)[:, None, :]) @ U2.conj().transpose(-1, -2)
    return torch.cat([G1, C1, S1]), torch.cat([G2, C2, S2])


X1, X2 = init_batch()
X1.requires_grad_(True); X2.requires_grad_(True)
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
        for X in (X1, X2):
            tr = torch.diagonal(herm(X), dim1=-2, dim2=-1).sum(-1).real / d
            X -= tr[:, None, None] * I
            nrm = torch.linalg.matrix_norm(herm(X), ord=2)
            X *= torch.clamp(18.0 / nrm, max=1.0)[:, None, None]
    cur = torch.where(bad, torch.full_like(val, float("inf")), val).min().item()
    best = min(best, cur)
    if it % 500 == 0 or it == steps - 1:
        print(f"d={d} (n,m)=({n},{m}) step {it}: batch min {cur:+.3e}, best so far {best:+.3e}", flush=True)

with torch.no_grad():
    val, p, L = f(herm(X1), herm(X2))
    val = torch.where(torch.isfinite(val), val, torch.full_like(val, float("inf")))
    order = torch.argsort(val)
    i = int(order[0])
    print(f"FINAL d={d} (n,m)=({n},{m}): min log-ratio {val[i].item():+.6e}", flush=True)
    cands = [int(j) for j in order[:5] if val[int(j)].item() < -1e-9]
    if cands:
        out = [{"d": d, "n": n, "m": m, "f": val[j].item(),
                "H1": [[[z.real, z.imag] for z in row] for row in herm(X1)[j].cpu().tolist()],
                "H2": [[[z.real, z.imag] for z in row] for row in herm(X2)[j].cpu().tolist()]} for j in cands]
        fn = f"candidates_d{d}_n{n}_m{m}_s{seed}.json"
        json.dump(out, open(fn, "w"))
        print(f"  {len(cands)} candidate(s) with f < -1e-9 written to {fn}", flush=True)
