"""Polynomial rule search, memory-lean cutting-plane version (native Clarabel, no cvxpy).
Same mathematics as polyrule_null.py: endpoint equalities eliminated by z = z_p + N w; PSD of the SCALED matrix
(T0 basis with s^{o/2} scaling for s <= 1/2, T1 basis with u^{o1/2} scaling for u = 1-s <= 1/2) imposed at sample
points; samples are added where a fine-grid check finds the margin violated.
Usage: python polyrule_cp.py n qd out.npz"""
import os
import sys
import time
from math import comb

import numpy as np
import scipy.sparse as sps
import clarabel

from polyrule import Setup

n, qd, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
S = Setup(n, qd, 0, n * qd)
E = S.E
m = len(E)
nv = len(S.var)
N = S.N
D = N
t_start = time.time()
print(f"n={n} qd={qd} m={m} nv={nv} D={D}", flush=True)

C0 = np.zeros((D + 1, m, m))
Cv = np.zeros((D + 1, m, m, nv))
for ii, i in enumerate(E):
    for jj, j in enumerate(E):
        if jj < ii:
            continue
        ij = (i, j)
        for (a, b) in S.pairs_by_sum.get(N - i - j, []):
            key = ((a, b), ij)
            for pp in ([a, b] if a != b else [a]):
                for (r_, c_) in {(ii, jj), (jj, ii)}:
                    if key in S.fixed:
                        C0[pp, r_, c_] += S.fixed[key]
                    elif key in S.vidx:
                        Cv[pp, r_, c_, S.vidx[key]] += 1.0
                    else:
                        C0[pp, r_, c_] += 2 * S.kappa((a, b), ij)
                        Cv[pp, r_, c_, S.vidx[(ij, (a, b))]] -= 1.0


def basis_with(vecs):
    T = list(vecs)
    for c in range(m):
        if len(T) == m:
            break
        cand = np.eye(m)[c]
        if np.linalg.matrix_rank(np.column_stack(T + [cand]), tol=1e-9) > len(T):
            T.append(cand)
    return np.column_stack(T)


kv = []
for t in range(m):
    i = E[t]
    if 4 * i < N and i % qd != 0:
        kv.append(np.eye(m)[t])
    if 4 * i < N and i % qd == 0 and i > 0:
        kv.append(np.eye(m)[t] - np.eye(m)[0])
T0 = basis_with(kv)
W1 = [np.ones(m)]
if qd % 2 == 0:
    W1 = [np.array([1.0 - (E[t] % 2) for t in range(m)]), np.array([float(E[t] % 2) for t in range(m)])]
T1 = basis_with(W1)
o1 = [2] * len(W1) + [0] * (m - len(W1))

Bin = np.array([[comb(K, k) * (-1) ** k if K >= k else 0 for K in range(D + 1)] for k in range(D + 1)], float)
A0c = np.stack([T0.T @ C0[k] @ T0 for k in range(D + 1)])
A0v = np.stack([np.einsum('ai,ijv,jb->abv', T0.T, Cv[k], T0, optimize=True) for k in range(D + 1)])
Cu0 = np.tensordot(Bin, C0, axes=1)
A1c = np.stack([T1.T @ Cu0[k] @ T1 for k in range(D + 1)])
A1v = np.stack([np.einsum('ai,ijv,jb->abv', T1.T, np.tensordot(Bin[k], Cv, axes=1), T1, optimize=True)
                for k in range(D + 1)])
del Cu0
orders = []
for a in range(m):
    o = D + 1
    for k in range(D + 1):
        if abs(A0c[k, a, a]) > 1e-14 or np.abs(A0v[k, a, a]).max() > 1e-14:
            o = k
            break
    orders.append(o)
print("s=0 orders", orders, flush=True)

rows, rhs = [], []
for a in range(m):
    for b in range(a, m):
        for k in range(D + 1):
            if k < (orders[a] + orders[b]) / 2:
                if np.abs(A0v[k, a, b]).max() > 1e-14:
                    rows.append(A0v[k, a, b]); rhs.append(-A0c[k, a, b])
                elif abs(A0c[k, a, b]) > 1e-14:
                    print("INCONSISTENT at s=0"); sys.exit(1)
for a in range(len(W1)):
    for b in range(m):
        if np.abs(A1v[0, a, b]).max() > 1e-14:
            rows.append(A1v[0, a, b]); rhs.append(-A1c[0, a, b])
        elif abs(A1c[0, a, b]) > 1e-14:
            print("INCONSISTENT at s=1"); sys.exit(1)
PARITY = os.environ.get("PARITY", "1") == "1"
if PARITY:
    # Z2 symmetry gamma -> (-1)^{a+b} gamma maps rules to rules (LOG.md); averaging lets us take gamma = 0 on all
    # classes with a + b odd.  Then C(x,y) is block diagonal (even / odd exponents).
    for v, (p, q_) in enumerate(S.var):
        if (p[0] + p[1]) % 2 == 1:
            e_ = np.zeros(nv); e_[v] = 1.0
            rows.append(e_); rhs.append(0.0)
Aeq, beq = np.array(rows), np.array(rhs)
_, sv, Vt = np.linalg.svd(Aeq, full_matrices=True)
rank = int(np.sum(sv > 1e-10 * max(1.0, sv.max())))
zp = np.linalg.lstsq(Aeq, beq, rcond=None)[0]
Nsp = Vt[rank:].T
dim = Nsp.shape[1]
print(f"{len(rows)} equalities, rank {rank}, residual {np.abs(Aeq @ zp - beq).max():.1e}; free dim {dim}", flush=True)
# reduced coefficient tensors: constant part (with z_p) and the w-part
A0z = A0c + np.tensordot(A0v, zp, axes=1)
A0w = np.tensordot(A0v, Nsp, axes=1)
A1z = A1c + np.tensordot(A1v, zp, axes=1)
A1w = np.tensordot(A1v, Nsp, axes=1)
del A0v, A1v, Cv
H0 = (np.array(orders)[:, None] + np.array(orders)[None, :]) / 2.0
H1 = (np.array(o1)[:, None] + np.array(o1)[None, :]) / 2.0


def weights(H, x):
    """W[k,a,b] = x^(k - H_ab) for k >= H_ab, else 0."""
    K = np.arange(D + 1)[:, None, None]
    P = K - H[None]
    with np.errstate(divide='ignore', invalid='ignore'):
        W = np.where(P >= -1e-12, np.where(P < 1e-12, 1.0, (x ** np.maximum(P, 0)) if x > 0 else 0.0), 0.0)
    return W


def scaled(side, x):
    if side == 0:
        W = weights(H0, x)
        return np.einsum('kab,kab->ab', W, A0z), np.einsum('kab,kabd->abd', W, A0w)
    W = weights(H1, x)
    return np.einsum('kab,kab->ab', W, A1z), np.einsum('kab,kabd->abd', W, A1w)


def col_parity(T):
    par = []
    for a in range(m):
        nz = np.nonzero(np.abs(T[:, a]) > 1e-12)[0]
        ps = {E[t] % 2 for t in nz}
        par.append(ps.pop() if len(ps) == 1 else -1)
    return par


if PARITY:
    groups = {0: [], 1: []}
    for side, T in ((0, T0), (1, T1)):
        par = col_parity(T)
        assert -1 not in par
        groups[side] = [[a for a in range(m) if par[a] == 0], [a for a in range(m) if par[a] == 1]]
else:
    groups = {0: [list(range(m))], 1: [list(range(m))]}
print("PSD blocks per sample:", [len(g) for g in groups[0]], flush=True)


def svec_parts(idx):
    iu = [(idx[i], idx[j]) for j in range(len(idx)) for i in range(j + 1)]
    sc = np.array([1.0 if i == j else np.sqrt(2) for (i, j) in iu])
    return np.array([i for i, j in iu]), np.array([j for i, j in iu]), sc


SV = {side: [svec_parts(g) for g in groups[side] if g] for side in (0, 1)}


REL = {}          # (side, x) -> reference diagonal for a relative margin (RELMARGIN=1)


def block(side, x):
    Mc, Mw = scaled(side, x)
    Mc = (Mc + Mc.T) / 2
    Mw = (Mw + Mw.transpose(1, 0, 2)) / 2
    out = []
    dref = REL.get((side, x))
    for (ii_, jj_, sc) in SV[side]:
        bvec = sc * Mc[ii_, jj_]
        Aw = -(sc[:, None] * Mw[ii_, jj_, :])
        Alam = sc * (ii_ == jj_).astype(float)
        if dref is not None:
            Alam = Alam * dref[ii_]
        out.append((np.column_stack([Aw, Alam]), bvec, int(round((np.sqrt(8 * len(ii_) + 1) - 1) / 2))))
    return out


def solve(samples, lam_floor=None):
    """lam_floor None: maximise lam.  Otherwise minimise |w|^2 subject to lam >= lam_floor (regularised)."""
    blocks_A, blocks_b, cones = [], [], []
    # box |w| <= WB and lam <= 10 as nonnegative cone rows
    WB = 1e4
    Abox = np.zeros((2 * dim + 1, dim + 1))
    bbox = np.zeros(2 * dim + 1)
    Abox[:dim, :dim] = np.eye(dim); bbox[:dim] = WB
    Abox[dim:2 * dim, :dim] = -np.eye(dim); bbox[dim:2 * dim] = WB
    Abox[2 * dim, dim] = 1.0; bbox[2 * dim] = 10.0
    blocks_A.append(Abox); blocks_b.append(bbox); cones.append(clarabel.NonnegativeConeT(2 * dim + 1))
    for side, x in samples:
        for A_, b_, sz in block(side, x):
            blocks_A.append(A_); blocks_b.append(b_); cones.append(clarabel.PSDTriangleConeT(sz))
    if lam_floor is not None:
        Af = np.zeros((1, dim + 1)); Af[0, dim] = -1.0          # s = lam - lam_floor >= 0
        blocks_A.insert(1, Af); blocks_b.insert(1, np.array([-lam_floor])); cones.insert(1, clarabel.NonnegativeConeT(1))
    A = sps.csc_matrix(np.vstack(blocks_A))
    b = np.concatenate(blocks_b)
    q = np.zeros(dim + 1)
    if lam_floor is None:
        q[dim] = -1.0
        P = sps.csc_matrix((dim + 1, dim + 1))
    else:
        P = sps.diags(np.concatenate([np.ones(dim), [0.0]])).tocsc()
    st = clarabel.DefaultSettings(); st.verbose = os.environ.get("VERB", "0") == "1"
    if os.environ.get("DSM"):
        st.direct_solve_method = os.environ["DSM"]
    st.max_iter = 400
    sol = clarabel.DefaultSolver(P, q, A, b, cones, st).solve()
    return sol


def check(wv, lam, grid):
    """min eigenvalue of the scaled matrices on a grid; returns sorted list of (minev, side, x)."""
    res = []
    for side, x in grid:
        Mc, Mw = scaled(side, x)
        M = Mc + np.tensordot(Mw, wv, axes=1)
        M = (M + M.T) / 2
        if os.environ.get("RELMARGIN") == "1" and REL:
            dg = np.diag(M).copy()
            dg = np.maximum(dg, 1e-3 * max(dg.max(), 1e-300))
            dh = 1 / np.sqrt(dg)
            M = M * np.outer(dh, dh)
        ev = min(np.linalg.eigvalsh(M[np.ix_(g, g)])[0] for g in groups[side] if g)
        res.append((ev, side, x))
    res.sort()
    return res


NB = int(os.environ.get("NBASE", "40"))
base = np.unique(np.concatenate([[0.0], np.logspace(-6, np.log10(0.5), NB), np.linspace(0, 0.5, NB + 1)[1:]]))
samples = [(0, x) for x in base] + [(1, x) for x in base]
fine = np.unique(np.concatenate([[0.0], np.logspace(-8, np.log10(0.5), 400), np.linspace(0, 0.5, 1501)[1:]]))
grid = [(0, x) for x in fine] + [(1, x) for x in fine]
for it in range(int(os.environ.get("ITERS", "8"))):
    t0 = time.time()
    sol = solve(samples)
    x = np.array(sol.x)
    wv, lam = x[:dim], x[dim]
    if os.environ.get("REG", "0") == "1" and lam > 0:
        lam_star = lam
        sol2 = solve(samples, lam_floor=float(os.environ.get("REGFRAC", "0.5")) * lam_star)
        x2 = np.array(sol2.x)
        if x2.size and np.isfinite(x2).all():
            wv, lam = x2[:dim], x2[dim]
            print(f"   regularised: |w| {np.linalg.norm(wv):.3e} (max-lam solution |w| {np.linalg.norm(x[:dim]):.3e}), "
                  f"status {sol2.status}", flush=True)
    res = check(wv, lam, grid)
    worst = res[0][0]
    print(f"iter {it}: {len(samples)} samples, status {sol.status}, lam {lam:.4e}, fine-grid min eig {worst:.4e} "
          f"at side {res[0][1]} x={res[0][2]:.3e} ({time.time() - t0:.1f} s)", flush=True)
    if worst >= 0.25 * lam and lam > 0 and not (os.environ.get("RELMARGIN") == "1" and it == 0):
        break
    if os.environ.get("RELMARGIN") == "1" and not REL:
        # reference diagonals from the first solution (relative margin from now on)
        for (sd, xx) in set(samples):
            Mc_, Mw_ = scaled(sd, xx)
            dg = np.diag(Mc_ + np.tensordot(Mw_, wv, axes=1)).copy()
            dg = np.maximum(dg, 1e-3 * max(dg.max(), 1e-300))
            REL[(sd, xx)] = dg
        res = check(wv, lam, grid)
        lam = res[0][0] if res[0][0] > 0 else lam
    add = [(sd, xx) for (ev, sd, xx) in res if ev < 0.5 * lam][:int(os.environ.get("NADD", "60"))]
    samples += add
    if os.environ.get("RELMARGIN") == "1":
        for (sd, xx) in add:
            Mc_, Mw_ = scaled(sd, xx)
            dg = np.diag(Mc_ + np.tensordot(Mw_, wv, axes=1)).copy()
            REL[(sd, xx)] = np.maximum(dg, 1e-3 * max(dg.max(), 1e-300))
z = zp + Nsp @ wv
np.savez(out, z=z, n=n, qd=qd, lam=lam, orders=np.array(orders))
print(f"saved {out}; equality residual {np.abs(Aeq @ z - beq).max():.1e}; total {time.time() - t_start:.1f} s",
      flush=True)
