"""Adversarial hunt against TF on the ray through (1, r): minimize rho*_L (K fixed) over pairs."""
import sys, time
import numpy as np
from scipy.linalg import expm
from tf_moment_sdp import moments
from tf_ratio_sdp import rho_star

def pair_from(params, d):
    # params: log-eigs of A (d), log-eigs of B (d), Hermitian generator of relative unitary (d*d reals)
    la, lb = params[:d], params[d:2 * d]
    g = params[2 * d:].reshape(d, d)
    H = np.triu(g, 1) + 1j * np.tril(g, -1).T
    H = H + H.conj().T + np.diag(np.diag(g))
    U = expm(1j * H)
    return np.diag(np.exp(la)).astype(complex), U @ np.diag(np.exp(lb)) @ U.conj().T

def rho(params, d, r, K):
    A, B = pair_from(params, d)
    M, Mk = moments(A, B, r, K)
    S = np.exp(params[:d].max() + r * params[d:2 * d].max())
    try:
        v = rho_star(M, Mk, S, K)
    except Exception:
        return np.inf
    return v if v is not None else np.inf

if __name__ == '__main__':
    seed, r, K, budget = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), float(sys.argv[4])
    rng = np.random.default_rng(seed)
    t0 = time.time(); best = (np.inf, None, None)
    n = 0
    while time.time() - t0 < budget:
        d = int(rng.integers(2, 6))
        sp = float(rng.choice([0.2, 0.5, 1.0, 2.0, 3.0]))
        gs = float(rng.choice([0.03, 0.1, 0.3, 1.0, 3.0]))
        params = np.concatenate([sp * rng.normal(size=2 * d), gs * rng.normal(size=d * d)])
        v = rho(params, d, r, K); n += 1
        if v < best[0]:
            best = (v, d, params)
            print(f"[{time.time()-t0:7.1f}s] sample {n}: new min rho* = {v:.7f} (d={d}, spread={sp}, gen={gs})", flush=True)
    # local descent from the best
    v, d, params = best
    step = 0.1
    for it in range(400):
        if time.time() - t0 > 2 * budget:
            break
        cand = params + step * rng.normal(size=params.size) * (rng.random(params.size) < 0.5)
        vc = rho(cand, d, r, K)
        if vc < v:
            v, params = vc, cand
            print(f"  descent it {it}: rho* = {v:.7f}", flush=True)
        else:
            step *= 0.98
    print(f"FINAL min rho* = {v:.7f} (d={d}); samples {n}")
    np.save(f"tf_hunt_best_r{r}_s{seed}.npy", np.concatenate([[d], params]))
