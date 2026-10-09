"""SDP for the m = 4 diagonal-share certificate (see m4core.py)."""
import numpy as np
import cvxpy as cp

from m4core import Ktable, pairs_of


def build(n, alpha, Kt=None):
    r = len(alpha)
    P = pairs_of(r)
    if Kt is None:
        Kt = Ktable(n, alpha)
    G = {D: cp.Variable((r, r), symmetric=True) for D in P}
    cons = []
    for (D, E), k in Kt.items():
        if D == E:
            cons.append(G[D][E[0], E[1]] == k)
        else:
            cons.append(G[D][E[0], E[1]] + G[E][D[0], D[1]] == 2 * k)
    return G, cons, Kt


def proj(D, r):
    M = np.eye(r)
    if D[0] == D[1]:
        M[D[0], D[0]] = 0.0
    return M


def solve(n, alpha, objective="margin", extra=None, solver="CLARABEL", verbose=False, scale=True, **kw):
    """objective: 'margin' (max t, G^D - t*proj >= 0), 'mintrace', 'maxtrace', 'logdet' (analytic-centre like),
    or a callable (G, t) -> cvxpy objective.  extra: callable (G) -> list of constraints."""
    r = len(alpha)
    alpha = np.asarray(alpha, float)
    Kt = Ktable(n, alpha)
    sc = max(abs(v) for v in Kt.values()) if scale else 1.0
    Kt_s = {c: v / sc for c, v in Kt.items()}
    G, cons, _ = build(n, alpha, Kt_s)
    P = list(G.keys())
    t = cp.Variable()
    if objective == "margin":
        cons += [G[D] - t * proj(D, r) >> 0 for D in P]
        obj = cp.Maximize(t)
        cons += [t <= 1]
    elif objective == "mintrace":
        cons += [G[D] >> 0 for D in P]
        obj = cp.Minimize(sum(cp.trace(G[D]) for D in P))
    elif objective == "maxtrace":
        cons += [G[D] >> 0 for D in P]
        obj = cp.Maximize(sum(cp.trace(G[D]) for D in P))
    elif objective == "logdet":
        # log det on the complement of the forced zero row
        terms = []
        for D in P:
            idx = [i for i in range(r) if not (D[0] == D[1] and i == D[0])]
            sub = G[D][idx, :][:, idx]
            terms.append(cp.log_det(sub))
            cons.append(G[D] >> 0)
        obj = cp.Maximize(sum(terms))
    else:
        cons += [G[D] >> 0 for D in P]
        obj = objective(G, t)
    if extra is not None:
        cons += extra(G)
    prob = cp.Problem(obj, cons)
    try:
        prob.solve(solver=solver, verbose=verbose, **kw)
    except Exception as e:  # pragma: no cover
        if verbose:
            print("solver failed:", e)
        prob.solve(solver="SCS", eps=1e-9, max_iters=200000, verbose=verbose)
    Gv = None
    if G[P[0]].value is not None:
        Gv = {D: G[D].value * sc for D in P}
    return prob.status, (t.value if t.value is not None else None), Gv, sc
