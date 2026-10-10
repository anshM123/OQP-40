"""Probe (not part of the proof): widths of the centred-form enclosures on sample boxes for several eps slabs."""
import time
from flint import arb
import tb_arb as T


def box_bounds(a_lo, a_hi, d_lo, d_hi, e_lo, e_hi, form):
    eps = arb.union(arb(e_lo), arb(e_hi)) if e_lo != e_hi else arb(e_lo)
    cx = T.Ctx(eps)
    ac, dc = (a_lo + a_hi) / 2, (d_lo + d_hi) / 2
    ra, rd = (a_hi - a_lo) / 2, (d_hi - d_lo) / 2
    A = T.J.var(arb(ac), 0, T.MP)
    B = T.J.var(arb(ac) + arb(dc), 1, T.MP)
    Lc, _ = T.margins_from_logF(form(A, B, cx))
    Ab = arb.union(arb(a_lo), arb(a_hi))
    Db = arb.union(arb(d_lo), arb(d_hi))
    A = T.J.var(Ab, 0, T.MB)
    B = T.J.var(Ab + Db, 1, T.MB)
    L, gr = T.margins_from_logF(form(A, B, cx))
    out = []
    for k in range(3):
        ga, gb = gr[k]
        lo = Lc[k] + (ga + gb) * arb(0, ra) + gb * arb(0, rd)
        out.append(lo)
    return Lc, out


for (box, form) in [((60, 62, 38, 40), T.logF_nu2), ((60, 61, 38, 39), T.logF_nu2), ((8, 8.5, 20, 21), T.logF_nu2),
                    ((100, 104, 1, 1.25), T.logF_mixed2), ((20, 21, 3.5, 4), T.logF_nu2)]:
    for (e_lo, e_hi) in [(1 / 37, 1 / 37), (0, 0), (1 / 38, 1 / 37), (1 / 50, 1 / 37), (0, 1 / 37), (0, 1 / 200)]:
        t = time.time()
        Lc, out = box_bounds(*box, e_lo, e_hi, form)
        dt = time.time() - t
        print(box, f"eps [{e_lo:.4f},{e_hi:.4f}]", " | ".join(f"L{k+1} c=[{float(Lc[k].lower()):.5f},{float(Lc[k].upper()):.5f}] box_lo={float(out[k].lower()):.5f}" for k in range(3)), f"{dt*1000:.0f} ms")
