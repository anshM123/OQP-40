"""Region B: rigorous ball-arithmetic verification of H(theta, x, y) > 0 on boxes, by adaptive bisection.

For a box B = [th_lo, th_hi] x [x_lo, x_hi] x [y_lo, y_hi]:
  H = g - tm,  g is increasing in x and in y  =>  g >= g(x_lo, y_lo) on B   (point evaluation),
  tm <= upper end of an Arb enclosure of tm over B, by formula (I') [box off the axes] and/or (II'') [box with s > 0].
B is verified if g(x_lo, y_lo) > tm_upper.  Boxes contained in the exclusion region A' (handled by the Cauchy/Taylor
part, file regionA.py) or in {s < 0} are skipped.  Failing boxes are bisected down to a minimum size; boxes that
still fail are recorded.

Usage: python regionB.py TH_LO TH_HI L OUTFILE [AMODE]
"""
import sys
import time
import json
from flint import arb, ctx
import ecore as C

ctx.prec = 192
MAXBOX = 3000000


def ball(lo, hi):
    return arb.union(arb(lo), arb(hi))


def in_exclusion(th_lo, th_hi, x_lo, x_hi, y_lo, y_hi, excl):
    """True if every point of the box with s >= 0 lies in the exclusion region A' (union of the pieces).
    excl: list of (th_a, th_b, s1, d1): piece = {th in [th_a, th_b], 0 <= s <= s1, |x - y| <= d1}.
    Test: the pieces whose (s, d)-rectangle contains all four corners (with a 1e-9 margin) must have theta-intervals
    covering [th_lo, th_hi]."""
    if x_hi + y_hi < 0:
        return True
    ivs = []
    for (ta, tb, s1, d1) in excl:
        ok = True
        for xx in (x_lo, x_hi):
            for yy in (y_lo, y_hi):
                if xx + yy > s1 - 1e-9 or abs(xx - yy) > d1 - 1e-9:
                    ok = False
        if ok:
            ivs.append((ta, tb))
    if not ivs:
        return False
    ivs.sort()
    cur = th_lo
    for (ta, tb) in ivs:
        if ta > cur:
            break
        if tb > cur:
            cur = tb
        if cur >= th_hi:
            return True
    return cur >= th_hi


def verify(th_lo, th_hi, x_lo, x_hi, y_lo, y_hi):
    thB, xB, yB = ball(th_lo, th_hi), ball(x_lo, x_hi), ball(y_lo, y_hi)
    glo = C.g_box_lower(arb(x_lo), arb(y_lo))
    best = None
    if not (x_lo <= 0 <= x_hi) and not (y_lo <= 0 <= y_hi):
        t = C.tm_box_I(thB, xB, yB)
        if t.is_finite():
            best = t.upper()
    if x_lo + y_lo > 0:
        t = C.tm_box_II(thB, xB, yB)
        if t.is_finite():
            u = t.upper()
            best = u if best is None else (u if u < best else best)
    if best is None:
        return False, None
    margin = glo - best
    return bool(margin > 0), margin


def run(th_lo, th_hi, L, excl, min_w=(1 / 256, 1 / 64, 1 / 64), wts=(6.0, 1.0, 1.0), init=(0.05, 1.0, 1.0)):
    global MAXBOX
    stack = []
    nt = max(1, int(round((th_hi - th_lo) / init[0])))
    nx = int(round(2 * L / init[1]))
    for i in range(nt):
        a = th_lo if i == 0 else th_lo + (th_hi - th_lo) * i / nt
        b = th_hi if i == nt - 1 else th_lo + (th_hi - th_lo) * (i + 1) / nt
        for j in range(nx):
            xa = -L + 2 * L * j / nx
            xb = -L + 2 * L * (j + 1) / nx
            for k in range(nx):
                ya = -L + 2 * L * k / nx
                yb = -L + 2 * L * (k + 1) / nx
                stack.append((a, b, xa, xb, ya, yb))
    n_ver = n_skip = 0
    fails = []
    vol_ver = 0.0
    t0 = time.time()
    nproc = 0
    while stack:
        nproc += 1
        if nproc > MAXBOX:
            fails.append(('ABORT', len(stack)))
            break
        bx = stack.pop()
        if in_exclusion(*bx, excl):
            n_skip += 1
            continue
        ok, m = verify(*bx)
        if ok:
            n_ver += 1
            continue
        w = (bx[1] - bx[0], bx[3] - bx[2], bx[5] - bx[4])
        cand = [i for i in range(3) if w[i] > min_w[i] * 1.0000001]
        if not cand:
            fails.append(bx)
            continue
        i = max(cand, key=lambda j: w[j] * wts[j])
        lo, hi = bx[2 * i], bx[2 * i + 1]
        mid = (lo + hi) / 2
        b1 = list(bx); b2 = list(bx)
        b1[2 * i + 1] = mid
        b2[2 * i] = mid
        stack.append(tuple(b1)); stack.append(tuple(b2))
    return n_ver, n_skip, fails, time.time() - t0


if __name__ == '__main__':
    th_lo, th_hi, L = float(sys.argv[1]), float(sys.argv[2]), float(sys.argv[3])
    out = sys.argv[4]
    excl = json.loads(sys.argv[5]) if len(sys.argv) > 5 else []
    minw = tuple(json.loads(sys.argv[6])) if len(sys.argv) > 6 else (1 / 256, 1 / 64, 1 / 64)
    if len(sys.argv) > 7:
        MAXBOX = int(sys.argv[7])
    n_ver, n_skip, fails, dt = run(th_lo, th_hi, L, excl, min_w=minw)
    res = {'th': [th_lo, th_hi], 'L': L, 'excl': excl, 'verified_boxes': n_ver, 'skipped_boxes': n_skip,
           'failed_boxes': len(fails), 'fails': fails[:5000], 'seconds': dt, 'prec': ctx.prec}
    json.dump(res, open(out, 'w'))
    print(f"theta [{th_lo},{th_hi}] L={L}: verified {n_ver}, skipped {n_skip}, FAILED {len(fails)}, {dt:.1f}s", flush=True)
