"""Driver for region A' (Taylor models, regionA2.analyse_box).

A' is given as a list of pieces (th_a, th_b, s1, d1, rt):  {theta in [th_a, th_b], 0 <= s <= s1, |x - y| <= d1},
covered by boxes  [theta-interval of half-width rt] x [closed grid squares of half-width R0 = 0.25 centred on (0.5 Z)^2]
that meet the piece.  Every box must be accepted (each sub-box: H > 0 or d/ds H > 0); a failing box is split
(theta-halves, then quarter squares) up to depth 3.
Usage: python regionA_run.py OUT.json 'PIECES_JSON' [job k of n]
"""
import sys
import json
import math
import time
import regionA2 as A

R0 = 0.25


def squares_for_piece(s1, d1):
    out = []
    for i in range(-12, 13):
        for j in range(-12, 13):
            x0, y0 = 0.5 * i, 0.5 * j
            # closed square meets closed region {0 <= s <= s1, |d| <= d1}?  (convex: test via s- and d-ranges and
            # the exact intersection test by linear programming on corners is not needed: the region is the
            # intersection of the strips 0<=s<=s1 and |d|<=d1, and the square is the intersection of two strips;
            # we use the sufficient-and-necessary 2D test by sampling the boundary of the square.)
            smin, smax = x0 + y0 - 2 * R0, x0 + y0 + 2 * R0
            dmin, dmax = x0 - y0 - 2 * R0, x0 - y0 + 2 * R0
            if smax < 0 or smin > s1 or dmax < -d1 or dmin > d1:
                continue
            # the square in (s,d) coordinates is a diamond |s - s0| + |d - d0| <= 2 R0; it meets the rectangle
            # [0, s1] x [-d1, d1] iff the l1-distance from (s0, d0) to the rectangle is <= 2 R0
            s0, d0 = x0 + y0, x0 - y0
            ds = max(0.0, -s0, s0 - s1)
            dd = max(0.0, -d1 - d0, d0 - d1)
            if ds + dd <= 2 * R0 + 1e-12:
                out.append((x0, y0))
    return out


def choose_rho(c, r, cands=(1.2, 1.0, 0.9, 0.8, 0.7, 0.6, 0.5)):
    for rp in cands:
        if rp < 2.4 * r:
            continue
        if c != 0 and abs(abs(c) - rp) < 0.25:
            continue
        if c != 0 and abs(abs(c) - rp / 3) < 0.03:
            continue
        yield rp


def run_box(th0, rt, x0, y0, r, depth=0, log=None):
    """Try to certify the box; returns list of result dicts (one per accepted leaf) or raises on final failure."""
    best = None
    for rpx in choose_rho(x0, r):
        for rpy in choose_rho(y0, r):
            for fac in (3.0, 2.5, 2.0):
                rpt = fac * rt
                ok, info = A.analytic_check(th0, x0, y0, [rpt, rpx, rpy])
                if not ok:
                    continue
                # theta half-width enlarged by a relative 2^-20 so that neighbouring theta-boxes overlap
                # (box centres are floating-point numbers); x, y grids are exact dyadics.
                res = A.analyse_box(th0, x0, y0, rt * (1 + 2.0 ** -20), r, [rpt, rpx, rpy], [12, 16, 16], [8, 24, 24], 11, 15)
                res.update({'th0': th0, 'rt': rt, 'x0': x0, 'y0': y0, 'r': r, 'rp': [rpt, rpx, rpy]})
                if res.get('ok'):
                    return [res]
                best = res
                break  # analytic ok but certification failed: try other radii only via splitting
            if best is not None:
                break
        if best is not None:
            break
    if depth >= 3:
        raise RuntimeError(f"box failed: th0={th0} rt={rt} x0={x0} y0={y0} r={r} last={best}")
    out = []
    if best is None or rt > 0.004:
        # split theta
        for t in (th0 - rt / 2, th0 + rt / 2):
            out += run_box(t, rt / 2, x0, y0, r, depth + 1, log)
    else:
        for dx in (-r / 2, r / 2):
            for dy in (-r / 2, r / 2):
                if (x0 + dx + r / 2) + (y0 + dy + r / 2) < 0:
                    continue
                out += run_box(th0, rt, x0 + dx, y0 + dy, r / 2, depth + 1, log)
    return out


if __name__ == '__main__':
    out = sys.argv[1]
    pieces = json.loads(sys.argv[2])
    job, njobs = (int(sys.argv[3]), int(sys.argv[4])) if len(sys.argv) > 4 else (0, 1)
    boxes = []
    for (ta, tb, s1, d1, rt) in pieces:
        nt = int(round((tb - ta) / (2 * rt)))
        sq = squares_for_piece(s1, d1)
        for it in range(nt):
            th0 = ta + (2 * it + 1) * rt
            for (x0, y0) in sq:
                boxes.append((th0, rt, x0, y0))
    boxes = boxes[job::njobs]
    t0 = time.time()
    results = []
    for k, (th0, rt, x0, y0) in enumerate(boxes):
        res = run_box(th0, rt, x0, y0, R0)
        results += res
        print(f"[{k+1}/{len(boxes)}] th0={th0:.4f} x0={x0} y0={y0}: leaves={len(res)} "
              f"errS={max(r['errS'] for r in res):.2e} M={max(r['M'] for r in res):.1f} t={time.time()-t0:.0f}s", flush=True)
        json.dump({'pieces': pieces, 'job': [job, njobs], 'results': results}, open(out, 'w'))
    print(f"DONE: {len(boxes)} boxes, {len(results)} certified leaves, {time.time()-t0:.0f}s", flush=True)
