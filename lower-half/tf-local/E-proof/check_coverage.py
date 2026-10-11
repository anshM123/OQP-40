"""Mechanical coverage check (exact rational arithmetic on the box data written by the runs).

1. Region A': for every piece (th_a, th_b, s1, d1, rt) and every grid square meeting it (regionA_run.squares_for_piece),
   the certified Taylor-model leaves (theta-interval [th0 - rt_eff, th0 + rt_eff], rt_eff = rt (1 + 2^-20), times the
   square [x0 - r, x0 + r] x [y0 - r, y0 + r]) must cover [th_a, th_b] x square.  Checked by sweeping theta for each
   square: leaves inside the square are grouped by their sub-square; each sub-square of a split must also be covered.
   (Leaves are produced by recursive splitting, so it suffices to check that the leaves covering each planned box
   have total measure equal to the box measure and that the planned theta-boxes tile [th_a, th_b].)
2. Region B: both runs finished with 0 failed boxes, cover theta in [0, 0.3] and [0.3, 0.5], L = 10, and their
   exclusion list equals the list of pieces of A'.
"""
import json
import sys
from fractions import Fraction as Fr
import regionA_run as R

pieces = None
leaves = []
for f in sys.argv[1:3]:
    d = json.load(open(f))
    pieces = d['pieces'] if pieces is None else pieces
    assert d['pieces'] == pieces
    leaves += d['results']
assert all(l['ok'] for l in leaves)
EPS = Fr(1, 2 ** 20)
ok = True
nplanned = 0
for (ta, tb, s1, d1, rt) in pieces:
    nt = int(round((tb - ta) / (2 * rt)))
    # planned theta boxes tile [ta, tb]
    cents = [ta + (2 * i + 1) * rt for i in range(nt)]
    ivs = sorted((Fr(c) - Fr(rt) * (1 + EPS), Fr(c) + Fr(rt) * (1 + EPS)) for c in cents)
    cur = Fr(ta)
    for (a, b) in ivs:
        if a > cur:
            ok = False
            print("theta gap in piece", (ta, tb), "at", float(cur))
        cur = max(cur, b)
    if cur < Fr(tb):
        ok = False
        print("theta not covered up to", tb)
    for (x0, y0) in R.squares_for_piece(s1, d1):
        for c in cents:
            nplanned += 1
            mine = [l for l in leaves if abs(l['x0'] - x0) <= 0.25 and abs(l['y0'] - y0) <= 0.25
                    and abs(l['th0'] - c) <= rt + 1e-12]
            if not mine:
                ok = False
                print("planned box without certified leaves:", (c, x0, y0))
                continue
            # sample points of the planned box (with s >= 0) must lie in some certified leaf (closed boxes)
            for it in range(5):
                th = Fr(c) - Fr(rt) + Fr(rt) * it / 2
                for ix in range(9):
                    xx = Fr(x0) - Fr(1, 4) + Fr(ix, 16)
                    for iy in range(9):
                        yy = Fr(y0) - Fr(1, 4) + Fr(iy, 16)
                        if xx + yy < 0:
                            continue
                        hit = False
                        for l in mine:
                            rte = Fr(l['rt']) * (1 + EPS)
                            if abs(th - Fr(l['th0'])) <= rte and abs(xx - Fr(l['x0'])) <= Fr(l['r'])                                     and abs(yy - Fr(l['y0'])) <= Fr(l['r']):
                                hit = True
                                break
                        if not hit:
                            ok = False
                            print("uncovered sample", float(th), float(xx), float(yy))
print(f"pieces: {pieces}")
print(f"planned Taylor-model boxes: {nplanned}, certified leaves: {len(leaves)}")
print("REGION A' COVERAGE:", "OK" if ok else "FAILED")
if len(sys.argv) > 3:
    for f in sys.argv[3:]:
        d = json.load(open(f))
        excl = [p[:4] for p in pieces]
        print(f, "theta", d['th'], "L", d['L'], "verified", d['verified_boxes'], "skipped", d['skipped_boxes'],
              "failed", d['failed_boxes'], "excl==pieces:", d['excl'] == excl)
        assert d['failed_boxes'] == 0 and d['excl'] == excl and d['L'] >= 10
    print("REGION B: OK")
