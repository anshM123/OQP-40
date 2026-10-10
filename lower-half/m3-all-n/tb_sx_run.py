"""Theorem B, the strip 0 <= a <= 3: adaptive box verification with tb_sx.py (coordinates (a, b), all eps in
[0, 1/37]).  A box is accepted when, on the whole box,
  M1 = a L1 = 1 + a Ghat_a > 0,   L2 > 0 (M2 = 1 - b Ghat_b > 0 or N2 = 1/b - Ghat_b > 0),
  L3 > 0 (M3 = 1 - b Ghat_b + a Ghat_a - a b (Ghat_ab + Ghat_a Ghat_b) > 0 or N3 = N2 - a (Ghat_ab + Ghat_a (Ghat_b - 1/b)) > 0),
  and X = E^R/a^2 > 0 (F = (a/b) e^{Ghat}),
otherwise it is bisected in the direction (b, eps or a) with the largest contribution to the enclosure widths.
Usage: python tb_sx_run.py REGION > log, REGION one of
  corner                      0 <= a <= 1/4, 0 <= b <= 1/4 (corner chart: Taylor model at (0,0), shift by b),
  direct A0 A1 B0 DMAX WB NA NE   direct form, a-strips [x0,x1] of [A0,A1] (NA strips), b in [B0, x0 + DMAX], b-cells WB,
  nu A0 A1 DMIN B1 NA RB NE       nu form, a-strips [x0,x1] (NA strips), b in [x1 + DMIN, B1], b-cells of relative width 1/RB.
"""
import sys
import time
from fractions import Fraction as Fr
import tb_sx as S
from tb_sx import T

E37 = Fr(1, 37)
MIN_A = Fr(1, 2 ** 9)
MIN_B = Fr(1, 2 ** 13)
MIN_E = E37 / 2 ** 9


def check(box):
    form, corner, a0, a1, b0, b1, e0, e1, ke, J = box
    r = S.evaluate(form, 'ab', a0, a1, b0, b1, e0, e1, ke=ke, corner=corner, J=J)
    ok, out, contrib, g = S.conditions(r)
    return ok, out, contrib


def run(boxes, log, max_fail=20):
    t0 = time.time()
    stack = list(reversed(boxes))
    nbox, nfail, nsplit = 0, 0, 0
    worst = {}
    last = t0
    while stack:
        box = stack.pop()
        form, corner, a0, a1, b0, b1, e0, e1, ke, J = box
        try:
            ok, out, contrib = check(box)
        except (T.NotPositive, ValueError, ZeroDivisionError) as ex:
            ok, out, contrib = False, None, None
        if ok:
            nbox += 1
            vals = {'aL1': out['M1']}
            if 'N2' in out and out['N2'] > 0:
                vals['L2'] = out['N2']
            else:
                vals['bL2'] = out['M2']
            if 'N3' in out and out['N3'] > 0:
                vals['aL3'] = out['N3']
            else:
                vals['abL3'] = out['M3']
            for k, v in vals.items():
                lo = float(v.lower())
                if k not in worst or lo < worst[k][0]:
                    worst[k] = (lo, (float(a0), float(a1), float(b0), float(b1), float(e0), float(e1)))
            if time.time() - last > 60:
                last = time.time()
                log(f"  progress: {nbox} boxes, {nsplit} splits, stack {len(stack)}, {time.time() - t0:.0f} s, "
                    f"last a=[{float(a0):.4g},{float(a1):.4g}] b=[{float(b0):.5g},{float(b1):.5g}] e=[{float(e0):.4g},{float(e1):.4g}]")
            continue
        wa, wb, we = a1 - a0, b1 - b0, e1 - e0
        if contrib is None:
            # evaluation failed: split the relatively widest direction
            sizes = [float(wb) / max(float(b0), 1.0) * 8, float(we) * 37 * 4, float(wa) * 4]
        else:
            sizes = list(contrib)
        order = sorted(range(3), key=lambda i: -sizes[i])
        done = False
        for dim in order:
            if dim == 0 and wb >= 2 * MIN_B:
                m = (b0 + b1) / 2
                if corner:
                    # the corner box keeps b = 0 and a = 0; its upper b-half is an ordinary box
                    stack += [(form, False, a0, a1, m, b1, e0, e1, ke, J), (form, True, a0, a1, b0, m, e0, e1, ke, J)]
                else:
                    stack += [(form, corner, a0, a1, m, b1, e0, e1, ke, J), (form, corner, a0, a1, b0, m, e0, e1, ke, J)]
                done = True
            elif dim == 1 and we >= 2 * MIN_E:
                m = (e0 + e1) / 2
                stack += [(form, corner, a0, a1, b0, b1, m, e1, ke, J), (form, corner, a0, a1, b0, b1, e0, m, ke, J)]
                done = True
            elif dim == 2 and wa >= 2 * MIN_A:
                m = (a0 + a1) / 2
                if corner:
                    # points of the upper a-half with b >= a have b >= m: an ordinary box [m, a1] x [m, b1]
                    if m < b1:
                        stack.append((form, False, m, a1, m, b1, e0, e1, ke, J))
                    stack.append((form, True, a0, m, b0, b1, e0, e1, ke, J))
                else:
                    stack += [(form, corner, m, a1, b0, b1, e0, e1, ke, J), (form, corner, a0, m, b0, b1, e0, e1, ke, J)]
                done = True
            if done:
                break
        if done:
            nsplit += 1
            continue
        nfail += 1
        log(f"FAIL box a=[{a0},{a1}] b=[{b0},{b1}] e=[{e0},{e1}] corner={corner} out={out}")
        if nfail >= max_fail:
            break
    return nbox, nfail, nsplit, worst, time.time() - t0


def grid(form, a0, a1, na, blo, bhi, ne, wb=None, geometric=None, ke=2):
    """a-strips [x0, x1] of width (a1-a0)/na; for each strip b in [blo(x0, x1), bhi(x0, x1)], cut into cells of width
    wb or of relative width 1/geometric; eps-cells: ne (direct form) or max(ne, ceil(b/12)) (nu form)."""
    boxes = []
    for i in range(na):
        x0, x1 = a0 + (a1 - a0) * i / na, a0 + (a1 - a0) * (i + 1) / na
        b0, b1 = blo(x0, x1), bhi(x0, x1)
        bs = [b0]
        while bs[-1] < b1:
            nxt = bs[-1] + wb if wb else Fr(int(bs[-1] * (1 + Fr(1, geometric)) * 64) + 1, 64)
            bs.append(min(nxt, b1))
        for j in range(len(bs) - 1):
            y0, y1 = bs[j], bs[j + 1]
            if y1 <= x0:
                continue          # entirely below the diagonal b = a (not part of the region)
            nek = max(ne, -(-int(y1) // 12)) if geometric else ne
            for k in range(nek):
                boxes.append((form, False, x0, x1, y0, y1, E37 * k / nek, E37 * (k + 1) / nek, ke, 10))
    return boxes


if __name__ == '__main__':
    log = lambda s: print(s, flush=True)
    if '--box' in sys.argv:
        sys.argv.remove('--box')
        S.Tight.BOX = True
    reg = sys.argv[1]
    if reg == 'corner':
        boxes = [('direct', True, Fr(0), Fr(1, 4), Fr(0), Fr(1, 4), Fr(0), E37, 2, 10)]
        desc = "corner: a in [0, 1/4], b in [0, 1/4] (Taylor model at (0,0), b-order 10)"
    elif reg == 'direct':
        # direct form on a-strips [x0, x1], b in [B0, x0 + DMAX] (cells of width WB)
        A0, A1, B0, DMAX, WB = (Fr(x) for x in sys.argv[2:7])
        NA, NE = int(sys.argv[7]), int(sys.argv[8])
        boxes = grid('direct', A0, A1, NA, lambda x0, x1: B0, lambda x0, x1: x0 + DMAX, NE, wb=WB)
        desc = f"direct form: a in [{A0}, {A1}] (strips of width {(A1 - A0) / NA}), b in [{B0}, a_strip_lo + {DMAX}]"
    elif reg == 'nu':
        # nu form on a-strips [x0, x1], b in [x1 + DMIN, B1] (cells of relative width 1/RB)
        A0, A1, DMIN, B1 = (Fr(x) for x in sys.argv[2:6])
        NA, RB, NE = (int(x) for x in sys.argv[6:9])
        boxes = grid('nu', A0, A1, NA, lambda x0, x1: x1 + DMIN, lambda x0, x1: B1, NE, geometric=RB)
        desc = f"nu form: a in [{A0}, {A1}] (strips of width {(A1 - A0) / NA}), b in [a_strip_hi + {DMIN}, {B1}]"
    else:
        raise SystemExit('unknown region')
    log(f"strip verification (tb_sx): {desc}, all eps in [0, 1/37]; {len(boxes)} initial boxes; box tightening {S.Tight.BOX}")
    nbox, nfail, nsplit, worst, dt = run(boxes, log)
    log(f"boxes accepted: {nbox}, splits: {nsplit}, failures: {nfail}, time {dt:.1f} s")
    for k, (v, bx) in sorted(worst.items()):
        log(f"  certified min lower bound of {k}: {v:.6g} on box (a0,a1,b0,b1,e0,e1) = {bx}")
    log("RESULT: REGION VERIFIED" if nfail == 0 else "RESULT: FAILED")
