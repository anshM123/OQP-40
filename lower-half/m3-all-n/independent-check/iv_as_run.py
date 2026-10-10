"""Independent verifier, strip driver (0 <= a <= 3), own Taylor models in a (iv_as.py).
A box is accepted when, on the whole box, a L1 > 0, L2 > 0 (b L2 > 0 or L2 > 0), L3 > 0 (a b L3 > 0 or a L3 > 0) and
X > 0 (so F = (a/b) X e^{-(a+b)/2}/sqrt(S(-a) S(-b)) > 0); otherwise it is bisected (direction of the largest width
contribution).  All eps in [0, 1/37].
Usage: python iv_as_run.py corner
       python iv_as_run.py direct A0 A1 NA B0 DMAX WB NE          a-strips [x0,x1], b in [B0, x0 + DMAX], b-cells of width WB
       python iv_as_run.py nu A0 A1 NA DMIN B1 RB NE [box]        b in [x1 + DMIN, B1], geometric b-cells (ratio 1 + 1/RB)
"""
import sys
import time
from fractions import Fraction as Fr
import iv_as as AS
from iv_jet import NotPos

E37 = Fr(1, 37)
MIN_A, MIN_B, MIN_E = Fr(1, 2 ** 10), Fr(1, 2 ** 14), E37 / 2 ** 10


def run(boxes, log, max_fail=20):
    t0 = time.time()
    stack = list(reversed(boxes))
    nbox = nsplit = nfail = 0
    worst = {}
    last = t0
    while stack:
        box = stack.pop()
        form, corner, a0, a1, b0, b1, e0, e1 = box
        try:
            r = AS.evaluate(form, a0, a1, b0, b1, e0, e1, corner=corner)
            ok, out, contrib = AS.conditions_c(r)
        except (NotPos, ValueError, ZeroDivisionError):
            ok, out, contrib = False, None, None
        if ok:
            nbox += 1
            vals = {'aL1': out['aL1']}
            if 'L2' in out and out['L2'] > 0:
                vals['L2'] = out['L2']
            else:
                vals['bL2'] = out['bL2']
            if 'aL3' in out and out['aL3'] > 0:
                vals['aL3'] = out['aL3']
            else:
                vals['abL3'] = out['abL3']
            for k, v in vals.items():
                lo = float(v.lower())
                if k not in worst or lo < worst[k][0]:
                    worst[k] = (lo, tuple(float(x) for x in (a0, a1, b0, b1, e0, e1)))
            if time.time() - last > 120:
                last = time.time()
                log(f"  progress: {nbox} boxes, {nsplit} splits, stack {len(stack)}, {time.time() - t0:.0f} s, "
                    f"box a=[{float(a0):.4g},{float(a1):.4g}] b=[{float(b0):.5g},{float(b1):.5g}] e=[{float(e0):.4g},{float(e1):.4g}]")
            continue
        wa, wb, we = a1 - a0, b1 - b0, e1 - e0
        sizes = list(contrib) if contrib is not None else [float(wb) / max(float(b0), 1.0) * 8, float(we) * 37 * 4,
                                                          float(wa) * 4]
        order = sorted(range(3), key=lambda i: -sizes[i])
        done = False
        for dim in order:
            if dim == 0 and wb >= 2 * MIN_B:
                m = (b0 + b1) / 2
                if corner:
                    stack += [(form, False, a0, a1, m, b1, e0, e1), (form, True, a0, a1, b0, m, e0, e1)]
                else:
                    stack += [(form, False, a0, a1, m, b1, e0, e1), (form, False, a0, a1, b0, m, e0, e1)]
                done = True
            elif dim == 1 and we >= 2 * MIN_E:
                m = (e0 + e1) / 2
                stack += [(form, corner, a0, a1, b0, b1, m, e1), (form, corner, a0, a1, b0, b1, e0, m)]
                done = True
            elif dim == 2 and wa >= 2 * MIN_A:
                m = (a0 + a1) / 2
                if corner:
                    # upper a-half: the points with b >= a have b >= m (an ordinary box); lower half stays a corner box
                    if m < b1:
                        stack.append((form, False, m, a1, m, b1, e0, e1))
                    stack.append((form, True, a0, m, b0, b1, e0, e1))
                else:
                    stack += [(form, False, m, a1, b0, b1, e0, e1), (form, False, a0, m, b0, b1, e0, e1)]
                done = True
            if done:
                break
        if done:
            nsplit += 1
            continue
        nfail += 1
        log(f"FAIL box {form} corner={corner} a=[{a0},{a1}] b=[{b0},{b1}] e=[{e0},{e1}] "
            f"out={None if out is None else {k: str(v) for k, v in out.items()}}")
        if nfail >= max_fail:
            break
    return nbox, nsplit, nfail, worst, time.time() - t0


def grid(form, A0, A1, NA, blo, bhi, NE, wb=None, geometric=None):
    boxes = []
    for i in range(NA):
        x0, x1 = A0 + (A1 - A0) * i / NA, A0 + (A1 - A0) * (i + 1) / NA
        b0, b1 = blo(x0, x1), bhi(x0, x1)
        bs = [b0]
        while bs[-1] < b1:
            if wb:
                nxt = bs[-1] + wb
            else:
                nxt = Fr(int(bs[-1] * (1 + Fr(1, geometric)) * 64) + 1, 64)
            bs.append(min(nxt, b1))
        for j in range(len(bs) - 1):
            y0, y1 = bs[j], bs[j + 1]
            if y1 <= x0:
                continue                      # entirely below the diagonal b = a
            ne = max(NE, -(-int(y1) // 12)) if geometric else NE
            for k in range(ne):
                boxes.append((form, False, x0, x1, y0, y1, E37 * k / ne, E37 * (k + 1) / ne))
    return boxes


if __name__ == '__main__':
    log = lambda s: print(s, flush=True)
    args = sys.argv[1:]
    if 'box' in args:
        args.remove('box')
        AS.Ctl.BOX = True
    reg = args[0]
    if reg == 'corner':
        boxes = [('direct', True, Fr(0), Fr(1, 4), Fr(0), Fr(1, 4), Fr(0), E37)]
        desc = 'corner [0,1/4] x [0,1/4] (face and centre at b = 0, b-order 10)'
    elif reg == 'direct':
        A0, A1 = Fr(args[1]), Fr(args[2])
        NA = int(args[3])
        B0, DMAX, WB = Fr(args[4]), Fr(args[5]), Fr(args[6])
        NE = int(args[7])
        boxes = grid('direct', A0, A1, NA, lambda x0, x1: B0, lambda x0, x1: x0 + DMAX, NE, wb=WB)
        desc = f'direct form, a in [{A0},{A1}] ({NA} strips), b in [{B0}, x0 + {DMAX}], b-cells {WB}'
    elif reg == 'nu':
        A0, A1 = Fr(args[1]), Fr(args[2])
        NA = int(args[3])
        DMIN, B1 = Fr(args[4]), Fr(args[5])
        RB, NE = int(args[6]), int(args[7])
        boxes = grid('nu', A0, A1, NA, lambda x0, x1: x1 + DMIN, lambda x0, x1: B1, NE, geometric=RB)
        desc = f'nu form, a in [{A0},{A1}] ({NA} strips), b in [x1 + {DMIN}, {B1}], geometric b-cells 1/{RB}'
    elif reg == 'nuc':
        A0, A1 = Fr(args[1]), Fr(args[2])
        NA = int(args[3])
        B0, B1 = Fr(args[4]), Fr(args[5])
        RB, NE = int(args[6]), int(args[7])
        boxes = grid('nu', A0, A1, NA, lambda x0, x1: B0, lambda x0, x1: B1, NE, geometric=RB)
        desc = f'nu form, a in [{A0},{A1}] ({NA} strips), b in [{B0}, {B1}] for every strip, geometric b-cells 1/{RB}'
    else:
        raise SystemExit('region?')
    log(f"independent strip verifier (own a-Taylor models): {desc}; all eps in [0, 1/37]; {len(boxes)} initial boxes; "
        f"box Taylor models before univariate functions: {AS.Ctl.BOX}")
    nbox, nsplit, nfail, worst, dt = run(boxes, log)
    log(f"boxes accepted: {nbox}, splits: {nsplit}, failures: {nfail}, time {dt:.1f} s")
    for k, (v, bx) in sorted(worst.items()):
        log(f"  smallest certified lower bound of {k}: {v:.6g} on box (a0,a1,b0,b1,e0,e1) = {bx}")
    log("RESULT: REGION VERIFIED" if nfail == 0 else "RESULT: FAILED")
