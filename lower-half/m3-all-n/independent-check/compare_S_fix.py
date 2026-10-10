"""Effect of the S_of correction on accepted boxes of the mixed3 runs (C2 d-strips, C1 lo2).
For each box: the lower bounds lows_k = L_k(c) - |..| r computed by tb_bb.check_box (--dual) with the original
S_of and with the corrected one (patch_S.py).  A box whose corrected lower bound is <= 0 was accepted only
because of the missing eps^2 terms.
Usage: python compare_S_fix.py [random N seed]
"""
import os
import sys
import random
from fractions import Fraction as Fr
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
import tb_arb as T
import tb_bb as BB
import patch_S

BB.DUAL = True
form = T.logF_mixed3

# worst boxes reported in the logs (a0, a1, d0, d1, e0, e1)
boxes = [
    (Fr(97, 4) + Fr(7, 32), Fr(49, 2), Fr(33, 16), Fr(17, 8), Fr(0), Fr(1, 74)),            # dstrip_23_28 L3 worst
    (Fr(619, 16), Fr(155, 4), Fr(21, 16), Fr(11, 8), Fr(1, 74), Fr(1, 37)),                   # dstrip_33_48 L3 worst
    (Fr(52), Fr(833, 16), Fr(41, 16), Fr(21, 8), Fr(0), Fr(1, 148)),                           # dstrip_48_64 L3 worst
    (Fr(1483, 32), Fr(371, 8), Fr(51, 16), Fr(13, 4), Fr(1, 74), Fr(3, 148)),                  # lo2_40_64 L3 worst
    (Fr(289, 16), Fr(579, 32), Fr(27, 8), Fr(55, 16), Fr(1, 74), Fr(3, 148)),                 # lo2_16_40 L3 worst
    (Fr(997, 32), Fr(499, 16), Fr(2), Fr(33, 16), Fr(0), Fr(1, 74)),                           # dstrip_28_33 L3 worst
    (Fr(97, 32), Fr(243, 16), Fr(17, 8), Fr(35, 16), Fr(1, 74), Fr(1, 37)),                    # dstrip_13_18 L3 worst
    (Fr(147, 8), Fr(589, 32), Fr(33, 16), Fr(17, 8), Fr(1, 74), Fr(1, 37)),                    # dstrip_18_23 L3 worst
    (Fr(117, 16), Fr(59, 8), Fr(9, 4), Fr(19, 8), Fr(0), Fr(1, 296)),                          # dstrip_3_8 L3 worst
    (Fr(97, 8), Fr(389, 32), Fr(37, 16), Fr(19, 8), Fr(0), Fr(1, 74)),                         # dstrip_8_13 L3 worst
]
# fix the first entry (15.15625 .. 15.1875 is dstrip_13_18; entry 7 above is a placeholder), use the exact logged boxes:
boxes[6] = (Fr(485, 32), Fr(243, 16), Fr(17, 8), Fr(35, 16), Fr(1, 74), Fr(1, 37))


def lows_of(box, fixed):
    if fixed:
        patch_S.install()
    else:
        patch_S.uninstall()
    try:
        lows, contrib, Lc = BB.check_box(form, *box)
        return [float(l.lower()) for l in lows], [float(x.mid()) for x in Lc], contrib
    except (T.NotPositive, ValueError, ZeroDivisionError) as ex:
        return None, None, str(ex)[:60]


def show(box):
    lo0, Lc0, c0 = lows_of(box, False)
    lo1, Lc1, c1 = lows_of(box, True)
    fb = tuple(float(x) for x in box)
    print(f"box a=[{fb[0]:.6g},{fb[1]:.6g}] d=[{fb[2]:.6g},{fb[3]:.6g}] eps=[{fb[4]:.5g},{fb[5]:.5g}]")
    print(f"   original  lows = {lo0}  eps-contrib = {None if c0 is None or isinstance(c0, str) else [round(c[2], 9) for c in c0]}")
    print(f"   corrected lows = {lo1}  eps-contrib = {None if c1 is None or isinstance(c1, str) else [round(c[2], 9) for c in c1]}")
    if lo0 is not None and lo1 is not None:
        flips = [k + 1 for k in range(3) if lo0[k] > 0 >= lo1[k]]
        if flips:
            print(f"   *** accepted with the original S_of, NOT with the corrected one (L{flips})")
        return lo0, lo1
    return lo0, lo1


if __name__ == '__main__':
    nflip = 0
    for b in boxes:
        lo0, lo1 = show(b)
        if lo0 and lo1 and any(lo0[k] > 0 >= lo1[k] for k in range(3)):
            nflip += 1
    if len(sys.argv) > 2 and sys.argv[1] == 'random':
        N = int(sys.argv[2])
        rnd = random.Random(int(sys.argv[3]) if len(sys.argv) > 3 else 1)
        worst_change = 0.0
        for i in range(N):
            # random boxes of the sizes seen in the logs
            wa = Fr(1, rnd.choice([16, 32, 64]))
            wd = Fr(1, rnd.choice([16, 32]))
            ne = rnd.choice([2, 4, 8])
            a0 = Fr(rnd.randrange(3 * 64, 64 * 64), 64)
            d0 = Fr(rnd.randrange(0, int(3 / wd))) * wd
            k = rnd.randrange(ne)
            box = (a0, a0 + wa, d0, d0 + wd, Fr(k, 37 * ne), Fr(k + 1, 37 * ne))
            lo0, lo1 = show(box)
            if lo0 and lo1:
                worst_change = max(worst_change, max(lo0[k] - lo1[k] for k in range(3)))
                if any(lo0[k] > 0 >= lo1[k] for k in range(3)):
                    nflip += 1
        print("largest decrease of a lower bound (original - corrected):", worst_change)
    print("boxes accepted only with the original S_of:", nflip)
