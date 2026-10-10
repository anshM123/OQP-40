"""Re-run of every tb_bb.py --dual mixed3 region (C2 d-strips and the C1 mixed part) with the corrected S_of
(patch_S.py: eps-Taylor coefficients of S up to the eps-order of the jets).  Same driver (tb_bb.run, unchanged),
same regions and initial grids as run_tb_guarded2.sh.  One log line block per region.
Usage: python rerun_mixed3_fixed.py [index ...]
"""
import os
import sys
import time
from fractions import Fraction as Fr
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
import tb_bb as BB
import patch_S

BB.DUAL = True
patch_S.install()

REGIONS = [
    (28, 33, 0, 3, 5, 6), (23, 28, 0, 3, 5, 6), (18, 23, 0, 3, 5, 6), (13, 18, 0, 3, 5, 6), (8, 13, 0, 3, 5, 6),
    (3, 8, 0, 3, 5, 6), (33, 48, 0, 3, 15, 6), (48, 64, 0, 3, 16, 6),
    (16, 40, 3, Fr(15, 4), 24, 3), (40, 64, 3, Fr(15, 4), 24, 3),
]

if __name__ == '__main__':
    idx = [int(x) for x in sys.argv[1:]] or list(range(len(REGIONS)))
    log = lambda s: print(s, flush=True)
    for i in idx:
        a0, a1, d0, d1, na, nd = REGIONS[i]
        a0, a1, d0, d1 = Fr(a0), Fr(a1), Fr(d0), Fr(d1)
        log(f"region {i}: form=mixed3 (S_of corrected) a=[{a0},{a1}] d=[{d0},{d1}] eps=[0,1/37] init {na}x{nd}")
        nbox, nfail, worst, dt = BB.run('mixed3', a0, a1, d0, d1, Fr(0), Fr(1, 37), na, nd, log=log)
        log(f"boxes accepted: {nbox}, failures: {nfail}, time {dt:.1f} s")
        for k in range(3):
            if worst[k]:
                log(f"  certified min lower bound of L{k + 1}: {worst[k][0]:.6g} on box {worst[k][1]}")
        log("RESULT: REGION VERIFIED" if nfail == 0 else "RESULT: FAILED")
