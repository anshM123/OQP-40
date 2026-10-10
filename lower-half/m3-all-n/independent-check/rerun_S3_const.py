"""Re-run of chart S3 of Theorem B'' with the CURRENT tb_sx.py / tb_sx_run.py (unchanged files), on the grid that the
logged S3 run actually used: 6 a-strips of width 1/2 of [0, 3], b in [15/2, 515] for EVERY strip (geometric b-cells,
RB = 16, eps-cells max(4, ceil(b/12))), nu form, no box tightening.  (The documented command
`tb_sx_run.py nu 0 3 15/2 515 6 16 4` would start each strip at b = x1 + 15/2 with the current driver.)
"""
import os
import sys
from fractions import Fraction as Fr
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
import tb_sx_run as R

log = lambda s: print(s, flush=True)
boxes = R.grid('nu', Fr(0), Fr(3), 6, lambda x0, x1: Fr(15, 2), lambda x0, x1: Fr(515), 4, geometric=16)
log(f"S3 re-run (current code): nu form, a in [0, 3] (6 strips), b in [15/2, 515] for every strip; {len(boxes)} initial boxes")
nbox, nfail, nsplit, worst, dt = R.run(boxes, log)
log(f"boxes accepted: {nbox}, splits: {nsplit}, failures: {nfail}, time {dt:.1f} s")
for k, (v, bx) in sorted(worst.items()):
    log(f"  certified min lower bound of {k}: {v:.6g} on box (a0,a1,b0,b1,e0,e1) = {bx}")
log("RESULT: REGION VERIFIED" if nfail == 0 else "RESULT: FAILED")
