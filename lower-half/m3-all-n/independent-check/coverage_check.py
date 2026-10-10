"""Mechanical check that the regions verified by the independent code cover the whole (a, d) quadrant.
Core rectangles (a-range x d-range) from the run log headers; strip (0 <= a <= 3) and tail charts as described."""
from fractions import Fraction as Fr
INF = Fr(10 ** 9)
core = {'R1': (50, 120, 25, 60), 'V2': (16, 50, 16, 64), 'V3': (120, 250, 16, 64), 'V4': (3, 64, 64, 512),
        'V5': (50, 120, 8, 25), 'V6': (14, 32, Fr(7, 4), Fr(5, 2)), 'V7': (64, 250, 64, 512), 'V8': (16, 64, 8, 16),
        'V9': (3, 16, 16, 64), 'V10': (8, 64, 0, 3), 'V11': (16, 64, 3, Fr(15, 4)), 'V12': (50, 120, 60, 64),
        'W1': (3, 8, 0, 3), 'W2': (64, 250, 0, Fr(15, 4)), 'W3': (16, 64, Fr(15, 4), 8), 'W4': (3, 16, 3, Fr(15, 4)),
        'W5': (3, 16, Fr(15, 4), 16), 'W6': (64, 250, Fr(15, 4), 8), 'W7': (120, 250, 8, 16),
        'T1': (3, 250, 512, INF), 'T3': (250, INF, 512, INF), 'T5/T6': (250, INF, 0, 512)}
rects = [tuple(Fr(x) for x in r) for r in core.values()]
A = sorted({r[0] for r in rects} | {r[1] for r in rects})
D = sorted({r[2] for r in rects} | {r[3] for r in rects})
gaps = []
for i in range(len(A) - 1):
    for j in range(len(D) - 1):
        am, dm = (A[i] + A[i + 1]) / 2, (D[j] + D[j + 1]) / 2
        if A[i] >= 3 and not any(r[0] <= A[i] and A[i + 1] <= r[1] and r[2] <= D[j] and D[j + 1] <= r[3] for r in rects):
            gaps.append((float(A[i]), float(A[i + 1]), float(D[j]), float(D[j + 1])))
print('a >= 3: uncovered cells:', gaps if gaps else 'none')
# strip 0 <= a <= 3 in (a, b), b >= a: S0 [0,1/4]x[0,1/4]; S1 strips [x0,x0+1/4], b in [1/4, x0+4];
# S2 strips [y0,y0+1/8], b in [y0+1/8+15/4, 8]; S3 strips of width 1/2, b in [15/2, 515]; T2: d >= 512.
bad = []
for k in range(3 * 64):
    a0, a1 = Fr(k, 64), Fr(k + 1, 64)
    x0 = Fr(int(a0 * 4), 4)                      # S1 strip containing [a0, a1]
    y0 = Fr(int(a0 * 8), 8)                      # S2 strip
    pieces = []
    if a1 <= Fr(1, 4):
        pieces.append((Fr(0), Fr(1, 4)))
    pieces.append((Fr(1, 4), x0 + 4))
    pieces.append((y0 + Fr(1, 8) + Fr(15, 4), Fr(8)))
    pieces.append((Fr(15, 2), Fr(515)))
    pieces.append((a1 + 512, INF))               # T2 (d >= 512 for every a of the cell)
    lo = a0                                       # need b from a (>= a0) upwards
    for p in sorted(pieces):
        if p[0] <= lo:
            lo = max(lo, p[1])
    if lo < INF:
        bad.append((float(a0), float(lo)))
print('0 <= a <= 3: cells with uncovered b:', bad if bad else 'none')
