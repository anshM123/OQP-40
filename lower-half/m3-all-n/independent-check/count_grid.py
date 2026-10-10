from fractions import Fraction as Fr
E37 = Fr(1, 37)
def grid(a0, a1, na, blo, bhi, ne, wb=None, geometric=None):
    boxes = []
    cells = []
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
                continue
            cells.append((x0, x1, y0, y1))
            nek = max(ne, -(-int(y1) // 12)) if geometric else ne
            for k in range(nek):
                boxes.append((x0, x1, y0, y1))
    return boxes, cells
# S3 as in the current tb_sx_run.py: b from x1 + 15/2
b1, c1 = grid(Fr(0), Fr(3), 6, lambda x0, x1: x1 + Fr(15, 2), lambda x0, x1: Fr(515), 4, geometric=16)
# S3 with b from 15/2 for every strip
b2, c2 = grid(Fr(0), Fr(3), 6, lambda x0, x1: Fr(15, 2), lambda x0, x1: Fr(515), 4, geometric=16)
print("current grid (b >= x1 + 15/2):", len(b1), " constant b >= 15/2:", len(b2))
# cell boundaries of strip [0, 1/2] in both versions, to compare with the log lines (178.59, 189.77, 443.64, 471.38, 13.047, 13.461, 21.281, 22.625, 41.594, 44.203)
for name, cc in (("current", c1), ("const", c2)):
    s = sorted(set(float(y0) for (x0, x1, y0, y1) in cc if x0 == 0))
    print(name, [round(v, 3) for v in s if 12 < v < 50 or 170 < v < 200 or 440 < v < 480][:20])
# S2 runs
b3, _ = grid(Fr(0), Fr(3, 2), 12, lambda x0, x1: x1 + Fr(15, 4), lambda x0, x1: Fr(15, 2), 4, geometric=64)
b4, _ = grid(Fr(3, 2), Fr(3), 12, lambda x0, x1: x1 + Fr(15, 4), lambda x0, x1: Fr(15, 2), 4, geometric=64)
print("S2a initial boxes:", len(b3), "(log: 1444)   S2b:", len(b4), "(log: 636)")
# S1
b5, _ = grid(Fr(0), Fr(3), 12, lambda x0, x1: Fr(1, 4), lambda x0, x1: x0 + 4, 4, wb=Fr(1, 8))
print("S1 initial boxes:", len(b5), "(log: 1528)")
