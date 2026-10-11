"""Mechanical coverage check for the certified leaf boxes of cert_core.py.
Ansh Mishra, Aryan Senthilkumar.

Usage: python check_coverage.py L file1 [file2 ...]
Checks, with exact rational arithmetic (all box ends are dyadic floats, converted exactly by Fraction):
  1. every leaf has a certificate type in {W, P, I, F, D} (no failures X);
  2. every leaf lies inside [0, 1/2] x [0, L] x [0, L] x [-1, 1];
  3. the leaves have pairwise disjoint interiors (sweep over theta, then exact pairwise test inside slabs);
  4. the total volume equals the volume of the domain  (1/2) L^2 * 2.
(3) + (4) imply that the union of the closed leaves is the whole closed domain.
Additionally 20000 random points are located (each must lie in at least one leaf).
"""
import sys, random
from fractions import Fraction as Fr
from collections import defaultdict

L = Fr(sys.argv[1])
leaves = []
types = defaultdict(int)
for fn in sys.argv[2:]:
    for line in open(fn):
        p = line.split()
        if not p:
            continue
        t = p[0]
        types[t] += 1
        b = tuple(Fr(float(x)) for x in p[1:9])
        leaves.append((t, b))
print('leaf counts by type:', dict(types))
ok = True
if any(t not in ('W', 'P', 'I', 'F', 'D') for t, _ in leaves):
    print('FAILED: uncertified leaves present'); ok = False
dom = (Fr(0), Fr(1, 2), Fr(0), L, Fr(0), L, Fr(-1), Fr(1))
for t, b in leaves:
    for k in range(4):
        if not (dom[2 * k] <= b[2 * k] < b[2 * k + 1] <= dom[2 * k + 1]):
            print('FAILED: leaf outside domain or degenerate', t, b); ok = False
            break
vol = sum((b[1] - b[0]) * (b[3] - b[2]) * (b[5] - b[4]) * (b[7] - b[6]) for _, b in leaves)
dvol = (dom[1] - dom[0]) * (dom[3] - dom[2]) * (dom[5] - dom[4]) * (dom[7] - dom[6])
print('total leaf volume =', vol, ' domain volume =', dvol, ' equal:', vol == dvol)
if vol != dvol:
    ok = False

# disjointness: bucket leaves by a coarse grid in (a, c), test pairs in the same bucket exactly
def overl(b1, b2):
    return all(max(b1[2 * k], b2[2 * k]) < min(b1[2 * k + 1], b2[2 * k + 1]) for k in range(4))

G = 64
buckets = defaultdict(list)
for i, (_, b) in enumerate(leaves):
    ia0 = int(b[2] / L * G); ia1 = min(G - 1, int(b[3] / L * G - Fr(1, 10 ** 9)))
    ic0 = int(b[4] / L * G); ic1 = min(G - 1, int(b[5] / L * G - Fr(1, 10 ** 9)))
    for ia in range(ia0, max(ia0, ia1) + 1):
        for ic in range(ic0, max(ic0, ic1) + 1):
            buckets[(ia, ic)].append(i)
nover = 0
checked = 0
for key, idx in buckets.items():
    idx.sort(key=lambda i: leaves[i][1][0])
    # sweep in theta within the bucket
    active = []
    for i in idx:
        b = leaves[i][1]
        active = [j for j in active if leaves[j][1][1] > b[0]]
        for j in active:
            checked += 1
            if overl(b, leaves[j][1]):
                nover += 1
                if nover < 5:
                    print('OVERLAP', leaves[j], leaves[i])
        active.append(i)
print('pair tests', checked, 'overlaps', nover)
if nover:
    ok = False

random.seed(1)
miss = 0
pts = [(Fr(random.random()) / 2, Fr(random.random()) * L, Fr(random.random()) * L, Fr(random.random()) * 2 - 1)
       for _ in range(20000)]
for pt in pts:
    ia = min(G - 1, int(pt[1] / L * G)); ic = min(G - 1, int(pt[2] / L * G))
    found = any(all(leaves[i][1][2 * k] <= pt[k] <= leaves[i][1][2 * k + 1] for k in range(4)) for i in buckets[(ia, ic)])
    if not found:
        miss += 1
print('random points not covered:', miss)
if miss:
    ok = False
print('COVERAGE:', 'OK' if ok else 'FAILED')
