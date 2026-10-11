"""RIGOROUS certification of inequality (C) on [T0,T1] x [0,L]^2 x [-1,1], version 2 (adds the whole-column
certificate W of PROOF.md Lemma 3.7, tried on full columns with min(a0, c0) >= 2).
Ansh Mishra, Aryan Senthilkumar.

Initial boxes are full w-columns Theta x A x C x [-1, 1].  A full column with min(a0, c0) >= 2 is first tested with
W; if W fails the column is bisected in (theta, a, c) (keeping full columns) up to a depth limit, otherwise the
box is treated as in cert_core.py (certificates P, I, F, D; bisection of the widest normalised variable).
Usage: python cert_v2.py T0 T1 L outfile
Leaves: one line per leaf 'type th0 th1 a0 a1 c0 c1 w0 w1' (W leaves have w0=-1, w1=1); failures 'X'.
"""
import sys, time
from flint import ctx
from rbox import box_bounds, dw_lower, wcert

ctx.prec = 100
AW = 2.0          # W / column splitting only for min(a0, c0) >= AW
T0, T1, L = float(sys.argv[1]), float(sys.argv[2]), float(sys.argv[3])
out = open(sys.argv[4], 'w')


def weligible(a0, c0):
    """Heuristic (no effect on rigour): columns on which W is tried / kept as full columns."""
    return min(a0, c0) >= AW or (max(a0, c0) >= 3.0 and min(a0, c0) >= 0.25)


def certify(b):
    th0, th1, a0, a1, c0, c1, w0, w1 = b
    if w0 == -1.0 and w1 == 1.0 and th0 > 0 and weligible(a0, c0):
        ok, info = wcert(th0, th1, a0, a1, c0, c1)
        if ok:
            return 'W'
    o = box_bounds(th0, th1, a0, a1, c0, c1, w0, w1)
    if o['Rlo'] > 0:
        return 'P'
    if o['epsP_lo'] >= 1:
        return 'I'
    if o['Flo'] > 0:
        return 'F'
    d = dw_lower(th0, th1, a0, a1, c0, c1, -1.0, w1)
    if d > 0:
        return 'D'
    return None


def halves(b, k, mid):
    b1 = list(b); b2 = list(b)
    b1[2 * k + 1] = mid
    b2[2 * k] = mid
    return [tuple(b1), tuple(b2)]


def split(b):
    """Bisection rule (no effect on rigour).  The theta-width is weighted by max(6, 4(1 + c1)) because
    b = theta c/(1-theta) moves by up to 4 c dtheta across a box."""
    th0, th1, a0, a1, c0, c1, w0, w1 = b
    full = (w0 == -1.0 and w1 == 1.0)
    tw = (th1 - th0) * max(6.0, 4.0 * (1.0 + c1))
    if full and th0 > 0 and weligible(a0, c0) and max(a1 - a0, c1 - c0, tw / 6.0) > 1 / 64:
        sc = [tw, (a1 - a0), (c1 - c0)]
        k = max(range(3), key=lambda i: sc[i])
    else:
        sc = [tw, (a1 - a0), (c1 - c0), (w1 - w0) * 0.5]
        k = max(range(4), key=lambda i: sc[i])
    return halves(b, k, (b[2 * k] + b[2 * k + 1]) / 2)


nt = max(1, round((T1 - T0) / (1 / 16)))
na = max(1, round(L / 0.5))
stack = []
for i in range(nt):
    for j in range(na):
        for k in range(na):
            stack.append((T0 + (T1 - T0) * i / nt, T0 + (T1 - T0) * (i + 1) / nt,
                          L * j / na, L * (j + 1) / na, L * k / na, L * (k + 1) / na, -1.0, 1.0))
t0 = time.time()
cnt = {'W': 0, 'P': 0, 'I': 0, 'F': 0, 'D': 0, 'X': 0}
nproc = 0
while stack:
    b = stack.pop()
    nproc += 1
    try:
        cert = certify(b)
    except Exception:
        cert = None
    if cert:
        cnt[cert] += 1
        out.write(cert + ' ' + ' '.join(repr(x) for x in b) + '\n')
    else:
        th0, th1, a0, a1, c0, c1, w0, w1 = b
        if min(th1 - th0, a1 - a0, c1 - c0, w1 - w0) < 2.0 ** -22:
            cnt['X'] += 1
            out.write('X ' + ' '.join(repr(x) for x in b) + '\n')
            print('FAIL box', b, flush=True)
        else:
            stack.extend(split(b))
    if nproc % 2000 == 0:
        print(f"{time.time() - t0:8.0f}s processed {nproc} stack {len(stack)} leaves {cnt}", flush=True)
        out.flush()
out.close()
print(f"DONE {time.time() - t0:.0f}s processed {nproc} leaves {cnt}", flush=True)
