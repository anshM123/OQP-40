"""probe single boxes of the strip verification (development aid; prints enclosures and timing)."""
import sys
import time
from fractions import Fraction as Fr
import tb_sx as S


def probe(form, coords, a0, a1, y0, y1, e0, e1, corner=False, L=16, ke=1, J=10):
    t0 = time.time()
    try:
        r = S.evaluate(form, coords, a0, a1, y0, y1, e0, e1, L=L, ke=ke, corner=corner, J=J)
        ok, out, contrib, g = S.conditions(r)
    except Exception as ex:
        print(f"{form} {coords} a=[{float(a0)},{float(a1)}] y=[{float(y0)},{float(y1)}] e=[{float(e0):.4f},{float(e1):.4f}] ERROR {type(ex).__name__}: {ex}  ({time.time() - t0:.2f} s)")
        return None
    dt = time.time() - t0
    s = ' '.join(f"{k}=[{float(v.lower()):.4f},{float(v.upper()):.4f}]" for k, v in out.items())
    gs = ' '.join(f"[{float(x.lower()):.5f},{float(x.upper()):.5f}]" for x in g)
    print(f"{form} {coords} a=[{float(a0)},{float(a1)}] y=[{float(y0)},{float(y1)}] e=[{float(e0):.4f},{float(e1):.4f}] ok={ok} {s}"
          f"\n    G_a,G_b,G_ab = {gs}  contrib(y,eps,a) = {[f'{c:.1e}' for c in contrib]}  ({dt:.2f} s)", flush=True)
    return ok


if __name__ == '__main__':
    E = Fr(1, 37)
    probe('direct', 'ab', Fr(0), Fr(1, 2), Fr(1), Fr(9, 8), Fr(0), E)
    probe('direct', 'ab', Fr(0), Fr(1, 2), Fr(4), Fr(17, 4), Fr(0), E)
    probe('direct', 'ab', Fr(0), Fr(1, 4), Fr(1), Fr(9, 8), Fr(0), E)
    probe('direct', 'ad', Fr(1, 2), Fr(1), Fr(0), Fr(1, 8), Fr(0), E)
    probe('direct', 'ad', Fr(5, 2), Fr(3), Fr(4), Fr(9, 2), Fr(0), E)
    probe('nu', 'ab', Fr(0), Fr(1, 2), Fr(20), Fr(21), Fr(0), E)
    probe('nu', 'ab', Fr(0), Fr(1, 2), Fr(200), Fr(208), Fr(0), E)
    probe('nu', 'ab', Fr(5, 2), Fr(3), Fr(8), Fr(17, 2), Fr(0), E)
    probe('direct', 'ab', Fr(0), Fr(1, 2), Fr(0), Fr(1, 2), Fr(0), E, corner=True)
    probe('direct', 'ab', Fr(0), Fr(1, 4), Fr(0), Fr(1, 4), Fr(0), E, corner=True)
