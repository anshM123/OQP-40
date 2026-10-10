"""Real-exponent lower half via Heinavaara's measure: p_{x,y} := (x+y)(x+y+1) int a^x b^y dmu  vs  L_{x,y} = tr exp(x log A + y log B)."""
import sys
import numpy as np
from tailtest import radial_tables, logm_h
from tjsm import singular_points, word_avg

def make_eval(A, B, nphi=400, nr=200):
    PHI, R, MASS = radial_tables(A, B, nphi, nr)
    la, lb = np.log(R * np.cos(PHI)), np.log(R * np.sin(PHI))
    pts = np.array(singular_points(A, B))
    LA, LB = logm_h(A), logm_h(B)
    def p(x, y):
        N = x + y
        return N * (N + 1) * np.sum(MASS * np.exp(x * la + y * lb)) + np.sum(pts[:, 0] ** x * pts[:, 1] ** y)
    def L(x, y):
        return np.sum(np.exp(np.linalg.eigvalsh(x * LA + y * LB)))
    return p, L

if __name__ == '__main__':
    rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 0)
    def rand_pd(d, spread=1.0):
        X = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))
        Q, _ = np.linalg.qr(X)
        return (Q * np.exp(spread * rng.normal(size=d))) @ Q.conj().T
    grid = np.round(np.arange(0.25, 4.01, 0.25), 2)
    for trial in range(8):
        d = [2, 3, 3, 4, 4, 5, 3, 4][trial]; sp = [1, 1, 2, 1, 2, 1, 3, 3][trial]
        A, B = rand_pd(d, sp), rand_pd(d, sp)
        p, L = make_eval(A, B)
        acc = max(abs(p(n, m) / word_avg(A, B, n, m) - 1) for n, m in [(1, 1), (2, 1), (2, 2), (3, 2)])
        worst_in, worst_out = (np.inf, None), (np.inf, None)
        for x in grid:
            for y in grid:
                r = np.log(p(x, y) / L(x, y))
                if x >= 1 and y >= 1:
                    worst_in = min(worst_in, (r, (x, y)))
                else:
                    worst_out = min(worst_out, (r, (x, y)))
        print(f"[d={d} spread={sp}] integer-moment rel err {acc:.1e}; min log(p/L) on [1,4]^2: {worst_in[0]: .3e} at {worst_in[1]}; "
              f"outside: {worst_out[0]: .3e} at {worst_out[1]}", flush=True)
