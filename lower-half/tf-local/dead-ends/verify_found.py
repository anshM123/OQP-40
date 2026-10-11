"""Re-evaluate saved candidates in 50-digit arithmetic: f on the lambda grid, PM and log-convexity."""
import json, sys
import mpmath as mp
import numpy as np
mp.mp.dps = 50

def unpack_mp(x, d):
    k = 0
    def herm():
        nonlocal k
        M = mp.matrix(d, d)
        for i in range(d):
            M[i, i] = mp.mpf(x[k]); k += 1
        for i in range(d):
            for j in range(i + 1, d):
                M[i, j] = mp.mpc(x[k], x[k + 1]); M[j, i] = mp.conj(M[i, j]); k += 2
        return M
    return herm(), herm()

def word_avg(A, B, n, m):
    d = A.rows
    S = {(0, 0): mp.eye(d)}
    for i in range(n + 1):
        for j in range(m + 1):
            if i == 0 and j == 0: continue
            T = mp.zeros(d, d)
            if i > 0: T += A * S[(i - 1, j)]
            if j > 0: T += B * S[(i, j - 1)]
            S[(i, j)] = T
    return mp.re(sum(S[(n, m)][k, k] for k in range(d))) / mp.binomial(n + m, n)

def _main():
    for fn in sys.argv[1:]:
        for c in json.load(open(fn)):
            d, n, m = c['d'], c['n'], c['m']
            Z, T = unpack_mp(c['x'], d)
            th = mp.mpf(n) / (n + m)
            lams = [mp.mpf(-3) + mp.mpf(k) / 10 for k in range(61)]
            v = [word_avg(mp.expm(Z + (1 - th) * l * T), mp.expm(Z - th * l * T), n, m) for l in lams]
            f0 = v[30]
            scale = max(v[-1], v[0]) - f0
            dpos = min(v[k + 1] - v[k] for k in range(30, 60)) / scale
            dneg = min(v[k] - v[k + 1] for k in range(0, 30)) / scale
            lv = [mp.log(t) for t in v]
            c2 = [(lv[k + 1] - 2 * lv[k] + lv[k - 1]) * 100 for k in range(1, 60)]
            lc = min(c2) / max(abs(t) for t in c2)
            print(f"{fn} d={d} ({n},{m}) saved {c['score']:.4g} | 50-digit: PM+ {mp.nstr(dpos,4)} PM- {mp.nstr(dneg,4)} logconv {mp.nstr(lc,4)}  f0={mp.nstr(f0,6)} scale={mp.nstr(scale,4)}", flush=True)


if __name__ == "__main__":
    _main()
