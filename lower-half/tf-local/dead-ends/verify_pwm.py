"""50-digit re-check of PWM candidates: log R(h) on the h grid."""
import json, sys
import mpmath as mp
from verify_found import unpack_mp, word_avg
mp.mp.dps = 50
for fn in sys.argv[1:]:
    for c in json.load(open(fn)):
        d, n, m = c['d'], c['n'], c['m']
        X, Y = unpack_mp(c['x'], d)
        hs = [mp.mpf('0.05') + k * (mp.mpf('0.95') / 38) for k in range(39)]
        r = []
        for h in hs:
            p = word_avg(mp.expm(h * X), mp.expm(h * Y), n, m)
            L = mp.re(sum(mp.expm(h * (n * X + m * Y))[i, i] for i in range(d)))
            r.append(mp.log(p) - mp.log(L))
        dr = [r[k + 1] - r[k] for k in range(38)]
        k = min(range(38), key=lambda i: dr[i])
        print(f"{fn} d={d} ({n},{m}) saved {c['score']:.4g} | 50-digit min step {mp.nstr(dr[k]/max(r),4)} at h={mp.nstr(hs[k],3)}; logR(0.05)={mp.nstr(r[0],4)} logR(1)={mp.nstr(r[-1],4)} max={mp.nstr(max(r),4)}", flush=True)
