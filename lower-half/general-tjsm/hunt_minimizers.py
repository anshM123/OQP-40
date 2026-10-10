"""Re-evaluate the minimisers saved by tf_hunt.py: rho* to more digits, and how far the pair is from commuting."""
import glob
import numpy as np
from tf_hunt import pair_from, rho
for f in sorted(glob.glob('tf_hunt_best_r*_s*.npy')):
    v = np.load(f)
    d = int(v[0]); params = v[1:]
    r = int(f.split('_r')[1].split('_')[0])
    A, B = pair_from(params, d)
    comm = np.linalg.norm(A @ B - B @ A) / (np.linalg.norm(A) * np.linalg.norm(B))
    print(f"{f}: d={d}, ray through (1,{r}): rho* (K=8) = {rho(params, d, r, 8):.10f}; relative commutator |[A,B]|/(|A||B|) = {comm:.3e}")
