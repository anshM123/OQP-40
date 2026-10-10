# The general lower half: joint-spectral-measure route (code and logs)

These are the computations behind [`../../math/08-general-lower-half-route.md`](../../math/08-general-lower-half-route.md).
That note proves a reduction of the general lower half to **Conjecture TF**, and records the evidence for it and the
variants that fail. TF itself is **not** proved, and the general lower half remains open.

Requirements: Python 3 with numpy, scipy, mpmath and cvxpy (Clarabel). Run each script from this folder with
`OMP_NUM_THREADS=1`.

| Script | What it does | Log |
|---|---|---|
| `tjsm.py` | the measure: word averages, the singular points, and the density of the continuous part in polar coordinates | (module) |
| `calib.py` | checks p_{n,m} = S_{n,m} + N(N+1)·∫a^n b^m dμ_c against exact word averages; this fixes the constant 1/2π | `logs/calib.log` |
| `tailtest.py`, `tailconv.py` | first-order dominance without tilt: fails near the bottom eigenvalue of Z_θ, stable under refinement | `logs/tailconv.log` |
| `icxtest.py` | integrated tails; G_θ < 0, i.e. the real-exponent lower half fails for small exponents | `logs/icxtest.log` |
| `realquad.py` | the real-exponent comparison on a grid of exponents (quadrature; accurate only for moderate exponents) | (helper) |
| `tftest.py`, `tftest2.py`, `tfstress.py` | Conjecture TF by quadrature on several rays, random, near-commuting and Cha–Lee pairs | `logs/tftest2.log`, `logs/tfstress.log` |
| `tf_moment_sdp.py`, `tf_ratio_sdp.py` | Conjecture TF on the rays through (1, r) from exact word averages: ρ* by a semidefinite program over increasing polynomials | `logs/tf_ratio_r1.log` |
| `tff_sdp.py` | TF (reference L) and its F-version (reference AB) on the rays through (1, 1), (1, 2), (1, 3) | `logs/tff_r1.log`, `logs/tff_r2.log`, `logs/tff_r3.log` |
| `coltf_sdp.py` | the column version (fixed m, tilt by one A): fails at m = 2 | `logs/coltf.log` |
| `latmono.py` | p_{n,m}/L_{n,m} is not monotone in n (exact word averages) | `logs/latmono.log` |
| `tf_hunt.py` | adversarial search against TF (random sampling, then local descent); writes `tf_hunt_best_*.npy` | `logs/tf_hunt_r1_s11.log`, `logs/tf_hunt_r1_s12.log`, `logs/tf_hunt_r2_s13.log` |
| `hunt_minimizers.py` | re-evaluates the saved minimisers to more digits and reports how far they are from commuting | `logs/hunt_minimizers.log` |

**Notes.**
- The quadrature of the continuous density needs care near the singular directions, where the density has narrow spikes.
  For large exponents it becomes unreliable, so every statement about TF on the rays through (1, r) rests on the exact
  word-average tests.
- The hunt logs print ρ* to seven digits. Values printed as 1.0000000 are nearly commuting 2 × 2 pairs, at the solver
  tolerance; see `logs/hunt_minimizers.log`.
- In the hunt logs, local file paths in solver warnings were shortened.
- The logs other than the hunt logs were produced on 2026-10-10 from the scripts in this folder.
