# LOG: proof of E(theta, X, Y) >= 0

Authors: Ansh Mishra, Aryan Senthilkumar.
Python 3 with python-flint 0.9.0, mpmath 1.3.0, sympy 1.14.0; OMP_NUM_THREADS=1.

## 2026-10-10 21:10 start

### Step 0: closed form vs integral definition (numerical, mpmath 50 digits)
`verify_closed_form.py`: 60 random points, theta in (0.01, 0.5], |X|, |Y| <= 5, Delta > 0.
Max relative difference closed form vs mp.quad of the integral definition: 2.7e-48. OK.

### 21:15-22:15 exploration and design (numerical unless stated)
- Coordinates x = X, y = rY (s = x+y = Delta/theta >= 0). H := E/(theta x^2 y^2) = g - tm,
  g = (phi(s)-phi(x)phi(y))/(xy) = (1/2)E[(S-T)^2 D_x D_y] (increasing in x and in y; |g(x,y)| <= g(Re x, Re y)),
  tm = theta*m = -theta C_m1/(xy). Closed form for J via divided differences of exp (no p-q singularity) checked
  against mpmath (rel. diff 5e-16, limited by float inputs).
- Numerics: H decreasing in theta on a grid; d/ds H >= 0.041 on grids up to |x|,|y| <= 10; theta*m not monotone in s globally.
- PROVED (analytic): on s = 0, E_m1 = (pq/(p-q))^2 - theta^2 x^2 and
  H(theta,x,-x) = [phi(x)phi(-x) - 1 - theta(1-R^2)]/x^2, R = phi(x)phi(kx)/phi((1+k)x), R decreasing in k
  (log-convexity of phi), so H(theta,x,-x) >= H(1/2,x,-x) = (2 sinh^2 t + tanh^2 t - 3t^2)/(8t^4) >= 0 (t = x/2).
- Plan: (S) boundary s = 0 analytic; compact region: boxes with H > 0 (region B, interval arithmetic) or
  d/ds H > 0 (region A', Taylor models with Cauchy bounds); far region analytic.
- Region B pass 1 (L = 6, exclusion A' = {s<=1,|d|<=1.5} u {theta>=0.25, s<=1, |d|<=4}): 0 failures (runs/B_pass1_*.log).
- First Taylor-model attempt with tight complex ball covers of the torus was far too slow (loose exp enclosures on
  wide complex balls); replaced by an analytic bound |H| <= g(Re x, Re y) + |tm|-bound on the torus.

### 22:15-22:30
- Region B probes: exclusion {all theta: s<=0.6,|d|<=1} u {theta>=0.35: s<=0.6,|d|<=3}, L=4: 0 failures
  (runs/B_probe_*.log); exclusion {s<=0.3,|d|<=0.6} for theta in [0,0.3], L=4: 0 failures (runs/B_probe2_lo.log).
  Probe2 for theta in [0.3,0.5] with a smaller exclusion was stopped as unnecessary.
- far_region.py: all constants verified in Arb (G0(10) = 2.1924..., mu(10)-mu(-1) = 0.4820...).
- regionA2.py (Taylor models, Cauchy/DFT, analytic torus bound) certified test boxes, e.g. theta in [0.49,0.5],
  |x|,|y| <= 1/4 (the degenerate corner): M' = 338, err(d/ds H) = 3.2e-3, all sub-boxes type P or C.
- Fixes for rigour: ee series tail ratio bound (dm/(K+2)); theta half-width of Taylor-model boxes enlarged by 2^-20
  (overlap of float-centred boxes); exclusion test in region B uses a 1e-9 margin and unions of pieces; exact slab
  endpoints in region B.
- Final pieces of A': [0,0.3]x{s<=0.3,|d|<=0.6} (rt 0.025), [0.3,0.35]x{s<=0.6,|d|<=1} (rt 0.0125),
  [0.35,0.45]x{s<=0.6,|d|<=3} (rt 0.0125), [0.45,0.5]x{s<=0.6,|d|<=3} (rt 0.005). Runs runs/A_final_{0,1}.

### 22:24-22:34 final region A' (Taylor models) — rigorous
- First attempt crashed on boxes near (x,y) = (-1.5, 1.25): Arb's acb abs() returns lower bound 0 for wide
  rectangular balls, so |x|_min = 0 and the torus bound failed (not a soundness issue). Fixed with an explicit
  distance-to-rectangle lower bound (regionA2.abs_lower). Rerun from scratch (run_final_A.sh):
  runs/A_final_0.log, runs/A_final_1.log: 318 planned boxes, 326 certified leaves (8 boxes at theta0 = 0.495 split
  in theta), 0 failures, 700 s total.
  Sub-boxes: 7617 of type P (H > 0), 151 of type C (d/ds H > 0, all in theta in [0.45, 0.5]).
  Max error bounds: d/ds H 2.2e-2, H 9.1e-3; max torus bound M' = 1002.
  Per piece: [0,0.3]: 42 leaves; [0.3,0.35]: 24; [0.35,0.45]: 112; [0.45,0.5]: 148.
- check_coverage.py: theta-tiling exact (fractions), every planned box has certified leaves, all sample points of
  planned boxes (s >= 0) lie in certified leaves: "REGION A' COVERAGE: OK".
- Final region B launched 22:34 (run_final_B.sh): theta [0,0.3] and [0.3,0.5], L = 10, exclusion = pieces of A'.

### 22:34-22:40 rigour fixes, then full rerun
- Preliminary final runs (kept in runs/prelim/): region A' 326 leaves certified; region B theta [0,0.3]:
  47229 boxes verified, 0 failed (64 s); theta [0.3,0.5]: 120397 verified, 0 failed (80 s).
- Review found four rigour details, all fixed before the definitive rerun:
  1. ecore._absup: float(Arb upper bound) rounds to nearest; now inflated by 1 + 2^-40 (tail bounds and
     series branch choices use a true upper bound).
  2. ecore.g_series: tail bound now uses a = |x| + |y| (valid for |x|, |y| <= 1.1), not the assumption |x|,|y| <= 1.
  3. regionA2.H_abs_bound: exponent factor now max(1, m^{-(1+theta_r_hi)}) (valid also when m >= 1 is uncertain).
  4. regionA2: M' accumulated with Arb max (no uncertain comparisons); aliasing ratio q computed in Arb from the
     radii actually used.
  None of these changed any verdict in spot tests (corner box: M' = 306, err(d/ds H) = 2.9e-3, 6 P + 20 C sub-boxes).
- Definitive region A' rerun started 22:39 (run_final_A.sh); region B rerun to follow (run_final_B.sh).

### 22:39-22:50 definitive runs (all with the fixed code) — rigorous
- run_final_A.sh: runs/A_final_0.log (159 boxes, 163 leaves, 379 s), runs/A_final_1.log (159 boxes, 163 leaves,
  411 s). Same verdicts as the preliminary run: 326 leaves, 7617 P + 151 C sub-boxes, max err(dH/ds) 2.2e-2,
  max err(H) 9.1e-3, max M' 1002. C sub-boxes only at theta0 in [0.465, 0.495], |x0|,|y0| <= 1.
- run_final_B.sh: runs/B_final_lo.log: theta [0,0.3], L = 10: 47229 verified, 4871 skipped, 0 FAILED (93 s);
  runs/B_final_hi.log: theta [0.3,0.5], L = 10: 120397 verified, 5187 skipped, 0 FAILED (109 s).
- check_coverage.py (A and B): REGION A' COVERAGE: OK; REGION B: OK. far_region.py: all assertions pass.
- RESULT: E(theta, X, Y) >= 0 on the whole domain, E = 0 iff XY = 0 (PROOF.md). Computer-assisted; not yet
  independently reviewed.
