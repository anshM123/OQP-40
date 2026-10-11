# LOG: Conjecture TF for 2 × 2 pairs

Ansh Mishra, Aryan Senthilkumar.
Python 3 (python-flint 0.9.0 / Arb, mpmath 1.3.0, numpy, scipy). OMP_NUM_THREADS=1, at most 2 heavy processes.

## 2026-10-11

### Step 1. Closed forms and the shape of T (NUMERICAL)
- `cf2x2.py`: matrix closed forms in the normal form A = I + α σ_z, B = I + β(cos γ σ_z + sin γ σ_x):
  ζ_{1,2}, P = Tr(AB^r), G = Tr(A⁻¹ #_{1−θ} B⁻¹) (via M = A^{1/2}B⁻¹A^{1/2}), GT, AH, c = G − e^{−ζ₂},
  u_c = −log c, C(u), v_min/v_max (min/max of ℓ on the boundary circle of W).
- `explore_shape.py 1 3`: the exact Bloch-sphere tail (`tf-local/near-identity/tf2x2_sphere.tf_tail`) equals C(u)/(N₀(N₀+1))
  on [ζ₁, v_min] to 10 digits (3 random pairs). On [ζ₁, ζ₂] the grid minimum of T was at ζ₂ in these samples, and the
  minimum over [ζ₁, v_min] is at u_c.

### Step 2. The structural reduction (PROVED, PROOF.md Section 2)
- Observation: T'(u) = −e^{N₀u} f(u), (e^{−u}f)' = −e^{−u}(Λ(u) − #{ζ_i > u}), Λ(u) = ⟨Π, 1[ℓ > u]⟩.
- Lens lemma: in the disk picture Π has density −(1/π)(1−|y|²)^{−3/2} plus a boundary layer; for a convex superlevel
  set K, Λ = 2 − k − (lens integrals) ≤ 1 (k = number of cut caps). Hence e^{−u}f is decreasing on [ζ₁, v_min]
  (closed form 1 − c e^u) and nondecreasing on [v_min, ζ₂]; the minimum of T over R is at u_c if u_c < v_min, and TF
  is automatic otherwise. TF(2×2) ⇔ C(min(u_c, v_min)) ≥ 0, in particular TF ⇐ (C).
- `check_structure.py 3 2`: Λ computed directly from the disk formula with a smoothed indicator: 0.94–0.99 and
  0.90–0.93 at interior levels of two random pairs (< 1 as claimed); e^{−u}f from finite differences of the exact tail
  is increasing on (v_min, ζ₂). (The first grid point just above v_min reported Λ = 2: the integrator missed the
  narrow cap there; not a counterexample — the atom at v_min is resolved in the lens formula.)

### Step 3. Inequality (C): landscape (NUMERICAL)
- `explore_C.py 1 4000` (60 digits; random, near-identity at θ ≈ 1/2, near-singular α, β → 1, near-commuting):
  (C) holds in all samples; worst normalised ratio Dc/(α²β² sin²γ) = 4.1e−5 at θ = 0.499998, α, β ~ 1e−4 (the
  identity corner, where the ratio vanishes linearly as predicted by note 09 Theorem 2.3).
- Hyperbolic form (`hyp.py`, `explore_hyp.py`): det-normalised, P = 2[cosh a cosh c + w sinh a sinh c],
  G = 2[sinh(θd)cosh a + sinh((1−θ)d)cosh b]/sinh d (geodesic formula for 2×2 geometric means), λ₂ = e^{θR_E};
  matches cf2x2 to 15 digits. (C) ⇔ F = θ log(1+X_P) + log(1−Y_G) ≥ 0.
- `explore_w.py`: F is not concave in w (convex near w = −1 when a ≈ c, and in the middle for large a = c); the
  normalised R = F/(θ(1−w²)a²c²) stays positive and O(1) for moderate a, c, decays like (a+c)/(a²c²) in the bulk for
  large a, c, and is huge in the thin layers near w = ±1.
- `explore_gaps.py`: ε_G is not exactly concave in w (relative violations ≤ 0.3%); the "BL with margin" condition
  Y_G(1+X_P) ≤ θX_P holds wherever ε_P < 1 on the grid.

### Step 4. Rigorous core (RIGOROUS machinery)
- Divided-difference representations ε_P = 8q Ch[z₋, z, z₊], ε_G = (θ/(1−θ))² q E_G (PROOF.md Lemma 3.2), and the
  integral representation U_t(C) = (sin πt/π)∫λ^{−t}/(1 + 2Cλ + λ²) dλ (monotonicity of all U-divided differences),
  series U_t(1+y) = t Σ q_k(t)(−2y)^k with |q_k| ≤ 4^{−k}.
- `rcore.py` (first version) — ball arithmetic throughout. Problems found and fixed:
  1. θ-ball amplification in explicit U divided differences (width 0.02 in θ blew up the U-term by ~10×): fixed by
     the mean value theorem in θ around the box midpoint (centred form).
  2. Midpoint-radius overestimation on wide boxes (e.g. q's lower bound 0.0065 instead of 0.625): replaced by
     directed endpoint evaluation in `rbox.py` using the monotone structure (PROOF.md Section 4.1).
  3. Arb's radius rounding makes clamped balls dip below the clamp value: node evaluation now uses explicit
     max(lower, clamp) points.
- `test_rcore.py 2 40`: 0 mismatches vs the independent 60-digit mpmath code (points incl. w within 1e−8 of ±1,
  θ = 0.01, a, c up to 6); commuting faces: R(θ,a,c,±1) agrees with 4H (E-proof `ecore.H_point`) to 12 digits at
  40 random points.
- D-certificate (PROOF.md Lemma 3.6): ∂_wR ≥ ac·D with a 1/R_E main term; on the corner box
  [0.45, 0.5] × [0, 0.1]² × [−1, 1] D_lo = 1.49 > 0.
- `test_rbox.py 1 150`: 600 sampled points in 150 random boxes, every bound (R, ε_P, F, D) respected by the 50-digit
  values: 0 violations.

### Step 5. Certification runs (RIGOROUS)
- Probe θ ∈ [0.4375, 0.5], L = 1: 143 leaves, < 1 s, 0 failures (the identity corner is covered by D boxes).
- Probes L = 3 (`probe_L3_*`): 914 + 32,327 leaves, 0 failures, 49 s.
- Probes L = 6: θ ∈ [0, 1/4] done (54,306 leaves, 0 failures, 34 s); θ ∈ [1/4, 1/2] stopped by PID after ~5 min:
  boxes near w = 1 at a, c ≈ 6, θ ≈ 1/2 shrink to widths 1e−5 in (θ, a, c). Diagnosis: in the thin layer Y_G is close
  to 1 while X_P is huge; the decoupled endpoint bounds overestimate Y_G by the variation of E_G across the box.
  Added certificate F (PROOF.md Lemma 3.4(F), −log(1−Y_G) ≤ θR_E because G ≥ 2). A greedy "best split" heuristic was
  tried and abandoned (it degenerated, splitting c to width 1e−7 and declaring failures; these were splitting
  artifacts, not counterexamples); reverted to bisecting the widest normalised variable.
- L = 3 with `cert_core.py` (complete at the time; superseded by Step 8 because of the zrange fix there):
  `runs/L3_lo.txt` (θ ∈ [0, 1/4]): 914 leaves (P 824, I 49, D 41), 1 s;
  `runs/L3_hi.txt` (θ ∈ [1/4, 1/2]): 32,327 leaves (P 28,857, I 3,450, D 20), 45 s; wall 47 s; 0 failures.
  D boxes: the identity corner [0.4375, 0.5] × [0, 0.5]² × (4 w-ranges), the line {w = −1, a = c ≈ 0.6–0.75} near
  θ = 1/2, and a few boxes at θ ∈ [0, 1/64], a ≈ 1.5, small c.
  `check_coverage.py 3 runs/L3_lo.txt runs/L3_hi.txt`: total volume 9 = domain volume, 1,455,021 exact pair tests,
  0 overlaps, 20,000 random points covered: COVERAGE OK (6 s). Log: `runs/coverage_L3.log`.
- L = 4 with `cert_core.py`: θ ∈ [0, 1/4]: 2,757 leaves (P 2,410, I 306, D 41), 0 failures, ~1 s;
  θ ∈ [1/4, 1/2]: see Step 7 (stopped). (All files of this step are now in `runs/superseded/pre_zrange_fix/`.)

### Step 6. Far region (NUMERICAL)
- `scan_far.py 1 4000` (120 digits; a, c log-uniform up to ~34; θ near 0 and 1/2; w in the bulk and in layers
  1 ∓ w = 10^{−k}, k ≤ 40): F < 0 in 0 samples; min R = 6.9e−5 (bulk, a, c ≈ 30, where F itself is large);
  min F = 1.2e−45 (> 0) in a layer with 1 − w = 1.4e−38. Log: `runs/scan_far_s1.log`.
- Numerical shape for large a, c (`explore` in this log, mpmath finite differences): R(w) is U-shaped, e.g.
  θ = 1/2, a = c = 6: R = 2.5e7 at 1 − w = 1e−12, 0.58 at 1 − w = 1e−2, 0.010 at w = 0, 30 at w = −1;
  ε_P ≥ 1 for 1 − w ≥ 1e−5 and 1 + w ≥ 1e−3 there.

### Step 7. Whole-column certificate W and bug fixes
- L = 4 with cert_core.py, θ ∈ [1/4, 1/2]: stopped by PID after 442,000 boxes had certified only 0.6% of the
  cell θ ∈ [0.4375, 0.5], a, c ∈ [3.5, 4], w ∈ [0.5, 1] (thin layer near w = 1). Leaves kept as
  `runs/L4_hi_partial_stopped.*` (not used).
- New certificate W (PROOF.md Lemma 3.7, `rbox.wcert`): concavity of ε_P in w + derivative bounds of ε_G handle both
  thin layers and the bulk of a full w-column at once. Probes: θ ∈ [0.4375, 0.5], a, c ∈ [3.5, 4]: 22 ms;
  a, c ∈ [7.5, 8]: 28 ms; a ∈ [9.5, 10], c ∈ [0.25, 0.5]: 5 ms. W fails when θ₀ = 0 (factor θ₀ in the layer
  condition) and when min(a, c) is small (layers not thin) — those boxes use P/I/D.
- `test_wcert.py 1 40`: 40/40 W-certified random boxes (a, c ∈ [2, 7.6]), 480 points incl. points inside both
  layers and at 1 − w = 10^{−5..−30}: F ≥ 0 at all (80 digits).
- Driver `cert_v2.py` (W tried first on full columns with min(a₀,c₀) ≥ 2, or max ≥ 3 and min ≥ 0.25; otherwise as
  cert_core). Probe θ ∈ [0.4375, 0.5], L = 4: 13,173 leaves, 14 s, 0 failures. L = 6 (earlier eligibility rule
  min(a₀,c₀) ≥ 2): 2,520 + 70,254 leaves, ~64 s, 0 failures, coverage OK (volume 36) — superseded by the final runs
  below because of the following fixes.
- Bug 1 (`rcore.uf_derivs`): a ball straddling C = 1.5 was re-split forever (Arb's rounded union exceeds 1.5) →
  RecursionError. Bug 2 (`rcore.dd3_point`): the "close nodes" threshold was relative to the largest node, so for
  C ~ e^{20} distant nodes were treated as close and derivatives were evaluated on a huge hull (exception
  "leading term in denominator is not nonzero"). Both only raised exceptions; the drivers treat an exception as
  "not certified" and subdivide, so no unsound certificate could result, but they produced spurious failures at
  a, c ≈ 10, θ ≈ 1/2. Fixed (pairwise relative threshold; split at 1.375 with series/closed forms). After the fix:
  `test_rcore.py 3 40` 0 mismatches, `test_rbox.py 2 100` 400 points 0 violations; W certifies a, c ∈ [11.5, 12].
- All final runs below use the fixed code.

### Step 8. Final runs (RIGOROUS) and final tests
- Further fixes before the final runs (both only made certification fail or slow, never unsound):
  (a) `rbox.zrange` computed the edge minimisers of z in floating point, which could overestimate the exact
  minimum by ~1e−30 relative; replaced by the exact unconstrained edge minima a_v²(1 − w²), c_v²(1 − w²) (valid
  lower bounds) — this one was a genuine rigour gap in the earlier runs, so all runs before this point are
  superseded; (b) W faces were Python floats (1 − 2^{−k} representable only for k ≤ 52); now exact Arb dyadics
  with precision k + 96 for the face evaluations only (raising the precision globally had made the U-series exceed
  the factorial table — an exception, i.e. a spurious failure); (c) the bisection rule now weights the θ-width by
  max(6, 4(1 + c₁)) because b = θc/(1−θ) moves by ~4c·Δθ across a box (W failed on wide θ-boxes for large c).
  Superseded leaf files are kept in `runs/superseded/` and `runs/superseded/attempt2/`.
- **Final L = 20** (`cert_v2.py`, final code):
  `runs/final_L20_lo.txt` (θ ∈ [0, 1/4]): 17,019 leaves (W 6,882, P 8,698, I 1,398, D 41), 49 s;
  `runs/final_L20_hi.txt` (θ ∈ [1/4, 1/2]): 22,803 leaves (W 6,379, P 14,841, I 1,566, D 17), 54 s;
  0 failures. `check_coverage.py 20 …`: total volume 400 = domain volume, 604,335 exact pair tests, 0 overlaps,
  20,000 random points covered: COVERAGE OK (`runs/coverage_final_L20.log`).
  ⇒ Theorem B holds with L_cert = 20: (C), hence TF, for all θ ∈ (0, 1/2] and all 2 × 2 pairs with
  κ(A) ≤ e^{40} ≈ 2.35·10^{17} and κ(B)^{(1−θ)/θ} ≤ e^{40}.
- Final tests (final code): `test_rcore.py 11 40`: 0 mismatches vs 60-digit mpmath, 0 face mismatches vs the
  E-proof's H (`runs/test_rcore_final.log`); `test_rbox.py 7 200`: 800 points in 200 boxes, 0 violations
  (`runs/test_rbox_final.log`); `test_wcert.py 5 60` (a, c ∈ [2, 7.5]): 60/60 W boxes, 720 points, 0 violations
  (`runs/test_wcert_final.log`); `test_wcert.py 6 60 8 19.9` (a, c ∈ [8, 20], 120 digits): 60/60, 720 points,
  0 violations (`runs/test_wcert_final_large.log`).
- File locations: all runs made before fix (a) — the L = 3/4/6 runs, probes and their coverage logs mentioned in
  Steps 5 and 7 — were moved to `runs/superseded/pre_zrange_fix/` (and `runs/superseded/`, `…/attempt2/` for the
  aborted L = 10/20 attempts). Only `runs/final_*` and `runs/coverage_final_*` support Theorem B.
- `check_lemma37.py 1 300` (NUMERICAL, independent of the Arb code): the two derivative bounds of Lemma 3.7,
  −∂_wε_G ≤ 2|V'(C₋)| sinh a sinh b and ∂_wε_G ≤ 4θ²ac Ch'(θ²R_E²), hold at 300 random points (θ ∈ [0.02, 0.5],
  a, c ∈ [0.05, 8]); minimal relative slacks 0.42 and 0.008 (`runs/check_lemma37.log`).
- **Final L = 40** (`cert_v2.py`, final code): `runs/final_L40_lo.txt` (θ ∈ [0, 1/4]): 103,074 leaves (W 33,675,
  P 54,850, I 14,508, D 41), 674 s; `runs/final_L40_hi.txt` (θ ∈ [1/4, 1/2]): 80,347 leaves (W 26,420, P 45,883,
  I 8,027, D 17), 521 s; 0 failures. `check_coverage.py 40 …`: volume 1600 = domain volume, 5,245,022 exact pair
  tests, 0 overlaps, random points covered: COVERAGE OK (20 s, `runs/coverage_final_L40.log`).
  ⇒ Theorem B with L_cert = 40: κ(A) ≤ e^{80} ≈ 5.5·10^{34} and κ(B)^{(1−θ)/θ} ≤ e^{80}.
- Tests extended to the L = 40 range: `test_wcert.py 9 60 20 39.9 160` (a, c ∈ [20, 40], 160 digits): 60/60 W boxes,
  720 points, 0 violations (`runs/test_wcert_final_L40.log`); `test_rbox.py 8 150 39.5 150` (a, c up to 40,
  150 digits): 600 points in 150 boxes, 0 violations (`runs/test_rbox_final_large.log`).

- Far-region scan beyond the certified range (NUMERICAL): `scan_far.py 2 1500 40 150 350` — max(a, c) in [40, 150],
  layers down to 1 ∓ w ≈ 10^{−180}, 350 digits: F < 0 in 0 of 1500 samples; min F = 3.6e−144 (> 0) at
  1 − w = 3.3e−178 (`runs/scan_far_s2_40_150.log`).

### Step 9. Tail lemma for max(a, c) ≥ 40 (PROVED; NUMERICAL checks)
- Reformulation (PROOF.md Lemma 6.1): F ≥ 0 if ε_P ≥ 1, or if Y_G ≤ ½ min(1, θψ(R_E)) ε_P, ψ(R) = R/(1 − e^{−R}).
- Two 3-parameter sufficient conditions, each giving F ≥ 0 for every w:
  (W) explicit faces w = ±(1 − 1/ε_P(0)) + slope bounds in the two layers: conditions (L+), (L−) (Lemma 6.3);
  (T) a condition uniform in w from the smallest divided-difference nodes (Lemma 6.4).
- `tail_explore.py` (NUMERICAL map, θ ∈ {0.001, …, 0.5}, max(a, c) ∈ [40, 2000], min from 0.01 to max): at every
  grid point (W) or (T) holds; the largest (L+) ratio is 0.0064, at θ = 1/2, a = c = 40 (the direction a = b = c where
  the exponentials cancel); (W) holds even for min(a, c) = 0.01, (T) for min(a, c) up to ~ max/6.
- Analytic proof (PROOF.md Theorem 6.5): F2 = {min ≥ 1}: (W) with E₀ ≥ (½ − e^{−40/41})e^{a+c}, P₊ ≥ e^{a+c}((1 − 3·10⁻¹⁶)h − ½),
  and e^{−θR₁}K₊ ≤ e^{a+c}θ(4.47 + 2Δ)e^{−Δ}, Δ = |a − b| + (c − b), from the integral representation (M2) of V' (the
  exponents X_A, X_B reduce exactly to −Δ or less); F1 = {0 < min < 1}: (T) with the analogous bounds for V''.
- First runs of `tail_check.py` (v0) flagged only checker artefacts: (i) mp.quad over λ ∈ (0, ∞) and mp.diff at
  C ≈ e^{270} were inaccurate → quadrature in s = log λ with breakpoints at ±d; (ii) for d ≳ 40 the closed form of
  U_t'' and the quadrature disagreed, which I attributed to cancellation in the closed form (wrong, see the correction
  below) → v1 took the quadrature of (M2) as reference for V'' and compared the closed form only for d < 30;
  (iii) RHS_T ≥ min(1, θt)(t − 1)e^t/(4t³) is strict analytically but the gap is a relative e^{−2t} below working
  precision → relative tolerance 10⁻⁶⁰. v1 runs, seeds 2 and 3, 300 points each (F1: 111 + 92, F2: 189 + 208):
  no violation, about 8 min each (`runs/superseded/tail_check_v1/`; v0 logs in `runs/superseded/tail_check_old/`).
- Correction to (ii). At t = 0.3, d = 100 three independent evaluations of U_t''(cosh d) agree to 30 digits: the closed
  form (at 80 and at 400 digits), numerical d-derivatives of sinh(td)/sinh d, and numerical C-derivatives of
  sinh(t acosh C)/sinh(acosh C) (400 digits). The 60-subinterval quadrature is off by 1.4·10⁻⁷ (relative) there, and
  agrees to 3·10⁻¹¹ with subintervals of length 1.5. So the closed form is accurate and the quadrature was the less
  accurate side. The v1 verdicts stand (every checked inequality has a margin far above 10⁻⁶), but the checker was
  rewritten:
- `tail_check.py` v2: exact reference values from closed forms, via s_θI_a = |U_θ'(C₋)|, s_θI_b = |U_{1−θ}'(C₋)|,
  s_θII_a = U_θ''(C₋), s_θII_b = U_{1−θ}''(C₋) (the integral ∫λ^{−t}/(1 + 2Cλ + λ²)dλ is even in t, by λ → 1/λ);
  quadrature (subintervals ≤ 3) at every fifth point as a cross-check, tolerance 10⁻⁶; 45 fixed corner points
  (θ ∈ {1/2, 1/4, 10⁻⁴} × {(40, 40), (40, 1), (1, 40), (300, 300), (300, 1), (1, 300), (40, 39), (39, 40), (41, 40),
  (40, 0.999), (0.999, 40), (40, 10⁻⁶), (10⁻⁶, 40), (300, 0.5), (0.5, 300)}) before the random points; each
  intermediate inequality is checked separately (both forms of each bound in 6.2(d), the exponent identities for
  X_A, X_B, the sub-cases of Step 4, both bounds of Step 5, the intermediate bounds of the three F1 cases) and the
  largest ratio left/right of each is printed. The first launch grew to 0.7 GB per process within 2 minutes (mpmath
  caches the transformed quadrature nodes of every new interval); stopped by PID and relaunched with the cache cleared
  after each point.
- `tail_constants.py` (RIGOROUS): every numerical constant of Section 6 in Arb (200 bits) or exact rationals, with the
  remaining elementary facts listed with their one-line proofs. It found one slip in the text: in F1, case b ≥ 1, the
  constant is 1.3811[cosh(1)(e³/4)(5.49/2 + 8) + 5.575·e³/2] = 192.31…, not ≤ 192.3 as written; corrected to 193
  (the final step 193 ≤ 0.951(t − 1)e^t/(4t) at t = 39 has an enormous margin). Wording fix in Step 5:
  (1 − e^{−80})shc(37) − 1 instead of shc(37) − 1. (The script's first version reported three FAILs that were
  artefacts of the script: interval dependency in sin(πθ)/π − θ and in θ/(1−θ) − 2θ, and the decimal identity
  5.49 + 22.3 = 27.79 tested with balls → replaced by the one-line analytic facts and exact rationals.)
  Result: all claims verified (`runs/tail_constants.log`).
- `tail_check.py` v2, first full launch (seeds 2, 3; 2000 random + 45 corner points each): two VIOLATION lines for
  δ ≤ 2h/E₀, at (θ, a, c) = (0.2416, 180.90, 2.805) and (0.5, 181.84, 1.422), ratios 1.30 and 1.07. Checker artefact:
  δ = (a + c) − R₁ ≈ ac e^{−(a+c)}/(η(a + c)) is the difference of two numbers that agree to about 80 digits when
  a + c ≈ 180, so at 80 digits it is rounding noise. With E₀, R₁, R₂, δ computed at 120 + 0.45(a + c) digits, both
  points give δ/(2h/E₀) = 0.5, as the cancellation-free identity δ = 2ac/(E₀(a + c + R₁)) predicts (agreement
  10⁻¹²³). Logs in `runs/superseded/tail_check_v2_delta_precision/` (all other inequalities passed there).
- The label "e^{a+c}(½ − e^{−h}) ≥ η₀e^{a+c} ≥ 1" covered only the first inequality; added explicit checks
  η₀e^{a+c} ≥ 1 and E₀ ≥ 1 to `tail_check.py`, and η₀e^{41} ≥ 1 to `tail_constants.py` (39 claims, all verified),
  and reran both seeds (previous logs, identical otherwise, in `runs/superseded/tail_check_v2_before_E0_check/`).
- `tail_check.py` v2 final runs (`runs/tail_check_s2.log`, `runs/tail_check_s3.log`; 10 min each, two processes):
  seed 2: F1 715, F2 1330 points; seed 3: F1 657, F2 1388 points (45 corner points each included);
  **violations: 0 and 0**. Largest ratios left/right: (L+) 0.00641 (θ = ½, a = c = 40); (L−) 4.3·10⁻¹⁶; (T) 4.7·10⁻¹⁶
  (θ = ½, a = 40, c = 0.999); F1 constants: 776-bound 0.99927, 193-bound 0.99643, 258-bound 4.1·10⁻⁵; the 6.2(d) bounds
  up to 0.99997 (II_a at θ = 10⁻⁴, d ≈ 300); δ ≤ 2h/E₀: 0.5; Step 4(ii) m ≥ 20 (h ≥ 40/3): 0.997. Quadrature vs
  closed forms: largest relative deviation 1.5·10⁻⁸.
- `tail_explore.py` rerun with the closed form of U_t'' (it used mp.diff, inaccurate at large C): worst
  min(ratio_T, ratio_W) over the grid 0.00641 at θ = ½, a = c = 40 (unchanged); largest (T) ratio on the part of the
  grid with min(a, c) < 1: 3.3·10⁻¹⁷ (θ = ½, a = 40, c = 0.4) (`runs/tail_explore.log`, 1 s). The earlier figure
  "(T) ratios ≤ 10⁻¹⁰" came from the inaccurate mp.diff values and is withdrawn.
- Direct far-region scan extended (NUMERICAL, end-to-end F from the closed forms of `hyp.py`):
  `scan_far.py 4 3000 150 300 520` — max(a, c) ∈ [150, 300] (min(a, c) log-uniform from 10⁻⁴ or within 20% of the
  max, so a + c up to 660), θ including 1/2 and near 0, w in the bulk and in layers 1 ∓ w = 10^{−k}, k ≤ 360:
  3000 samples, F < 0 in 0; min R = 7.2e−8 at θ = 0.499994, a = 328, c = 292, w = −0.097; min F = 4.9e−231 in the
  layer 1 + w = 9.5e−359. Identical output at 760 digits. About 7 s (`runs/scan_far_s4_150_300.log`).

## Status at the end of the day
- PROVED (with a RIGOROUS computer-assisted part): **TF holds for every pair of 2 × 2 positive definite matrices and
  every θ ∈ (0, 1)** (PROOF.md Main Theorem, Section 6A): Theorem A (reduction to (C)) + Theorem B (RIGOROUS, F ≥ 0 for
  a, c ≤ 40) + Theorem 6.5 (PROVED, F ≥ 0 for max(a, c) ≥ 40).
- Also PROVED: Proposition C, Lemmas 3.1–3.7, 6.1–6.4. The numerical constants of Section 6 are checked in Arb /
  exact rationals (`tail_constants.py`, RIGOROUS; Step 9).
- Dependencies: Heinävaara positivity, Ando–Hiai, note 09 Lemma 1 / Tool 0.3, and (for the 58 D-boxes only) note 09
  Theorem 1 with the E-proof's H ≥ 0.
- NUMERICAL cross-checks: see Steps 3, 6, 8, 9.
