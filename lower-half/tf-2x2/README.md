# Conjecture TF for all 2 × 2 pairs (code, leaf lists and logs)

These are the computations behind [`../../math/10-tf-2x2.md`](../../math/10-tf-2x2.md), which proves Conjecture TF
for every 2 × 2 pair:
- **Theorem 1** (exact reduction of TF(2 × 2) to inequality (C)): analytic. The scripts here check its ingredients
  numerically.
- **Theorem 3** (inequality (C) for a, c ≤ 40, i.e. condition numbers up to e^{80}): computer-assisted. The proof is
  analytic lemmas plus rigorous ball arithmetic.
- **Theorem 4** (inequality (C) for max(a, c) ≥ 40): analytic. The scripts here verify its constants in ball arithmetic
  and test every intermediate inequality.
- **d ≥ 3:** the computation showing that the lens lemma fails.

Read [`PROOF.md`](PROOF.md) first. Its Theorem A, Proposition C, Theorem B and Theorem 6.5 are Theorem 1,
Proposition 2, Theorem 3 and Theorem 4 of note 10. [`LOG.md`](LOG.md) is the lab notebook.

Requirements: Python 3 with numpy, scipy, mpmath and python-flint (Arb). Run each script from its own folder with
`OMP_NUM_THREADS=1`. Some scripts import modules from the sibling folders `../tf-local/` and `../general-tjsm/`.

## The certification (Theorem 3)

| File | What it does |
|---|---|
| `rcore.py` | rigorous point and ball evaluation of the normalised margin R (divided differences of Ch and U_t, Arb) |
| `rbox.py` | rigorous box bounds: certificates P, I, F, the w-derivative bound D, and the thin-layer certificate W |
| `cert_v2.py` | adaptive bisection of [θ₀, θ₁] × [0, L]² × [−1, 1]; writes one line per certified leaf |
| `check_coverage.py` | exact rational check that the leaves are certified, disjoint and fill the domain |
| `test_rcore.py`, `test_rbox.py`, `test_wcert.py`, `check_lemma37.py` | tests against independent mpmath code and the E-proof |
| `hyp.py`, `cf2x2.py` | high-precision references (hyperbolic closed forms; matrix closed forms) |

How to reproduce Theorem 3 (about 20 minutes on two cores):
```bash
python cert_v2.py 0.0 0.25 40.0 runs/final_L40_lo.txt
python cert_v2.py 0.25 0.5 40.0 runs/final_L40_hi.txt
python check_coverage.py 40 runs/final_L40_lo.txt runs/final_L40_hi.txt
```

Results (`runs/`):
- **θ ∈ [0, 1/4]:** 103,074 leaves (W 33,675, P 54,850, I 14,508, D 41), 0 failures.
- **θ ∈ [1/4, 1/2]:** 80,347 leaves (W 26,420, P 45,883, I 8,027, D 17), 0 failures.
- **Coverage:** total volume 1600 equals the domain volume, 5,245,022 exact pair tests with 0 overlaps.
- **Smaller run:** an independent run with a, c ≤ 20 (`runs/final_L20_*`, 39,822 leaves) certifies that subregion.

**Our re-run** of the a, c ≤ 20 certification from the published scripts is in `rerun/`. It gives identical leaf
counts and coverage OK. The same folder has our re-runs of `tail_constants.py` and of seed 2 of `tail_check.py`; their
logs are identical to those in `runs/`.

## The far region (Theorem 4)

| File | What it does | Command and log |
|---|---|---|
| `tail_constants.py` | verifies all 39 numerical constants of the proof (PROOF.md, Section 6) in Arb ball arithmetic or exact rationals; prints ALL CONSTANTS VERIFIED | `python tail_constants.py`, `runs/tail_constants.log` |
| `tail_check.py` | evaluates every intermediate inequality of the proof at random far-region points (80 digits); about 10 minutes per seed | `python tail_check.py 2 2000` (and seed 3), `runs/tail_check_s2.log`, `runs/tail_check_s3.log` |
| `tail_explore.py` | maps the ratios in the sufficient conditions (L±) and (T) on a grid up to max(a, c) = 2000 | `python tail_explore.py`, `runs/tail_explore.log` |
| `scan_far.py` | F itself beyond max(a, c) = 40, including thin layers at w = ±1 | `python scan_far.py 4 3000 150 300 520`, `runs/scan_far_s4_150_300.log`; earlier scans `runs/scan_far_s1.log`, `runs/scan_far_s2_40_150.log` |

## Numerical checks of Theorem 1

| File | What it checks |
|---|---|
| `explore_shape.py`, `check_structure.py` | the closed form below v_min and the lens lemma, against the exact Bloch-sphere tail |
| `explore_hyp.py`, `explore_C.py`, `explore_w.py`, `explore_gaps.py` | closed forms and the landscape of (C) |

## Independent checks (`independent-checks/`, written from the statements only)

| Script | What it checks | Log |
|---|---|---|
| `check_thmA.py` | for random pairs, the exact Bloch-sphere tail at u* = min(u_c, v_min) equals the closed form (1.3); the grid minimum of T on [ζ₁, ζ₂] is at u* or at ζ₂, where T ≥ 0 trivially | `logs/check_thmA.log` |
| `soundness_sample.py` | 300 random points in random certified leaves of the final runs, including thin layers down to 1 − \|w\| = 10⁻³⁰; (C) evaluated from the matrices at 80 digits | `logs/soundness_sample.log` |
| `hyperbolic_form.py` | the hyperbolic-triangle form of (C) | `logs/hyperbolic_form.log` |
| `zeta2_vmin.py` | the ordering ζ₁ ≤ v_min ≤ ζ₂ (proved in note 10, Section 0) on random pairs | `logs/zeta2_vmin.log` |
| `tail_independent.py` | Theorem 4: (L+), (L−), (T), the slope facts and F itself at random far-region points, with exact closed forms for V′ and V″ (150 digits) | `logs/tail_independent_s1.log`, `logs/tail_independent_s2.log` |

## `general-d/`: the lens lemma fails for d ≥ 3

`lens_general.py` computes Λ(u) = Π^θ((u, ∞)) for random 3 × 3 and 4 × 4 pairs, from the density of the continuous part
and the singular points (module `../general-tjsm/tjsm.py`). It compares Λ(u) with #{i : ζ_i > u}. Log:
`general-d/logs/lens_general.log`.
