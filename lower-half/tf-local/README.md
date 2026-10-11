# Conjecture TF in the two perturbative regimes (code and logs)

These are the computations behind [`../../math/09-tf-local.md`](../../math/09-tf-local.md):
- **Theorem 1.** TF to second order at commuting pairs.
- **Theorem 2.** TF near the identity.
- **Dead ends.** Monotonicity statements that are false; they are recorded in note 08, Section 5.

Requirements: Python 3 with numpy, scipy, mpmath, sympy, python-flint (Arb) and cvxpy. Run each script from its own
folder with `OMP_NUM_THREADS=1`.

## `E-proof/`: the inequality E ≥ 0 (last step of Theorem 1)

The proof is computer-assisted: analytic arguments plus rigorous ball arithmetic. Read [`E-proof/PROOF.md`](E-proof/PROOF.md)
first; `E-proof/LOG.md` is the lab notebook.

| File | What it does |
|---|---|
| `ecore.py` | Arb formulas for H = E/(θx²y²) and its parts; rigorous enclosures of φ, ψ and the second divided difference of exp |
| `regionB.py` | interval boxes with adaptive bisection on [−10, 10]² (H > 0 on each box) |
| `regionA2.py`, `regionA_run.py` | Taylor models near the degenerate corner; each sub-box gets H > 0 or ∂H/∂s > 0 |
| `far_region.py` | the constants of the analytic far-region bounds (Arb, asserts) |
| `check_coverage.py` | mechanical check that the certified boxes cover the compact region |
| `test_ecore.py`, `verify_closed_form.py` | sanity checks against independent mpmath code |
| `run_final_A.sh`, `run_final_B.sh` | the definitive runs; logs in `runs/` |

How to reproduce (about 15 minutes):
```bash
sh run_final_A.sh
sh run_final_B.sh
python check_coverage.py runs/A_final_0.json runs/A_final_1.json runs/B_final_lo.json runs/B_final_hi.json
```

Results:
- **Region A′:** 318 boxes, 326 certified leaves, 0 failures.
- **Region B:** 167,626 boxes, 0 failures.
- **Coverage:** OK.

**Our re-run** from these scripts is in `rerun/`; it gives the same verdicts.

**Independent checks** (`independent-checks/`, written from the statements only):

| Script | What it checks | Log |
|---|---|---|
| `check_lemmas.py` | the analytic identities of PROOF.md (closed form vs integral, Lemmas 2.1, 2.2, 2.4, Theorem 3.1, the corner value) at 60 digits | `logs/check_lemmas.log` |
| `soundness_B.py` | random region-B boxes: the certified lower bound never exceeds the sampled minimum of H | `logs/soundness_B.log` |
| `soundness_A.py` | Taylor models: the torus bound M′ dominates the sampled values of H, and the certified errors dominate the actual polynomial errors | `logs/soundness_A.log` |
| `gm_bch.py` | the geometric-mean expansion used in Theorem 2.3 | `logs/gm_bch.log` |

## `second-order/`: the 2 × 2 second-order formula and the closed form of E

| Script | What it does | Log |
|---|---|---|
| `bloch_second_order.py` | Lemma 2 of note 09 (second variation of the Weyl pairing) from the exact Bloch-sphere formula, for smooth test functions | `logs/bloch_second_order.log` |
| `bloch_kernel_check.py` | the same for the TF kernel itself (only C^{1,1}): Richardson-extrapolated second differences | `logs/bloch_kernel_check.log` |
| `t2_explicit.py`, `tf_second_order.py` | the explicit second-order tail T₂ and its moments against ε → 0 extrapolations of exact word averages | |
| `e_coordered.py`, `e_series.py`, `e_landscape.py` | the closed form of E, its corner series (sympy), and grids | |

## `near-identity/`: Theorem 2

| Script | What it checks | Log |
|---|---|---|
| `near_id_check.py` | p − L ≈ nm(n+m−1)κh⁴/24 against exact word averages (d = 2, 3, 4) | `logs/near_id_check.log` |
| `m4_check.py` | the h⁴ coefficient (13 digits) and the fourth moment of the first-order deviation (9 digits) | `logs/m4_check.log` |
| `bottom_formula.py` | the θ = 1/2 bottom value (h⁵/48)Tr((S − s₁)K), d = 2, …, 5 | `logs/bottom_formula.log` |
| `tf2x2_sphere.py` | exact TF tails for 2 × 2 pairs via the Bloch-sphere formula (checked against word averages) | (module) |
| `ni_interior_check.py` | T(hγ)/(h³τ(γ)) → 1 inside the cluster, computed directly | `logs/ni_interior_check.log` |
| `tf2x2_scan.py` | a global scan of TF for 2 × 2 pairs with the exact formula (no negative value) | `logs/tf2x2_scan_s21.log` |

## `dead-ends/`: monotonicity statements that are false

| Script | Statement tested | Result |
|---|---|---|
| `mono_test.py`, `bmv_p_test*.py` | p_{n,m} along the Z-preserving family is nondecreasing / a positive Laplace transform | holds in random tests and Hankel tests |
| `bmvp_hunt2.py`, `verify_found.py` | the same, adversarially | **false** for d = 3 (log-convexity and monotonicity fail), confirmed at 50 digits (`logs/verify_found.log`) |
| `kernel_vec_test.py` | ⟨v, e^{H+λK}v⟩ with Kv = 0 is a positive Laplace transform (Hankel test) | consistent in the tests; not needed |
| `pwm_hunt.py`, `verify_pwm.py` | p_{n,m}(A^h, B^h)/L_{n,m}(A^h, B^h) is nondecreasing in h | **false** for d = 3, even at (n, m) = (3, 1), confirmed at 50 digits (`logs/verify_pwm.log`) |

In every counterexample above the lower half itself still holds.
