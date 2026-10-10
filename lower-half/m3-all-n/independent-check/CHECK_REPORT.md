# Independent check of Theorem B (OQP 40, case (n,3), all n ≥ 37 and the limit kernel)

Ansh Mishra, Aryan Senthilkumar. Everything is in this folder (`independent-check/`). No original file was edited, and
no commit was made.

## Verdict: CONFIRMED WITH FIXES

- Own code now verifies every region of the computer-assisted part, for every eps = 1/n in [0, 1/37] and also at
  eps = 0: 605,334 boxes, 0 failures.
- `coverage_check.py` checks mechanically that these regions cover the whole quadrant a, d ≥ 0, including a → ∞ and
  d → ∞. No gaps.
- The proof as filed had one real gap (P1 below). Corrected re-runs close it. No check anywhere found a failing box or
  a counterexample.

## Coverage verified by own code

Here a = n log s, d = n log(t/s), b = a + d, and x0, x1 are the ends of each a-strip.

| Region | Run | Chart / form | Boxes |
|---|---|---|---|
| a ∈ [3,250], d ∈ [0,512] | 19 runs (listed below) | (a,d) jets with centre/box tightening; mixed form for d ≤ 15/4, scaled ν-forms above | 540,878 |
| corner a, b ≤ 1/4 | S0 | Taylor model in a, b-shift of order 10 | 1 |
| a ∈ [0,3], b ∈ [1/4, x0+4] | S1 | direct form, exact division by a² via series shift | 15,468 |
| a ∈ [0,3], b ∈ [x1+15/4, 8] | S2 | ν-form, box Taylor models | 11,569 |
| a ∈ [0,3], b ∈ [15/2, 515] | S3 | ν-form | 15,001 |
| a ∈ [0,3], d ≥ 512 (to ∞) | T2 | w = 1/d chart, G = log(F/a) | 256 |
| a ∈ [3,250], d ≥ 512 (to ∞) | T1 | w = 1/d chart | 2,368 |
| a ≥ 250, d ≥ 512 (both to ∞) | T3 | (m_a, w) chart | 64 |
| a ≥ 250 (to ∞), d ∈ [0,512] | T7 | m_a chart, mean value in (d, eps) | 19,729 |
| same region, second pass | T5 + T6 | earlier version of the T7 code | 75,794 |
| **Total, one pass per region** | | | **605,334** |

The 19 core runs (a-range × d-range, boxes):
- d up to 15/4: W1 [3,8]×[0,3] 34,104; V10 [8,64]×[0,3] 86,016; V6 [14,32]×[7/4,5/2] 13,824 (inside V10);
  W4 [3,16]×[3,15/4] 8,873; V11 [16,64]×[3,15/4] 18,432; W2 [64,250]×[0,15/4] 44,640.
- d from 15/4 to 25: W5 [3,16]×[15/4,16] 42,866; W3 [16,64]×[15/4,8] 9,406; W6 [64,250]×[15/4,8] 45,129;
  V8 [16,64]×[8,16] 13,445; V5 [50,120]×[8,25] 38,080; W7 [120,250]×[8,16] 16,696.
- d from 16 to 64: V9 [3,16]×[16,64] 6,726; V2 [16,50]×[16,64] 13,056; R1 [50,120]×[25,60] 19,600;
  V12 [50,120]×[60,64] 2,240; V3 [120,250]×[16,64] 49,978.
- d from 64 to 512: V4 [3,64]×[64,512] 31,085; V7 [64,250]×[64,512] 46,682.

Self-tests against an own reference built from the definitions (mpmath): 966 comparisons of certified bounds against
true values, 0 violations (iv_selftest 438, iv_selftest2 192, iv_test_tail3 63, iv_test_strip_nu 273, the last for
corner and ν-form strip boxes). The eps-derivatives of the a-tail jets match finite differences to 1.4e-32.

## Problems in the original proof

**P1. Proof gap (serious, fixed).**
- `tb_arb.S_of` expands S(x; eps) in eps only to first order, so the eps² slots of the MT2 dual jets are exactly 0. Their
  true values are 0.004 to 0.17 (`test_S_eps2.py`).
- `tighten()` uses those slots to enclose the eps¹ slots. So all 10 `tb_bb.py --dual mixed3` runs were unjustified: the
  C2 d-strips, and C1 for 3 ≤ d ≤ 15/4.
- It never produced an actual failure: 0 violations in 11,520 gradient spot-checks.
- Fix: `patch_S.py`. All 10 regions were re-run with the corrected S and verified: 301,380 boxes (`rerun_mixed3_fixed.log`).

**P2. Reproducibility (moderate).**
- The S3 log came from an older driver and library. The documented command, run with the current `tb_sx_run.py`, leaves a
  gap below b = x1 + 15/2. A re-run of S3 with the current code on the grid actually used is verified
  (`rerun_S3_const.log`).
- `tb_tail2_A64.log` also predates the current `tb_tail2.py`; the current code re-verifies that region.

**P3. Minor.**
- Disjoint ball intersections are silently ignored instead of raising an error.
- Some tail bounds pass through `float()`, which can round down by one ulp (harmless).
- A few code comments are wrong.

## Other independent checks

- **Mathematics:** re-derived by hand Proposition 6′, Lemma 4 (smooth version), (B0)/(B1), F(s,s) = 1, the design at
  d → 0, and the closed forms (F1)–(F5). The Lemma T/T′ constants were checked numerically. No error found.
- **Random points:** 8,000 points with n from 37 to 10⁶ plus the limit kernel; no violation. The minima match the
  reported margins, and the original point formulas agree with the own reference to ≤ 1e-34.
- **The original enclosures:** 25,044 soundness spot-checks, 0 violations. Seven original logs reproduce exactly.

## The S_of question for the strip code

- The strip code of this check (`iv_as.py`) does not use `tb_arb.S_of`. It uses its own S-series
  (`iv_small.S_coeffs`): every eps-order comes from the exact polynomials s_k(eps), with one extra order for wide eps balls.
- The original strip code is not affected by P1:
  - `tb_sx.py` has its own S (`s_coeffs_q`/`S_ts`, eps-orders up to ke plus one more for balls);
  - `tb_sx_dtail.py` calls `tb_arb.S_of`, but only with (a, b)-jets and a plain eps ball, where S is evaluated directly
    on the ball.

## Problems found in the code of this check (all fixed; none caused a false acceptance)

- **a-tail atom bound.** It used Re b′ ≥ a − 1 where only a − 2 holds. Two minor bounds were too small by at most a factor
  of e, which stays inside the ×10 safety margin. The overall maximum, set by the eps-free Φ̂(b)e^{−μa} term, did not
  change. Fixed before T5–T7.
- **eps-derivative bound for the atoms.** A Cauchy estimate on a complex eps-disc of radius 1/(4(a+d+2)), written out in
  `iv_atoms._a_tail_atoms`.
- **m_a = ν_a − eps by subtraction.** With wide eps balls this lost information. It only cost speed: the old a-tail run T4
  stalled and was stopped. It is now computed as m(a+h) = m/(m h φ(h eps) + e^{h eps}).
- **Earlier bugs**, all of which failed safely, and the affected runs were redone: the Φ branch threshold, log of a ball
  containing 0, S with a ball eps, and the double-tail a_min after eps splits.

## Remaining caveats

1. **Same reduction.** This check verifies the same sufficient conditions (F > 0 and L1, L2, L3 > 0 for λ = 7/100,
   η = 7/10). The reduction to these conditions was checked by hand, not machine-checked.
2. **Shared definitions.** The formulas here are own re-derivations of the same identities, and the reference implements
   the definitions as written in RESULTS.md §8 and `04-lower-half-new-cases.md`. A mistake in those written definitions
   would be shared.
3. **Same strategy in the strip.** The strip code is independent but uses the same idea as tb_sx (Taylor models in a with
   exact division by a²).
4. **Hand-derived atom bounds.** The exponentially small tail terms are bounded by own Cauchy estimates with a ×10
   factor. They are at most 6e-16 in every run, far below the margins. The eps-derivative estimate is new and checked
   only here.
5. **Software trust.** Arb (python-flint) and mpmath. A few constants pass through `float()`; these are covered by safety
   factors or nudged upward.
6. **Scope.** n ≤ 36 is outside Theorem B and was not checked here; those cases have their own exact per-n verification.
7. **Not an external review.** This is one independent computational check, not an external referee report.

## Reproduction

Use the venv Python with OMP_NUM_THREADS=1. The first line of each log records its region and settings; the launch
commands are in `slotmgr*.sh`. Examples:
- T7: `iv_tail3_run.py 0 512 512 2 8 0 8`
- S0: `iv_as_run.py corner`
- S1: `iv_as_run.py direct 0 3 12 1/4 4 1/8 4`
- S2: `iv_as_run.py nu 0 3 24 15/4 8 64 4 box`
- S3: `iv_as_run.py nuc 0 3 6 15/2 515 16 4`
- T1, T2, T3: `iv_tail_run.py farreg 3 250 62 4 8`, `farstrip 0 3 8 4 8`, `double 2 4 8`
- core runs: `iv_bb2.py <form> A0 A1 D0 D1 NA ND 8`

`iv_T4_atail_stopped_superseded.log` is the stopped run that T7 replaces.
