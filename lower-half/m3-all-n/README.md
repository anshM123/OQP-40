# The lower half of OQP 40 at (n, 3) and (3, n) for every n

Ansh Mishra, Aryan Senthilkumar. Computer-assisted; independently checked; not yet reviewed by outside experts.

**Result.** For every n ≥ 1 and all positive definite A, B of any size, A_{n,3}(A, B) ≥ Tr((A^{n/3} B)^3)
(Conjecture F at (n, 3)). Hence the lower half of OQP 40 holds at (n, 3) and (3, n) for every n, and so whenever
min(n, m) ≤ 3.
- n ≤ 36: Theorem 5 of [`../../math/05-lower-half-m3.md`](../../math/05-lower-half-m3.md), an exact computation for each n
  (`../m3/`).
- n ≥ 37: Theorem B of [`THEOREM.md`](THEOREM.md), one computation for all n ≥ 37 at once. It uses a modified certificate
  (Proposition 6' with a Gaussian design) and verifies the four conditions of Lemma 4 of
  [`04-lower-half-new-cases.md`](../../math/04-lower-half-new-cases.md) in ball arithmetic, with eps = 1/n as an
  interval variable in [0, 1/37].

**Two implementations.**
- The first is the `tb_*.py` scripts in this folder.
- The second is [`independent-check/`](independent-check/): separately written code, with its own formulas, jets,
  enclosures and charts. It re-verifies every region: 605,334 boxes, 0 failures.
  - `coverage_check.py` checks mechanically that the regions cover the whole domain.
  - Its report is [`independent-check/CHECK_REPORT.md`](independent-check/CHECK_REPORT.md).

**Which logs of the first implementation count.**
- Valid as they stand (each ends with `RESULT: REGION VERIFIED`):
  - `tb_core_A1.log`, `tb_core_A2a_hi.log`, `tb_core_A2a_lo1.log`, `tb_core_A2b.log`, `tb_core_far.log`,
    `tb_tail2_A64_far.log`, `tb_ddouble.log`, `tb_dtail.log`;
  - for the strip: `tb_sx_corner.log`, `tb_sx_direct.log`, `tb_sx_nu_low_a.log`, `tb_sx_nu_low_b.log`, `tb_sx_dtail.log`.
- **Superseded, because the independent check found a gap.** The ten `--dual mixed3` runs are `tb_dstrip_*.log`,
  `tb_core_lo2_16_40.log` and `tb_core_lo2_40_64.log`. They relied on an eps-expansion in `tb_arb.S_of` that was
  truncated at first order, so they are not valid as filed. The same regions were re-run with the corrected expansion
  (`independent-check/patch_S.py`) and verified: `independent-check/rerun_mixed3_fixed.log`, 301,380 boxes.
- **Superseded for reproducibility.**
  - `tb_sx_nu.log` (S3) came from an older driver; see `independent-check/rerun_S3_const.log`.
  - `tb_tail2_A64.log` came from an older `tb_tail2.py`; see `independent-check/rerun_orig/tb_tail2_A64.log`.
- `*_stopped*.log` and `*_failed1.log` are development runs, kept for the record. They are not part of the proof.

In every region the verdict also rests on the independent implementation, which agrees.

**Reproduce.** Section 8.7 of `THEOREM.md` lists the commands of the first implementation. The end of
`independent-check/CHECK_REPORT.md` gives those of the second. You need Python 3 with python-flint, mpmath and numpy, and
`OMP_NUM_THREADS=1`. The full set of runs takes on the order of a day of CPU time; single regions take minutes to hours.

**Caveats** (from the check report).
- Both implementations verify the same sufficient conditions, and the reduction to them is checked by hand.
- The definitions are taken as written in the notes.
- The tiny exponential tail terms use hand-derived Cauchy bounds with large safety factors.
- All interval arithmetic relies on Arb (python-flint).
- This is an internal independent check, not an external review.
