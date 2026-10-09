import OQP40.Thm33

/-!
# Axioms used by Theorem 1 of the lower-half note (the case n = m = 3)

Authors: Ansh Mishra, Aryan Senthilkumar. License: MIT.

Every theorem below depends only on `propext`, `Classical.choice` and `Quot.sound`.
Run from `lean/` after building: `lake env lean OQP40/AxiomsThm33.lean`.
-/

/- Theorem 1 (`OQP40/Thm33.lean`). -/
#print axioms OpenQuantumProblem40.three_mul_trace_mul_cube_le
#print axioms OpenQuantumProblem40.trace_mul_cube_le_wordAverage
#print axioms OpenQuantumProblem40.wordAverage_three_three
#print axioms OpenQuantumProblem40.trace_sq_sq_mul_re
#print axioms OpenQuantumProblem40.Thm33.core_diag
#print axioms OpenQuantumProblem40.Thm33.sum_kappa_eq

/- The finite inequality, the certificate and Lemma 2 (`OQP40/Thm33Reduction.lean`). -/
#print axioms OpenQuantumProblem40.Thm33.kernel_sum_nonneg
#print axioms OpenQuantumProblem40.Thm33.kernel_sum_nonneg_of_pos
#print axioms OpenQuantumProblem40.Thm33.share_add_share_add_share
#print axioms OpenQuantumProblem40.Thm33.sum_kappa_eq_three_mul_sum_share
#print axioms OpenQuantumProblem40.Thm33.psdForm_reT
#print axioms OpenQuantumProblem40.Thm33.sum_mul_share_nonneg
#print axioms OpenQuantumProblem40.Thm33.above_eq

/- Lemma 3 at the apex `1` (`OQP40/Thm33Kernel.lean`). -/
#print axioms OpenQuantumProblem40.Thm33.kerE_psd
#print axioms OpenQuantumProblem40.Thm33.intervalHyp_kerF

/- The four sign conditions (`OQP40/Thm33Signs.lean`). -/
#print axioms OpenQuantumProblem40.Thm33.kerE_nonneg
#print axioms OpenQuantumProblem40.Thm33.cond1
#print axioms OpenQuantumProblem40.Thm33.cond2
#print axioms OpenQuantumProblem40.Thm33.cond3

/- Lemma 4, interval mixtures (`OQP40/Thm33Interval.lean`). -/
#print axioms OpenQuantumProblem40.Thm33.interval_mixture
