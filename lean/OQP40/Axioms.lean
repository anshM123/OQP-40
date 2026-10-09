import OQP40.Pinching

/-!
# Axioms used by the OQP 40 results

Authors: Ansh Mishra, Aryan Senthilkumar. License: MIT.

Every theorem below depends only on `propext`, `Classical.choice` and `Quot.sound`.
Run from `lean/` after building: `lake env lean OQP40/Axioms.lean`.
-/

/- The answer to OQP 40 and the Cha-Lee counterexample (`OQP40/Statement.lean`). -/
#print axioms OpenQuantumProblem40.refinedBMV
#print axioms OpenQuantumProblem40.not_refinedBMV
#print axioms OpenQuantumProblem40.not_upperHalf
#print axioms OpenQuantumProblem40.chaLee_counterexample
#print axioms OpenQuantumProblem40.chaLee_perturbed_counterexample
#print axioms OpenQuantumProblem40.chaLee_trace
#print axioms OpenQuantumProblem40.chaLee_wordAverage

/- Checks of the definitions (`OQP40/Statement.lean`). -/
#print axioms OpenQuantumProblem40.wordSum_succ_succ
#print axioms OpenQuantumProblem40.wordAverage_of_commute
#print axioms OpenQuantumProblem40.wordAverage_one_one
#print axioms OpenQuantumProblem40.wordAverage_im
#print axioms OpenQuantumProblem40.trace_pow_mul_pow_im
#print axioms OpenQuantumProblem40.trace_exp_log_im
#print axioms OpenQuantumProblem40.chaLeeA_add_posDef
#print axioms OpenQuantumProblem40.chaLeeB_add_posDef

/- The pinching inequality for all word lengths (`OQP40/Pinching.lean`). -/
#print axioms OpenQuantumProblem40.pinchingInequality
#print axioms OpenQuantumProblem40.trace_pinching_le_wordAverage
#print axioms OpenQuantumProblem40.wordAverage_eq_trace_pinching_add
#print axioms OpenQuantumProblem40.gap_identity
#print axioms OpenQuantumProblem40.coeff_identity
#print axioms OpenQuantumProblem40.moment_identity
#print axioms OpenQuantumProblem40.pinchH_smul
#print axioms OpenQuantumProblem40.pinching_eq_self_of_commute
