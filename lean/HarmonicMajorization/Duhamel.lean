import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Matrix.Normed

/-!
# Duhamel's formula and the second-order expansion of `a ↦ Tr e^{X + aY}`

Authors: Ansh Mishra, Aryan Senthilkumar.  License: MIT.

For complex `M × M` matrices `W, X, Z, Y` and `a ∈ ℂ`:
* `trace_duhamel`: `Tr(W e^Z) - Tr(W e^X) = ∫_0^1 Tr(W e^{rZ} (Z - X) e^{(1-r)X}) dr`;
* `trace_exp_add_smul`: `Tr e^{X + aY} = Tr e^X + a Tr(Y e^X) + a² Φ_{X,Y}(a)`, where
  `Φ_{X,Y}(a) = ∫_0^1 r ∫_0^1 Tr(Y e^{(1-r)X} e^{r'r(X+aY)} Y e^{(1-r')rX}) dr' dr` (`phi2`);
* `continuous_phi2`: `Φ_{X,Y}` is continuous on `ℂ`.

Only scalar (trace) integrals appear; the matrix norm (the `L^∞` operator norm of
`Matrix.Norms.Operator`) is used only to differentiate `exp` and for its continuity.

This is the input for the `τ`-marginal of the density of Theorem A (THEOREMS.md, Step 3).
No hypotheses.
-/

set_option autoImplicit false

namespace HarmonicMajorization

open Matrix Complex MeasureTheory intervalIntegral
open scoped Matrix.Norms.Operator

variable {M : ℕ}

/-- Continuity of the matrix exponential (for the product topology on matrices). -/
lemma continuous_matrix_exp :
    Continuous (fun A : Matrix (Fin M) (Fin M) ℂ => NormedSpace.exp A) :=
  NormedSpace.exp_continuous

lemma continuous_exp_smul (Z : Matrix (Fin M) (Fin M) ℂ) :
    Continuous (fun c : ℂ => NormedSpace.exp (c • Z)) :=
  continuous_matrix_exp.comp (continuous_id.smul continuous_const)

/-- `e^{(1-c)X} e^{cX} = e^X`. -/
lemma exp_one_sub_mul_exp (X : Matrix (Fin M) (Fin M) ℂ) (c : ℂ) :
    NormedSpace.exp ((1 - c) • X) * NormedSpace.exp (c • X) = NormedSpace.exp X := by
  rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left _).smul_right _), ← add_smul,
    sub_add_cancel, one_smul]

/-- **Duhamel's formula** (traced against `W`):
`Tr(W e^Z) - Tr(W e^X) = ∫_0^1 Tr(W e^{rZ} (Z - X) e^{(1-r)X}) dr`. -/
theorem trace_duhamel (W X Z : Matrix (Fin M) (Fin M) ℂ) :
    (W * NormedSpace.exp Z).trace - (W * NormedSpace.exp X).trace
      = ∫ r in (0:ℝ)..1, (W * NormedSpace.exp ((r : ℂ) • Z) * (Z - X)
          * NormedSpace.exp ((1 - (r : ℂ)) • X)).trace := by
  let L : Matrix (Fin M) (Fin M) ℂ →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap (Matrix.traceLinearMap (Fin M) ℝ ℂ)
  have hF : ∀ r : ℝ, HasDerivAt
      (fun r : ℝ => (W * NormedSpace.exp ((r : ℂ) • Z) * NormedSpace.exp ((1 - (r : ℂ)) • X)).trace)
      ((W * NormedSpace.exp ((r : ℂ) • Z) * (Z - X) * NormedSpace.exp ((1 - (r : ℂ)) • X)).trace) r := by
    intro r
    have hZ := hasDerivAt_exp_smul_const (𝕂 := ℝ) Z r
    have hX0 := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (1 - r)
    have hs : HasDerivAt (fun r : ℝ => 1 - r) (-1) r := by
      simpa using (hasDerivAt_id r).const_sub 1
    have hX := hX0.scomp r hs
    have h1 := (hZ.const_mul W).mul hX
    have h2 := L.hasFDerivAt.comp_hasDerivAt r h1
    have h3 : HasDerivAt
        (fun r : ℝ => (W * NormedSpace.exp (r • Z) * NormedSpace.exp ((1 - r) • X)).trace)
        (L (W * (NormedSpace.exp (r • Z) * Z) * NormedSpace.exp ((1 - r) • X) +
          W * NormedSpace.exp (r • Z) * (-1 : ℝ) • (NormedSpace.exp ((1 - r) • X) * X))) r := h2
    have efun : (fun r : ℝ => (W * NormedSpace.exp ((r : ℂ) • Z)
        * NormedSpace.exp ((1 - (r : ℂ)) • X)).trace)
        = fun r : ℝ => (W * NormedSpace.exp (r • Z) * NormedSpace.exp ((1 - r) • X)).trace := by
      funext u
      rw [← Complex.coe_smul, ← Complex.coe_smul]
      push_cast
      rfl
    rw [efun]
    refine h3.congr_deriv ?_
    have hc : NormedSpace.exp ((1 - r) • X) * X = X * NormedSpace.exp ((1 - r) • X) :=
      (((Commute.refl X).smul_right (1 - r)).exp_right).eq.symm
    have e1 : ((r : ℂ)) • Z = r • Z := Complex.coe_smul r Z
    have e2 : (1 - (r : ℂ)) • X = (1 - r) • X := by
      rw [← Complex.coe_smul]; push_cast; rfl
    show (W * (NormedSpace.exp (r • Z) * Z) * NormedSpace.exp ((1 - r) • X) +
          W * NormedSpace.exp (r • Z) * (-1 : ℝ) • (NormedSpace.exp ((1 - r) • X) * X)).trace = _
    rw [e1, e2, hc, neg_one_smul]
    congr 1
    noncomm_ring
  have hcont : Continuous (fun r : ℝ => (W * NormedSpace.exp ((r : ℂ) • Z) * (Z - X)
      * NormedSpace.exp ((1 - (r : ℂ)) • X)).trace) := by
    have h1 : Continuous (fun r : ℝ => NormedSpace.exp ((r : ℂ) • Z)) :=
      (continuous_exp_smul Z).comp Complex.continuous_ofReal
    have h2 : Continuous (fun r : ℝ => NormedSpace.exp ((1 - (r : ℂ)) • X)) :=
      (continuous_exp_smul X).comp (continuous_const.sub Complex.continuous_ofReal)
    exact (((continuous_const.matrix_mul h1).matrix_mul continuous_const).matrix_mul h2).matrix_trace
  rw [integral_eq_sub_of_hasDerivAt (fun r _ => hF r) (hcont.intervalIntegrable 0 1)]
  simp

/-! ### The second-order kernel -/

/-- The kernel of the second-order term: `Tr(Y e^{(1-r)X} e^{r'r(X+aY)} Y e^{(1-r')rX})`. -/
noncomputable def kern2 (X Y : Matrix (Fin M) (Fin M) ℂ) (a : ℂ) (r r' : ℝ) : ℂ :=
  (Y * NormedSpace.exp ((1 - (r : ℂ)) • X) * NormedSpace.exp (((r' : ℂ) * r) • (X + a • Y)) * Y
    * NormedSpace.exp (((1 - (r' : ℂ)) * r) • X)).trace

lemma continuous_kern2 (X Y : Matrix (Fin M) (Fin M) ℂ) :
    Continuous (fun p : (ℂ × ℝ) × ℝ => kern2 X Y p.1.1 p.1.2 p.2) := by
  unfold kern2
  have c1 : Continuous (fun p : (ℂ × ℝ) × ℝ => (1 - (p.1.2 : ℂ))) :=
    continuous_const.sub (Complex.continuous_ofReal.comp continuous_fst.snd)
  have c2 : Continuous (fun p : (ℂ × ℝ) × ℝ => ((p.2 : ℂ) * p.1.2)) :=
    (Complex.continuous_ofReal.comp continuous_snd).mul
      (Complex.continuous_ofReal.comp continuous_fst.snd)
  have c3 : Continuous (fun p : (ℂ × ℝ) × ℝ => ((1 - (p.2 : ℂ)) * p.1.2)) :=
    (continuous_const.sub (Complex.continuous_ofReal.comp continuous_snd)).mul
      (Complex.continuous_ofReal.comp continuous_fst.snd)
  have m2 : Continuous (fun p : (ℂ × ℝ) × ℝ => X + p.1.1 • Y) :=
    continuous_const.add (continuous_fst.fst.smul continuous_const)
  have h1 : Continuous (fun p : (ℂ × ℝ) × ℝ => NormedSpace.exp ((1 - (p.1.2 : ℂ)) • X)) :=
    (continuous_exp_smul X).comp c1
  have h2 : Continuous (fun p : (ℂ × ℝ) × ℝ =>
      NormedSpace.exp (((p.2 : ℂ) * p.1.2) • (X + p.1.1 • Y))) :=
    continuous_matrix_exp.comp (c2.smul m2)
  have h3 : Continuous (fun p : (ℂ × ℝ) × ℝ => NormedSpace.exp (((1 - (p.2 : ℂ)) * p.1.2) • X)) :=
    (continuous_exp_smul X).comp c3
  exact ((((continuous_const.matrix_mul h1).matrix_mul h2).matrix_mul continuous_const).matrix_mul
    h3).matrix_trace

/-- The inner integral `(a, r) ↦ ∫_0^1 kern2 X Y a r r' dr'` is continuous. -/
lemma continuous_inner2 (X Y : Matrix (Fin M) (Fin M) ℂ) :
    Continuous (fun p : ℂ × ℝ => ∫ r' in (0:ℝ)..1, kern2 X Y p.1 p.2 r') := by
  have h : Continuous (Function.uncurry fun (p : ℂ × ℝ) (r' : ℝ) => kern2 X Y p.1 p.2 r') :=
    continuous_kern2 X Y
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' h 0 1

/-- `Φ_{X,Y}(a) = ∫_0^1 r ∫_0^1 kern2 X Y a r r' dr' dr`. -/
noncomputable def phi2 (X Y : Matrix (Fin M) (Fin M) ℂ) (a : ℂ) : ℂ :=
  ∫ r in (0:ℝ)..1, (r : ℂ) * ∫ r' in (0:ℝ)..1, kern2 X Y a r r'

lemma continuous_outer2 (X Y : Matrix (Fin M) (Fin M) ℂ) :
    Continuous (fun p : ℂ × ℝ => (p.2 : ℂ) * ∫ r' in (0:ℝ)..1, kern2 X Y p.1 p.2 r') :=
  (Complex.continuous_ofReal.comp continuous_snd).mul (continuous_inner2 X Y)

/-- Slices of the kernel are continuous. -/
lemma continuous_kern2_slice (X Y : Matrix (Fin M) (Fin M) ℂ) (a : ℂ) (r : ℝ) :
    Continuous (fun r' : ℝ => kern2 X Y a r r') := by
  have h := (continuous_kern2 X Y).comp
    (continuous_const.prodMk continuous_id : Continuous (fun r' : ℝ => ((a, r), r')))
  exact h

/-- Slices of the outer integrand are continuous. -/
lemma continuous_outer2_slice (X Y : Matrix (Fin M) (Fin M) ℂ) (a : ℂ) :
    Continuous (fun r : ℝ => (r : ℂ) * ∫ r' in (0:ℝ)..1, kern2 X Y a r r') := by
  have h := (continuous_outer2 X Y).comp
    (continuous_const.prodMk continuous_id : Continuous (fun r : ℝ => (a, r)))
  exact h

/-- `Φ_{X,Y}` is continuous. -/
theorem continuous_phi2 (X Y : Matrix (Fin M) (Fin M) ℂ) : Continuous (phi2 X Y) := by
  have h : Continuous (Function.uncurry fun (a : ℂ) (r : ℝ) =>
      (r : ℂ) * ∫ r' in (0:ℝ)..1, kern2 X Y a r r') := continuous_outer2 X Y
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' h 0 1

/-- **Second-order expansion**: `Tr e^{X + aY} = Tr e^X + a Tr(Y e^X) + a² Φ_{X,Y}(a)`. -/
theorem trace_exp_add_smul (X Y : Matrix (Fin M) (Fin M) ℂ) (a : ℂ) :
    (NormedSpace.exp (X + a • Y)).trace
      = (NormedSpace.exp X).trace + a * (Y * NormedSpace.exp X).trace + a ^ 2 * phi2 X Y a := by
  have h1 := trace_duhamel 1 X (X + a • Y)
  simp only [Matrix.one_mul, add_sub_cancel_left] at h1
  have h2 : ∀ r : ℝ, (NormedSpace.exp ((r : ℂ) • (X + a • Y)) * (a • Y)
      * NormedSpace.exp ((1 - (r : ℂ)) • X)).trace
      = a * (Y * NormedSpace.exp X).trace
        + a ^ 2 * ((r : ℂ) * ∫ r' in (0:ℝ)..1, kern2 X Y a r r') := by
    intro r
    set W := Y * NormedSpace.exp ((1 - (r : ℂ)) • X) with hW
    have h3 := trace_duhamel W ((r : ℂ) • X) ((r : ℂ) • (X + a • Y))
    have hWr : (W * NormedSpace.exp ((r : ℂ) • X)).trace = (Y * NormedSpace.exp X).trace := by
      rw [hW, Matrix.mul_assoc, exp_one_sub_mul_exp]
    have hint : ∀ r' : ℝ, (W * NormedSpace.exp ((r' : ℂ) • ((r : ℂ) • (X + a • Y)))
        * ((r : ℂ) • (X + a • Y) - (r : ℂ) • X)
        * NormedSpace.exp ((1 - (r' : ℂ)) • ((r : ℂ) • X))).trace
        = ((r : ℂ) * a) * kern2 X Y a r r' := by
      intro r'
      have e1 : (r : ℂ) • (X + a • Y) - (r : ℂ) • X = ((r : ℂ) * a) • Y := by
        rw [smul_add, add_sub_cancel_left, smul_smul]
      rw [e1, smul_smul, smul_smul, hW]
      unfold kern2
      rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
    simp_rw [hint] at h3
    rw [intervalIntegral.integral_const_mul] at h3
    have hcyc : (NormedSpace.exp ((r : ℂ) • (X + a • Y)) * (a • Y)
        * NormedSpace.exp ((1 - (r : ℂ)) • X)).trace
        = a * (W * NormedSpace.exp ((r : ℂ) • (X + a • Y))).trace := by
      rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, hW,
        Matrix.trace_mul_cycle, Matrix.mul_assoc, Matrix.mul_assoc Y, Matrix.trace_mul_comm Y,
        Matrix.mul_assoc]
    rw [hcyc]
    have h4 : (W * NormedSpace.exp ((r : ℂ) • (X + a • Y))).trace
        = (W * NormedSpace.exp ((r : ℂ) • X)).trace
          + (r : ℂ) * a * ∫ r' in (0:ℝ)..1, kern2 X Y a r r' := by
      rw [← h3]; ring
    rw [h4, hWr]
    ring
  simp_rw [h2] at h1
  have hc : Continuous (fun r : ℝ => a ^ 2 * ((r : ℂ) * ∫ r' in (0:ℝ)..1, kern2 X Y a r r')) :=
    continuous_const.mul ((continuous_outer2 X Y).comp (continuous_const.prodMk continuous_id))
  rw [intervalIntegral.integral_add intervalIntegrable_const (hc.intervalIntegrable 0 1),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul] at h1
  simp only [sub_zero, one_smul] at h1
  unfold phi2
  linear_combination h1

end HarmonicMajorization
