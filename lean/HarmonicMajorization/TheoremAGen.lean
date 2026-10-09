import HarmonicMajorization.PencilGen
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.MeasureTheory.Group.LIntegral

/-!
# Theorem A for a Hermitian `P` (general `B`), from the multi-line Radon identity

Authors: Ansh Mishra, Aryan Senthilkumar.  License: MIT.

Setting: `P` Hermitian with `spec P ⊆ [0,1]` (in THEOREMS.md, `P = 1 - B` with `0 ≤ B ≤ 1`), `g`
Hermitian, `g_d = pinchH hP g` the pinching onto the eigenspaces of `P` (equivalently of `B`), and
`ρ = rhoG P g` the density `(1/2π) Σ |Im x_i(s,τ)|`.

* `Hyp_RI_gen M`: **the multi-line Radon identity** for Hermitian `P`, `H` of size `M`:
  `(1/2π) ∫_ℝ Σ_i |Im y_i(τ)| dτ = Tr H_+ - Tr (H_d)_+`, `y_i(τ)` the eigenvalues of `(P - τ)⁻¹ H`.
  This is [27, Remark RIgeneralB]; for `P` a projection it is `OQP27.StripL3b.hyp_RI`.
* `radon_eq_sliceFunG`: (RI) gives the Radon slices `∫ ρ(w + ξτ, τ) dτ = U_ξ(w)`.
* **`theoremA_gen`** (from `Hyp_RI_gen M`): for all `(a, t) ∈ ℂ²`,
  `Tr e^{ag - tP} - Tr e^{a g_d - tP} = a² ∫∫ e^{as - tτ} ρ(s,τ) ds dτ`, together with the
  integrability of `e^{as - tτ} ρ`.

Hypothesis used: `Hyp_RI_gen M` (stated as a `Prop`, passed as an argument).
Paper: THEOREMS.md, Theorem A; [27, Section RItoD] (the argument from the Radon identity).
-/

set_option autoImplicit false

namespace HarmonicMajorization

open Matrix Complex MeasureTheory Filter Topology Set
open scoped Real
open OQP27.StripL3b (pencilRoots imAbsSum frob sliceU)

variable {M : ℕ}

/-- **The multi-line Radon identity** ([27, Remark RIgeneralB]): for Hermitian `P` and `H`,
`τ ↦ Σ_i |Im y_i(τ)|` is integrable on `ℝ` and `(1/2π) ∫ Σ_i |Im y_i(τ)| dτ = Tr H_+ - Tr (H_d)_+`,
where `y_i(τ)` are the eigenvalues of `(P - τ)⁻¹ H` and `H_d` is the pinching of `H` onto the
eigenspaces of `P`. -/
def Hyp_RI_gen (M : ℕ) : Prop :=
  ∀ (P H : Matrix (Fin M) (Fin M) ℂ) (hP : P.IsHermitian) (hH : H.IsHermitian),
    Integrable (fun τ => imAbsSum (pencilRoots P H τ)) ∧
    (∫ τ, imAbsSum (pencilRoots P H τ)) / (2 * π)
      = ∑ i, max (hH.eigenvalues i) 0 - ∑ i, max ((isHermitian_pinchH hP hH).eigenvalues i) 0

/-- `D(a, t) = Tr e^{ag - tP} - Tr e^{a g_d - tP}`. -/
noncomputable def bmvDG {P : Matrix (Fin M) (Fin M) ℂ} (hP : P.IsHermitian)
    (g : Matrix (Fin M) (Fin M) ℂ) (a t : ℂ) : ℂ :=
  (NormedSpace.exp (a • g - t • P)).trace - (NormedSpace.exp (a • pinchH hP g - t • P)).trace

/-- The Laplace transform `L(a, t) = ∫∫ e^{as - tτ} ρ(s, τ) ds dτ`. -/
noncomputable def laplaceG (P g : Matrix (Fin M) (Fin M) ℂ) (a t : ℂ) : ℂ :=
  ∫ q : ℝ × ℝ, cexp (a * q.1 - t * q.2) * (rhoG P g q.1 q.2 : ℂ)

lemma tendsto_inv_nat_nhdsNE :
    Tendsto (fun n : ℕ => (((1 : ℝ) / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝[≠] 0) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · have h := (Complex.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
    rw [Complex.ofReal_zero] at h
    exact h
  · refine Eventually.of_forall fun n => ?_
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Complex.ofReal_eq_zero]
    positivity

section Slices

variable {P g : Matrix (Fin M) (Fin M) ℂ} (hP : P.IsHermitian) (hg : g.IsHermitian)
include hP hg

omit hg in
lemma measurable_rhoG_comp {α : Type*} [MeasurableSpace α] {u v : α → ℝ} (hu : Measurable u)
    (hv : Measurable v) : Measurable (fun x => rhoG P g (u x) (v x)) := by
  have h := (measurable_rhoG hP g).comp (hu.prodMk hv)
  exact h

lemma isHermitian_sub_smulG (ξ : ℝ) : (g - (ξ : ℂ) • P).IsHermitian :=
  hg.sub (hP.smul (OQP27.StripL3b.isSelfAdjoint_ofReal ξ))

/-- The slice function `U_ξ(w) = Σ (λ_j(ξ) - w)_+ - Σ (λ^0_j(ξ) - w)_+`, with `λ_j(ξ)` the
eigenvalues of `g - ξP` and `λ^0_j(ξ)` those of its pinching `g_d - ξP`. -/
noncomputable def sliceFunG (ξ w : ℝ) : ℝ :=
  sliceU (isHermitian_sub_smulG hP hg ξ).eigenvalues
    (isHermitian_pinchH hP (isHermitian_sub_smulG hP hg ξ)).eigenvalues w

/-- **(RI) ⟹ Radon slices**: `∫ ρ(w + ξτ, τ) dτ = U_ξ(w)`. -/
theorem radon_eq_sliceFunG (hRI : Hyp_RI_gen M) (ξ w : ℝ) :
    Integrable (fun τ => rhoG P g (w + ξ * τ) τ) ∧
    ∫ τ, rhoG P g (w + ξ * τ) τ = sliceFunG hP hg ξ w := by
  set A := g - (ξ : ℂ) • P with hA_def
  have hA : A.IsHermitian := isHermitian_sub_smulG hP hg ξ
  set H := A - (w : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ) with hH_def
  have hH : H.IsHermitian := hA.sub (isHermitian_one.smul (OQP27.StripL3b.isSelfAdjoint_ofReal w))
  obtain ⟨hint, heq⟩ := hRI P H hP hH
  have hpt : (fun τ => rhoG P g (w + ξ * τ) τ)
      = fun τ => imAbsSum (pencilRoots P H τ) / (2 * π) := by
    funext τ
    unfold rhoG
    have e : g - (((w + ξ * τ : ℝ)) : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ)
        = H + (ξ : ℂ) • (P - (τ : ℂ) • 1) := by
      rw [hH_def, hA_def]; push_cast; module
    rw [e, imAbsSum_pencilRoots_add_smul hP]
  refine ⟨by rw [hpt]; exact hint.div_const _, ?_⟩
  rw [hpt, integral_div, heq]
  have e1 : ∑ i, max (hH.eigenvalues i) 0 = ∑ i, max (hA.eigenvalues i - w) 0 :=
    OQP27.StripL3b.sum_eigenvalues_sub_smul_one hA w hH (fun x => max x 0)
  have hpinch : pinchH hP H = pinchH hP A - (w : ℂ) • 1 := by
    rw [hH_def, pinchH_sub, pinchH_smul, pinchH_one]
  have hA0 : (pinchH hP A).IsHermitian := isHermitian_pinchH hP hA
  have hA0w : (pinchH hP A - (w : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ)).IsHermitian :=
    hpinch ▸ isHermitian_pinchH hP hH
  have e2 : ∑ i, max ((isHermitian_pinchH hP hH).eigenvalues i) 0
      = ∑ i, max (hA0.eigenvalues i - w) 0 := by
    rw [OQP27.StripL3b.eigenvalues_congr hpinch (isHermitian_pinchH hP hH) hA0w]
    exact OQP27.StripL3b.sum_eigenvalues_sub_smul_one hA0 w hA0w (fun x => max x 0)
  rw [e1, e2]
  rfl

lemma sliceFunG_nonneg (hRI : Hyp_RI_gen M) (ξ w : ℝ) : 0 ≤ sliceFunG hP hg ξ w := by
  rw [← (radon_eq_sliceFunG hP hg hRI ξ w).2]
  exact integral_nonneg fun τ => rhoG_nonneg _ _ _ _

/-- **Tonelli step.** `∫∫ e^{as - aξτ} ρ = ∫ e^{aw} U_ξ(w) dw` (in `[0, ∞]`). -/
theorem lintegral_exp_mul_rhoG (hRI : Hyp_RI_gen M) (a ξ : ℝ) :
    ∫⁻ q : ℝ × ℝ, ENNReal.ofReal (Real.exp (a * q.1 - a * ξ * q.2) * rhoG P g q.1 q.2)
      = ∫⁻ w, ENNReal.ofReal (Real.exp (a * w) * sliceFunG hP hg ξ w) := by
  have hF : Measurable (Function.uncurry (rhoG P g)) := measurable_rhoG hP g
  set f : ℝ × ℝ → ENNReal := fun q =>
    ENNReal.ofReal (Real.exp (a * q.1 - a * ξ * q.2) * rhoG P g q.1 q.2) with hf_def
  have hfm : Measurable f := by
    apply ENNReal.measurable_ofReal.comp
    exact (by fun_prop : Measurable fun q : ℝ × ℝ => Real.exp (a * q.1 - a * ξ * q.2)).mul hF
  rw [Measure.volume_eq_prod, lintegral_prod_symm' f hfm]
  have hshift : ∀ τ : ℝ, ∫⁻ s, f (s, τ)
      = ∫⁻ w, ENNReal.ofReal (Real.exp (a * w) * rhoG P g (w + ξ * τ) τ) := by
    intro τ
    rw [← lintegral_add_right_eq_self (fun s => f (s, τ)) (ξ * τ)]
    congr 1
    funext w
    simp only [hf_def]
    congr 3
    ring
  simp_rw [hshift]
  have hm2 : Measurable (Function.uncurry fun τ w =>
      ENNReal.ofReal (Real.exp (a * w) * rhoG P g (w + ξ * τ) τ)) := by
    apply ENNReal.measurable_ofReal.comp
    have h1 : Measurable fun p : ℝ × ℝ => Real.exp (a * p.2) := by fun_prop
    have h2 : Measurable fun p : ℝ × ℝ => rhoG P g (p.2 + ξ * p.1) p.1 :=
      measurable_rhoG_comp hP (by fun_prop) (by fun_prop)
    exact h1.mul h2
  rw [lintegral_lintegral_swap hm2.aemeasurable]
  congr 1
  funext w
  have hR := radon_eq_sliceFunG hP hg hRI ξ w
  have hmeas : Measurable fun τ => ENNReal.ofReal (rhoG P g (w + ξ * τ) τ) :=
    ENNReal.measurable_ofReal.comp (measurable_rhoG_comp hP (by fun_prop) (by fun_prop))
  calc ∫⁻ τ, ENNReal.ofReal (Real.exp (a * w) * rhoG P g (w + ξ * τ) τ)
      = ∫⁻ τ, ENNReal.ofReal (Real.exp (a * w)) * ENNReal.ofReal (rhoG P g (w + ξ * τ) τ) := by
        congr 1; funext τ; exact ENNReal.ofReal_mul (Real.exp_pos _).le
    _ = ENNReal.ofReal (Real.exp (a * w)) * ∫⁻ τ, ENNReal.ofReal (rhoG P g (w + ξ * τ) τ) :=
        lintegral_const_mul _ hmeas
    _ = ENNReal.ofReal (Real.exp (a * w))
          * ENNReal.ofReal (∫ τ, rhoG P g (w + ξ * τ) τ) := by
        rw [ofReal_integral_eq_lintegral_ofReal hR.1
          (ae_of_all _ fun τ => rhoG_nonneg _ _ _ _)]
    _ = ENNReal.ofReal (Real.exp (a * w) * sliceFunG hP hg ξ w) := by
        rw [hR.2, ← ENNReal.ofReal_mul (Real.exp_pos _).le]

/-- **Real Laplace identity.**  For real `a ≠ 0` and real `ξ`: `e^{as - aξτ} ρ` is integrable on
`ℝ²` and its integral is `(Σ e^{aλ_j(ξ)} - Σ e^{aλ^0_j(ξ)}) / a²`. -/
theorem integral_exp_mul_rhoG (hRI : Hyp_RI_gen M) {a : ℝ} (ha : a ≠ 0) (ξ : ℝ) :
    Integrable (fun q : ℝ × ℝ => Real.exp (a * q.1 - a * ξ * q.2) * rhoG P g q.1 q.2) ∧
    ∫ q : ℝ × ℝ, Real.exp (a * q.1 - a * ξ * q.2) * rhoG P g q.1 q.2
      = (∑ i, Real.exp (a * (isHermitian_sub_smulG hP hg ξ).eigenvalues i)
          - ∑ i, Real.exp (a *
            (isHermitian_pinchH hP (isHermitian_sub_smulG hP hg ξ)).eigenvalues i)) / a ^ 2 := by
  have hA := isHermitian_sub_smulG hP hg ξ
  have hA0 := isHermitian_pinchH hP hA
  have hsum : ∑ i, hA.eigenvalues i = ∑ i, hA0.eigenvalues i :=
    OQP27.StripL3b.sum_eigenvalues_eq_of_trace_eq hA hA0 (trace_pinchH hP _).symm
  obtain ⟨hSint0, hSval0⟩ :=
    OQP27.StripL3b.integral_exp_mul_sliceU hA.eigenvalues hA0.eigenvalues hsum ha
  have hSint : Integrable (fun w => Real.exp (a * w) * sliceFunG hP hg ξ w) := hSint0
  have hSval : ∫ w, Real.exp (a * w) * sliceFunG hP hg ξ w
      = (∑ j, Real.exp (a * hA.eigenvalues j) - ∑ j, Real.exp (a * hA0.eigenvalues j)) / a ^ 2 :=
    hSval0
  have hnn : ∀ q : ℝ × ℝ, 0 ≤ Real.exp (a * q.1 - a * ξ * q.2) * rhoG P g q.1 q.2 :=
    fun q => mul_nonneg (Real.exp_pos _).le (rhoG_nonneg _ _ _ _)
  have hSnn : ∀ w, 0 ≤ Real.exp (a * w) * sliceFunG hP hg ξ w :=
    fun w => mul_nonneg (Real.exp_pos _).le (sliceFunG_nonneg hP hg hRI ξ w)
  have hL : ∫⁻ q : ℝ × ℝ, ENNReal.ofReal (Real.exp (a * q.1 - a * ξ * q.2) * rhoG P g q.1 q.2)
      = ENNReal.ofReal (∫ w, Real.exp (a * w) * sliceFunG hP hg ξ w) := by
    rw [lintegral_exp_mul_rhoG hP hg hRI a ξ,
      ofReal_integral_eq_lintegral_ofReal hSint (ae_of_all _ hSnn)]
  have hmeas : Measurable fun q : ℝ × ℝ => Real.exp (a * q.1 - a * ξ * q.2) * rhoG P g q.1 q.2 :=
    (by fun_prop : Measurable fun q : ℝ × ℝ => Real.exp (a * q.1 - a * ξ * q.2)).mul
      (measurable_rhoG hP g)
  have hint : Integrable (fun q : ℝ × ℝ => Real.exp (a * q.1 - a * ξ * q.2) * rhoG P g q.1 q.2) := by
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hnn), hL]
    exact ENNReal.ofReal_lt_top
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hnn) hmeas.aestronglyMeasurable, hL,
    ENNReal.toReal_ofReal (integral_nonneg hSnn)]
  exact hSval

/-- `D(a, aξ)` for real `a`, `ξ` in terms of the eigenvalues of `g - ξP` and `g_d - ξP`. -/
lemma bmvDG_real (a ξ : ℝ) :
    bmvDG hP g a ((a : ℂ) * ξ)
      = ((∑ i, Real.exp (a * (isHermitian_sub_smulG hP hg ξ).eigenvalues i)
          - ∑ i, Real.exp (a *
            (isHermitian_pinchH hP (isHermitian_sub_smulG hP hg ξ)).eigenvalues i) : ℝ) : ℂ) := by
  have hA := isHermitian_sub_smulG hP hg ξ
  have hA0 := isHermitian_pinchH hP hA
  have e1 : (a : ℂ) • g - ((a : ℂ) * ξ) • P = (a : ℂ) • (g - (ξ : ℂ) • P) := by
    rw [smul_sub, smul_smul]
  have e2 : (a : ℂ) • pinchH hP g - ((a : ℂ) * ξ) • P = (a : ℂ) • pinchH hP (g - (ξ : ℂ) • P) := by
    rw [pinchH_sub, pinchH_smul, pinchH_self, smul_sub, smul_smul]
  unfold bmvDG
  rw [e1, e2, OQP27.StripL3b.trace_exp_smul_isHermitian hA,
    OQP27.StripL3b.trace_exp_smul_isHermitian hA0]
  push_cast
  rfl

end Slices

/-! ### Theorem A -/

section TheoremA

variable {P g : Matrix (Fin M) (Fin M) ℂ} (hP : P.IsHermitian) (hg : g.IsHermitian)
  (hspec : ∀ p ∈ spec hP, 0 ≤ p ∧ p ≤ 1)
include hP hg

/-- **Theorem A for real `a ≠ 0` and real `t`.** -/
theorem bmv2G_real (hRI : Hyp_RI_gen M) {a : ℝ} (ha : a ≠ 0) (t : ℝ) :
    Integrable (fun q : ℝ × ℝ => Real.exp (a * q.1 - t * q.2) * rhoG P g q.1 q.2) ∧
    bmvDG hP g a t
      = ((a ^ 2 * ∫ q : ℝ × ℝ, Real.exp (a * q.1 - t * q.2) * rhoG P g q.1 q.2 : ℝ) : ℂ) := by
  have hξ : a * (t / a) = t := by field_simp
  obtain ⟨hint, hval⟩ := integral_exp_mul_rhoG hP hg hRI ha (t / a)
  have hfun : (fun q : ℝ × ℝ => Real.exp (a * q.1 - a * (t / a) * q.2) * rhoG P g q.1 q.2)
      = fun q => Real.exp (a * q.1 - t * q.2) * rhoG P g q.1 q.2 := by
    funext q; rw [hξ]
  rw [hfun] at hint hval
  refine ⟨hint, ?_⟩
  have h := bmvDG_real hP hg a (t / a)
  rw [show ((a : ℂ) * ((t / a : ℝ) : ℂ)) = (t : ℂ) by rw [← Complex.ofReal_mul, hξ]] at h
  rw [h, hval]
  congr 1
  field_simp

/-- `e^{bs} ρ(s, τ)` is integrable on `ℝ²` for every real `b`. -/
lemma integrable_exp_mul_rhoG (hRI : Hyp_RI_gen M) (b : ℝ) :
    Integrable (fun q : ℝ × ℝ => Real.exp (b * q.1) * rhoG P g q.1 q.2) := by
  by_cases hb : b = 0
  · have h1 := (bmv2G_real hP hg hRI one_ne_zero 0).1
    have h2 := (bmv2G_real hP hg hRI (neg_ne_zero.mpr one_ne_zero) 0).1
    have hmeas : Measurable fun q : ℝ × ℝ => Real.exp (b * q.1) * rhoG P g q.1 q.2 :=
      (by fun_prop : Measurable fun q : ℝ × ℝ => Real.exp (b * q.1)).mul (measurable_rhoG hP g)
    refine (h1.add h2).mono' hmeas.aestronglyMeasurable (ae_of_all _ fun q => ?_)
    have hF := rhoG_nonneg P g q.1 q.2
    have e1 := Real.exp_pos q.1
    have e2 := Real.exp_pos (-q.1)
    have e3 : 1 ≤ Real.exp q.1 + Real.exp (-q.1) := by
      rcases le_total 0 q.1 with h | h
      · linarith [Real.one_le_exp h]
      · linarith [Real.one_le_exp (neg_nonneg.mpr h)]
    rw [hb, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    simp only [zero_mul, Real.exp_zero, one_mul, sub_zero, neg_mul, Pi.add_apply]
    nlinarith [mul_nonneg (sub_nonneg.mpr e3) hF]
  · simpa using (bmv2G_real hP hg hRI hb 0).1

omit hP hg in
lemma laplaceG_real (a t : ℝ) :
    laplaceG P g a t
      = ((∫ q : ℝ × ℝ, Real.exp (a * q.1 - t * q.2) * rhoG P g q.1 q.2 : ℝ) : ℂ) := by
  unfold laplaceG
  rw [← integral_complex_ofReal]
  congr 1
  funext q
  rw [Complex.ofReal_mul, Complex.ofReal_exp]
  push_cast
  ring

omit hg in
open scoped Matrix.Norms.Operator in
/-- `t ↦ D(a, t)` is entire. -/
lemma differentiable_bmvDG_t (a : ℂ) : Differentiable ℂ (fun t : ℂ => bmvDG hP g a t) := by
  have htr : Differentiable ℂ (fun X : Matrix (Fin M) (Fin M) ℂ => X.trace) :=
    (LinearMap.toContinuousLinearMap (Matrix.traceLinearMap (Fin M) ℂ ℂ)).differentiable
  have hterm : ∀ A : Matrix (Fin M) (Fin M) ℂ,
      Differentiable ℂ (fun t : ℂ => (NormedSpace.exp (A - t • P)).trace) := by
    intro A t
    have hexp : DifferentiableAt ℂ (NormedSpace.exp : Matrix (Fin M) (Fin M) ℂ → _) (A - t • P) :=
      (NormedSpace.exp_analytic (𝕂 := ℂ) (A - t • P)).differentiableAt
    have haff : DifferentiableAt ℂ (fun t : ℂ => A - t • P) t :=
      (differentiableAt_const A).sub (differentiableAt_id.smul_const P)
    exact (htr _).comp t (hexp.comp t haff)
  unfold bmvDG
  exact (hterm (a • g)).sub (hterm (a • pinchH hP g))

omit hg in
open scoped Matrix.Norms.Operator in
/-- `a ↦ D(a, t)` is entire. -/
lemma differentiable_bmvDG_a (t : ℂ) : Differentiable ℂ (fun a : ℂ => bmvDG hP g a t) := by
  have htr : Differentiable ℂ (fun X : Matrix (Fin M) (Fin M) ℂ => X.trace) :=
    (LinearMap.toContinuousLinearMap (Matrix.traceLinearMap (Fin M) ℂ ℂ)).differentiable
  have hterm : ∀ A : Matrix (Fin M) (Fin M) ℂ,
      Differentiable ℂ (fun a : ℂ => (NormedSpace.exp (a • A - t • P)).trace) := by
    intro A a
    have hexp : DifferentiableAt ℂ (NormedSpace.exp : Matrix (Fin M) (Fin M) ℂ → _)
        (a • A - t • P) :=
      (NormedSpace.exp_analytic (𝕂 := ℂ) (a • A - t • P)).differentiableAt
    have haff : DifferentiableAt ℂ (fun a : ℂ => a • A - t • P) a :=
      (differentiableAt_id.smul_const A).sub (differentiableAt_const _)
    exact (htr _).comp a (hexp.comp a haff)
  unfold bmvDG
  exact (hterm g).sub (hterm (pinchH hP g))

include hspec in
/-- `‖e^{as - tτ}‖ ≤ e^{|Re t|} e^{(Re a) s}` on the support of `ρ`. -/
lemma norm_cexp_mul_rhoG_le (a t : ℂ) (q : ℝ × ℝ) :
    ‖cexp (a * q.1 - t * q.2) * (rhoG P g q.1 q.2 : ℂ)‖
      ≤ Real.exp (|t.re|) * (Real.exp (a.re * q.1) * rhoG P g q.1 q.2) := by
  by_cases hq : 0 < q.2 ∧ q.2 < 1
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (rhoG_nonneg _ _ _ _),
      ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (OQP27.StripL3b.norm_cexp_le hq.1 hq.2) (rhoG_nonneg _ _ _ _)
  · rw [rhoG_eq_zero_of_not_mem_Ioo hP hg hspec hq]
    simp

include hspec in
/-- The integrand of the Laplace transform is integrable for all complex `a`, `t`. -/
lemma integrable_laplaceG_integrand (hRI : Hyp_RI_gen M) (a t : ℂ) :
    Integrable (fun q : ℝ × ℝ => cexp (a * q.1 - t * q.2) * (rhoG P g q.1 q.2 : ℂ)) := by
  have hFm : Measurable fun q : ℝ × ℝ => rhoG P g q.1 q.2 := measurable_rhoG hP g
  have hmeas : Measurable fun q : ℝ × ℝ => cexp (a * q.1 - t * q.2) * (rhoG P g q.1 q.2 : ℂ) :=
    (by fun_prop : Measurable fun q : ℝ × ℝ => cexp (a * q.1 - t * q.2)).mul
      (Complex.measurable_ofReal.comp hFm)
  exact ((integrable_exp_mul_rhoG hP hg hRI a.re).const_mul (Real.exp (|t.re|))).mono'
    hmeas.aestronglyMeasurable (ae_of_all _ fun q => norm_cexp_mul_rhoG_le hP hg hspec a t q)

include hspec in
/-- `t ↦ L(a, t)` is entire for real `a`. -/
lemma differentiable_laplaceG_t (hRI : Hyp_RI_gen M) (a : ℝ) :
    Differentiable ℂ (fun t : ℂ => laplaceG P g a t) := by
  intro t₀
  have hFm : Measurable fun q : ℝ × ℝ => rhoG P g q.1 q.2 := measurable_rhoG hP g
  have hbd := integrable_exp_mul_rhoG hP hg hRI a
  set C : ℝ := Real.exp (|t₀.re| + 1) with hC
  have hmeasF : ∀ t : ℂ, Measurable fun q : ℝ × ℝ =>
      cexp (a * q.1 - t * q.2) * (rhoG P g q.1 q.2 : ℂ) := fun t =>
    (by fun_prop : Measurable fun q : ℝ × ℝ => cexp (a * q.1 - t * q.2)).mul
      (Complex.measurable_ofReal.comp hFm)
  have hkey := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun (t : ℂ) (q : ℝ × ℝ) => cexp (a * q.1 - t * q.2) * (rhoG P g q.1 q.2 : ℂ))
    (F' := fun (t : ℂ) (q : ℝ × ℝ) =>
      (-(q.2 : ℂ)) * cexp (a * q.1 - t * q.2) * (rhoG P g q.1 q.2 : ℂ))
    (x₀ := t₀) (s := Metric.ball t₀ 1)
    (bound := fun q => C * (Real.exp (a * q.1) * rhoG P g q.1 q.2))
    (Metric.ball_mem_nhds t₀ one_pos)
    (Eventually.of_forall fun t => (hmeasF t).aestronglyMeasurable)
    (integrable_laplaceG_integrand hP hg hspec hRI a t₀)
    (by
      refine ((by fun_prop : Measurable fun q : ℝ × ℝ => (-(q.2 : ℂ))
        * cexp (a * q.1 - t₀ * q.2)).mul
        (Complex.measurable_ofReal.comp hFm)).aestronglyMeasurable)
    (ae_of_all _ fun q t ht => by
      by_cases hq : 0 < q.2 ∧ q.2 < 1
      · have hre : |t.re| ≤ |t₀.re| + 1 := by
          have h1 : |t.re - t₀.re| ≤ ‖t - t₀‖ := by
            rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _
          have h2 : ‖t - t₀‖ < 1 := by rw [← dist_eq_norm]; exact ht
          have := abs_sub_abs_le_abs_sub t.re t₀.re
          linarith
        rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs, abs_of_nonneg (rhoG_nonneg _ _ _ _), abs_of_pos hq.1]
        have hb := OQP27.StripL3b.norm_cexp_le (a := (a : ℂ)) (t := t) hq.1 hq.2
        simp only [Complex.ofReal_re] at hb
        have hC' : Real.exp (|t.re|) ≤ C := Real.exp_le_exp.mpr hre
        have hF := rhoG_nonneg P g q.1 q.2
        have hE := Real.exp_pos (a * q.1)
        calc q.2 * ‖cexp (a * q.1 - t * q.2)‖ * rhoG P g q.1 q.2
            ≤ 1 * (Real.exp (|t.re|) * Real.exp (a * q.1)) * rhoG P g q.1 q.2 := by
              apply mul_le_mul_of_nonneg_right _ hF
              exact mul_le_mul hq.2.le hb (norm_nonneg _) zero_le_one
          _ ≤ C * (Real.exp (a * q.1) * rhoG P g q.1 q.2) := by
              rw [one_mul, mul_assoc]
              exact mul_le_mul_of_nonneg_right hC' (by positivity)
      · rw [rhoG_eq_zero_of_not_mem_Ioo hP hg hspec hq]
        simp)
    (hbd.const_mul C)
    (ae_of_all _ fun q t _ => by
      have h1 : HasDerivAt (fun t : ℂ => (a : ℂ) * q.1 - t * q.2) (-(1 * (q.2 : ℂ))) t :=
        ((hasDerivAt_id t).mul_const (q.2 : ℂ)).const_sub _
      have h2 := (h1.cexp).mul_const (rhoG P g q.1 q.2 : ℂ)
      refine h2.congr_deriv ?_
      ring)
  exact hkey.2.differentiableAt

include hspec in
/-- `a ↦ L(a, t)` is entire. -/
lemma differentiable_laplaceG_a (hRI : Hyp_RI_gen M) (t : ℂ) :
    Differentiable ℂ (fun a : ℂ => laplaceG P g a t) := by
  intro a₀
  have hFm : Measurable fun q : ℝ × ℝ => rhoG P g q.1 q.2 := measurable_rhoG hP g
  set c : ℝ := a₀.re with hc
  set K : ℝ := Real.exp (|t.re|) with hK
  have hmeasF : ∀ a : ℂ, Measurable fun q : ℝ × ℝ =>
      cexp (a * q.1 - t * q.2) * (rhoG P g q.1 q.2 : ℂ) := fun a =>
    (by fun_prop : Measurable fun q : ℝ × ℝ => cexp (a * q.1 - t * q.2)).mul
      (Complex.measurable_ofReal.comp hFm)
  have hbd : Integrable fun q : ℝ × ℝ => K * ((Real.exp ((c + 2) * q.1)
      + 2 * Real.exp (c * q.1) + Real.exp ((c - 2) * q.1)) * rhoG P g q.1 q.2) := by
    have h1 := integrable_exp_mul_rhoG hP hg hRI (c + 2)
    have h2 := integrable_exp_mul_rhoG hP hg hRI c
    have h3 := integrable_exp_mul_rhoG hP hg hRI (c - 2)
    have := ((h1.add (h2.const_mul 2)).add h3).const_mul K
    refine this.congr (ae_of_all _ fun q => ?_)
    simp only [Pi.add_apply]
    ring
  have hkey := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun (a : ℂ) (q : ℝ × ℝ) => cexp (a * q.1 - t * q.2) * (rhoG P g q.1 q.2 : ℂ))
    (F' := fun (a : ℂ) (q : ℝ × ℝ) =>
      (q.1 : ℂ) * cexp (a * q.1 - t * q.2) * (rhoG P g q.1 q.2 : ℂ))
    (x₀ := a₀) (s := Metric.ball a₀ 1)
    (bound := fun q => K * ((Real.exp ((c + 2) * q.1)
      + 2 * Real.exp (c * q.1) + Real.exp ((c - 2) * q.1)) * rhoG P g q.1 q.2))
    (Metric.ball_mem_nhds a₀ one_pos)
    (Eventually.of_forall fun a => (hmeasF a).aestronglyMeasurable)
    (integrable_laplaceG_integrand hP hg hspec hRI a₀ t)
    (((by fun_prop : Measurable fun q : ℝ × ℝ => (q.1 : ℂ)
        * cexp (a₀ * q.1 - t * q.2)).mul
        (Complex.measurable_ofReal.comp hFm)).aestronglyMeasurable)
    (ae_of_all _ fun q a ha => by
      by_cases hq : 0 < q.2 ∧ q.2 < 1
      · have hre : |a.re - c| ≤ 1 := by
          have h1 : |a.re - a₀.re| ≤ ‖a - a₀‖ := by
            rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _
          have h2 : ‖a - a₀‖ < 1 := by rw [← dist_eq_norm]; exact ha
          rw [hc]; linarith
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs, abs_of_nonneg (rhoG_nonneg _ _ _ _)]
        have hb := OQP27.StripL3b.norm_cexp_le (a := a) (t := t) hq.1 hq.2
        have hF := rhoG_nonneg P g q.1 q.2
        have hm := OQP27.StripL3b.abs_mul_exp_le (s := q.1) hre
        calc |q.1| * ‖cexp (a * q.1 - t * q.2)‖ * rhoG P g q.1 q.2
            ≤ |q.1| * (K * Real.exp (a.re * q.1)) * rhoG P g q.1 q.2 := by
              apply mul_le_mul_of_nonneg_right _ hF
              exact mul_le_mul_of_nonneg_left hb (abs_nonneg _)
          _ = K * (|q.1| * Real.exp (a.re * q.1)) * rhoG P g q.1 q.2 := by ring
          _ ≤ K * ((Real.exp ((c + 2) * q.1) + 2 * Real.exp (c * q.1)
                + Real.exp ((c - 2) * q.1))) * rhoG P g q.1 q.2 := by
              apply mul_le_mul_of_nonneg_right _ hF
              exact mul_le_mul_of_nonneg_left hm (Real.exp_pos _).le
          _ = K * ((Real.exp ((c + 2) * q.1) + 2 * Real.exp (c * q.1)
                + Real.exp ((c - 2) * q.1)) * rhoG P g q.1 q.2) := by ring
      · rw [rhoG_eq_zero_of_not_mem_Ioo hP hg hspec hq]
        simp)
    hbd
    (ae_of_all _ fun q a _ => by
      have h1 : HasDerivAt (fun a : ℂ => a * q.1 - t * q.2) (1 * (q.1 : ℂ)) a :=
        ((hasDerivAt_id a).mul_const (q.1 : ℂ)).sub_const _
      have h2 := (h1.cexp).mul_const (rhoG P g q.1 q.2 : ℂ)
      refine h2.congr_deriv ?_
      ring)
  exact hkey.2.differentiableAt

include hspec in
/-- **Theorem A: real `a`, complex `t`.** -/
theorem bmv2G_of_RI (hRI : Hyp_RI_gen M) (a : ℝ) (t : ℂ) :
    bmvDG hP g a t = (a : ℂ) ^ 2 * laplaceG P g a t := by
  by_cases ha : a = 0
  · subst ha
    simp [bmvDG]
  · have hL := differentiable_bmvDG_t hP (g := g) (a : ℂ)
    have hR : Differentiable ℂ (fun t : ℂ => (a : ℂ) ^ 2 * laplaceG P g a t) :=
      (differentiable_laplaceG_t hP hg hspec hRI a).const_mul _
    have hreal : ∀ t : ℝ, bmvDG hP g a t = (a : ℂ) ^ 2 * laplaceG P g a t := by
      intro t
      rw [(bmv2G_real hP hg hRI ha t).2, laplaceG_real]
      push_cast
      ring
    have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), bmvDG hP g a z = (a : ℂ) ^ 2 * laplaceG P g a z :=
      tendsto_inv_nat_nhdsNE.frequently (Frequently.of_forall fun n => hreal _)
    have := AnalyticOnNhd.eq_of_frequently_eq (fun z _ => hL.analyticAt z)
      (fun z _ => hR.analyticAt z) hfreq
    exact congrFun this t

include hspec in
/-- **Theorem A** (THEOREMS.md, Section 1): for all `(a, t) ∈ ℂ²`,
`Tr e^{ag - tP} - Tr e^{a g_d - tP} = a² ∫∫ e^{as - tτ} ρ(s, τ) ds dτ`, from the multi-line Radon
identity `Hyp_RI_gen M`. -/
theorem theoremA_gen (hRI : Hyp_RI_gen M) (a t : ℂ) :
    bmvDG hP g a t = a ^ 2 * laplaceG P g a t := by
  have hL := differentiable_bmvDG_a hP (g := g) t
  have hR : Differentiable ℂ (fun a : ℂ => a ^ 2 * laplaceG P g a t) :=
    (differentiable_id.pow 2).mul (differentiable_laplaceG_a hP hg hspec hRI t)
  have hreal : ∀ a : ℝ, bmvDG hP g a t = (a : ℂ) ^ 2 * laplaceG P g a t :=
    fun a => bmv2G_of_RI hP hg hspec hRI a t
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), bmvDG hP g z t = z ^ 2 * laplaceG P g z t :=
    tendsto_inv_nat_nhdsNE.frequently (Frequently.of_forall fun n => hreal _)
  have := AnalyticOnNhd.eq_of_frequently_eq (fun z _ => hL.analyticAt z)
    (fun z _ => hR.analyticAt z) hfreq
  exact congrFun this a

end TheoremA

end HarmonicMajorization
