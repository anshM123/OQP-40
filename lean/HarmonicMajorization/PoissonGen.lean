import OQP27.StripFromBMV

/-!
# The strip balayage of a density with an integrable `τ`-profile, and the two-sweep Poisson core

Authors: Ansh Mishra, Aryan Senthilkumar.  License: MIT.

This file generalises two pieces of module L3a of the OQP27 development
(`OQP27/StripFromBMV.lean`, `OQP27/StripPoisson.lean`) from a projection `B` to a general `0 ≤ B ≤ 1`:

* `DensityRegG F`: the regularity used for the defect `V(λ) = ∫_0^1 ∫ K_{1-τ}(s - λ) F(s,τ) ds dτ`, with
  the bound `F(s, τ) ≤ Φ(τ)` for an integrable `Φ` (in place of `C/√(τ(1-τ))`, which fails for interior
  eigenvalues of `B`; THEOREMS.md, Lemma 2.2(6));
* the balayage lemmas: integrability, `V = ∫∫ K F` over `ℝ²`, continuity of `V`
  (`DensityRegG.continuous_stripBalayage`; this is the step that closes the gap noted in
  CHECK_REPORT.md), and the Fourier transform of `V`;
* the two-sweep core: for two multisets `S, S₀` in the closed strip with equal mass and first moment,
  `λ ↦ Σ_{ν ∈ S} h_λ(ν) - Σ_{ν ∈ S₀} h_λ(ν)` is continuous, equals an integrable ramp defect, and its
  Fourier transform is `-(ρ̂_S - ρ̂_{S₀})/κ²` (`fourier_rampDefect2`).

No hypotheses.
-/

set_option autoImplicit false

namespace HarmonicMajorization

open Real MeasureTheory Set Filter Topology Complex
open OQP27.StripL3a (stripKernel stripBalayage balayageProd hLam psiRamp rampKer sinhRatio)

/-! ### Regularity of a density -/

/-- Regularity of a density `F(s, τ)`: measurable, `F ≥ 0`, `F = 0` unless `0 < τ < 1`, compact
support in `s`, and `F(s, τ) ≤ Φ(τ)` for an integrable `Φ ≥ 0`. -/
structure DensityRegG (F : ℝ → ℝ → ℝ) : Prop where
  measurable : Measurable (Function.uncurry F)
  nonneg : ∀ s τ, 0 ≤ F s τ
  zero_of_not_mem : ∀ s τ, ¬ (0 < τ ∧ τ < 1) → F s τ = 0
  support : ∃ R : ℝ, 0 < R ∧ ∀ s τ : ℝ, R ≤ |s| → F s τ = 0
  bound : ∃ Φ : ℝ → ℝ, Integrable Φ ∧ (∀ τ, 0 ≤ Φ τ) ∧ ∀ s τ, F s τ ≤ Φ τ

section Density

variable {F : ℝ → ℝ → ℝ} (hF : DensityRegG F)
include hF

lemma DensityRegG.measurable_section (τ : ℝ) : Measurable (fun s => F s τ) :=
  hF.measurable.comp (measurable_id.prodMk measurable_const)

lemma DensityRegG.integrable : Integrable (fun q : ℝ × ℝ => F q.1 q.2) := by
  obtain ⟨R, hR, hsupp⟩ := hF.support
  obtain ⟨Φ, hΦi, hΦ0, hΦ⟩ := hF.bound
  have hdom : Integrable (fun q : ℝ × ℝ => (Set.indicator (Icc (-R) R) (fun _ => (1:ℝ)) q.1)
      * Φ q.2) (volume.prod volume) :=
    Integrable.mul_prod ((integrable_indicator_iff measurableSet_Icc).mpr
      (integrableOn_const (by simp))) hΦi
  rw [← Measure.volume_eq_prod] at hdom
  refine hdom.mono' hF.measurable.aestronglyMeasurable (Eventually.of_forall fun q => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (hF.nonneg _ _)]
  by_cases hs : q.1 ∈ Icc (-R) R
  · rw [Set.indicator_of_mem hs, one_mul]; exact hΦ q.1 q.2
  · rw [Set.indicator_of_notMem hs, zero_mul]
    have : R ≤ |q.1| := by
      simp only [mem_Icc, not_and_or, not_le] at hs
      rcases hs with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    rw [hsupp q.1 q.2 this]

lemma DensityRegG.integrable_cexp_mul (a t : ℂ) :
    Integrable (fun q : ℝ × ℝ => cexp (a * q.1 - t * q.2) * (F q.1 q.2 : ℂ)) := by
  obtain ⟨R, hR, hsupp⟩ := hF.support
  refine (hF.integrable.ofReal.const_mul (Real.exp (‖a‖ * R + ‖t‖))).mono'
    ((by fun_prop : Continuous fun q : ℝ × ℝ => cexp (a * q.1 - t * q.2)).aestronglyMeasurable.mul
      (Complex.measurable_ofReal.comp hF.measurable).aestronglyMeasurable)
    (Eventually.of_forall fun q => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hF.nonneg _ _)]
  by_cases hq : F q.1 q.2 = 0
  · rw [hq]; simp
  · have hτ : 0 < q.2 ∧ q.2 < 1 := by
      by_contra h; exact hq (hF.zero_of_not_mem _ _ h)
    have hs : |q.1| < R := by
      by_contra h; exact hq (hsupp _ _ (not_lt.mp h))
    have hn : ‖cexp (a * q.1 - t * q.2)‖ ≤ Real.exp (‖a‖ * R + ‖t‖) := by
      rw [Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      have h1 : (a * q.1 - t * q.2).re ≤ ‖a * q.1 - t * q.2‖ := Complex.re_le_norm _
      have h2 : ‖a * q.1 - t * q.2‖ ≤ ‖a‖ * |q.1| + ‖t‖ * |q.2| := by
        calc ‖a * q.1 - t * q.2‖ ≤ ‖a * q.1‖ + ‖t * q.2‖ := norm_sub_le _ _
          _ = ‖a‖ * |q.1| + ‖t‖ * |q.2| := by
            rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
              Real.norm_eq_abs]
      have h3 : ‖a‖ * |q.1| ≤ ‖a‖ * R := mul_le_mul_of_nonneg_left hs.le (norm_nonneg _)
      have h4 : ‖t‖ * |q.2| ≤ ‖t‖ := by
        rw [abs_of_pos hτ.1]; nlinarith [norm_nonneg t]
      linarith
    exact mul_le_mul_of_nonneg_right hn (hF.nonneg _ _)

/-- The iterated integral `∫_0^1 ∫_ℝ` is the integral over `ℝ × ℝ`. -/
lemma DensityRegG.iterated_eq_prod (G : ℝ × ℝ → ℂ)
    (hG : Integrable (fun q : ℝ × ℝ => G q * (F q.1 q.2 : ℂ))) :
    ∫ τ in (0:ℝ)..1, ∫ s : ℝ, G (s, τ) * (F s τ : ℂ)
      = ∫ q : ℝ × ℝ, G q * (F q.1 q.2 : ℂ) := by
  rw [Measure.volume_eq_prod] at hG ⊢
  rw [integral_prod_symm _ hG, intervalIntegral.integral_of_le zero_le_one]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro τ hτ
  have hτ' : ¬ (0 < τ ∧ τ < 1) := fun h => hτ ⟨h.1, h.2.le⟩
  simp [hF.zero_of_not_mem _ _ hτ']

lemma DensityRegG.kernel_mul_nonneg (s τ w : ℝ) : 0 ≤ stripKernel (1 - τ) (s - w) * F s τ := by
  by_cases hτ : 0 < τ ∧ τ < 1
  · exact mul_nonneg (OQP27.StripL3a.stripKernel_pos (X := 1 - τ) (by linarith [hτ.2])
      (by linarith [hτ.1]) _).le (hF.nonneg _ _)
  · rw [hF.zero_of_not_mem _ _ hτ, mul_zero]

lemma DensityRegG.measurable_joint :
    Measurable (fun p : ℝ × (ℝ × ℝ) => stripKernel (1 - p.2.2) (p.2.1 - p.1) * F p.2.1 p.2.2) := by
  have hK : Measurable (fun p : ℝ × (ℝ × ℝ) => stripKernel (1 - p.2.2) (p.2.1 - p.1)) :=
    OQP27.StripL3a.measurable_stripKernel_comp (measurable_const.sub measurable_snd.snd)
      (measurable_snd.fst.sub measurable_fst)
  exact hK.mul (hF.measurable.comp measurable_snd)

lemma DensityRegG.integrable_joint :
    Integrable (fun p : ℝ × (ℝ × ℝ) => stripKernel (1 - p.2.2) (p.2.1 - p.1) * F p.2.1 p.2.2) := by
  rw [Measure.volume_eq_prod]
  rw [integrable_prod_iff' hF.measurable_joint.aestronglyMeasurable]
  constructor
  · refine Eventually.of_forall fun q => ?_
    by_cases hτ : 0 < q.2 ∧ q.2 < 1
    · dsimp only
      exact (OQP27.StripL3a.integrable_stripKernel_sub (X := 1 - q.2) (by linarith [hτ.2])
        (by linarith [hτ.1]) q.1).mul_const _
    · simp [hF.zero_of_not_mem _ _ hτ]
  · have e : (fun q : ℝ × ℝ => ∫ w, ‖stripKernel (1 - q.2) (q.1 - w) * F q.1 q.2‖)
        = fun q => (if 0 < q.2 ∧ q.2 < 1 then q.2 else 0) * F q.1 q.2 := by
      funext q
      by_cases hτ : 0 < q.2 ∧ q.2 < 1
      · rw [if_pos hτ]
        have : (fun w => ‖stripKernel (1 - q.2) (q.1 - w) * F q.1 q.2‖)
            = fun w => stripKernel (1 - q.2) (q.1 - w) * F q.1 q.2 := by
          funext w
          rw [Real.norm_eq_abs, abs_of_nonneg (hF.kernel_mul_nonneg _ _ _)]
        rw [this, integral_mul_const, OQP27.StripL3a.integral_stripKernel_one_sub_sub' hτ.1 hτ.2]
      · rw [if_neg hτ, hF.zero_of_not_mem _ _ hτ]; simp
    rw [e]
    refine hF.integrable.mono'
      ((Measurable.ite ((measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_lt measurable_snd measurable_const)) measurable_snd measurable_const).mul
        hF.measurable).aestronglyMeasurable (Eventually.of_forall fun q => ?_)
    rw [Real.norm_eq_abs]
    by_cases hτ : 0 < q.2 ∧ q.2 < 1
    · rw [if_pos hτ, abs_of_nonneg (mul_nonneg hτ.1.le (hF.nonneg _ _))]
      nlinarith [hF.nonneg q.1 q.2, hτ.2]
    · rw [if_neg hτ, zero_mul, abs_zero]; exact hF.nonneg _ _

lemma DensityRegG.integrable_balayageProd : Integrable (balayageProd F) := by
  have h := hF.integrable_joint
  rw [Measure.volume_eq_prod] at h
  exact h.integral_prod_left

/-- Fourier transform of the balayage: `∫ e^{iκw} V(w) dw = ∫∫ e^{iκs} sinh(κτ)/sinh κ F(s, τ)`. -/
lemma DensityRegG.fourier_balayageProd {κ : ℝ} (hκ : κ ≠ 0) :
    ∫ w : ℝ, cexp (I * κ * w) * (balayageProd F w : ℂ)
      = ∫ q : ℝ × ℝ, cexp (I * κ * q.1) * (sinhRatio (1 - q.2) κ : ℂ) * (F q.1 q.2 : ℂ) := by
  have hJ := hF.integrable_joint
  rw [Measure.volume_eq_prod] at hJ
  have e1 : ∀ w : ℝ, cexp (I * κ * w) * (balayageProd F w : ℂ)
      = ∫ q : ℝ × ℝ, cexp (I * κ * w) * ((stripKernel (1 - q.2) (q.1 - w) * F q.1 q.2 : ℝ) : ℂ) := by
    intro w
    unfold balayageProd
    rw [← integral_complex_ofReal, ← integral_const_mul]
  simp_rw [e1]
  rw [integral_integral_swap]
  · congr 1
    funext q
    by_cases hτ : 0 < q.2 ∧ q.2 < 1
    · have e2 : (fun w : ℝ => cexp (I * κ * w) * ((stripKernel (1 - q.2) (q.1 - w) * F q.1 q.2 : ℝ) : ℂ))
          = fun w : ℝ => cexp (I * κ * w) * (stripKernel (1 - q.2) (q.1 - w) : ℂ) * (F q.1 q.2 : ℂ) := by
        funext w; push_cast; ring
      rw [e2, integral_mul_const,
        OQP27.StripL3a.fourier_stripKernel_sub (by linarith [hτ.2]) (by linarith [hτ.1]) q.1 hκ]
    · simp [hF.zero_of_not_mem _ _ hτ]
  · refine (hJ.ofReal (𝕜 := ℂ)).bdd_mul (c := 1)
      ((by fun_prop : Continuous fun p : ℝ × (ℝ × ℝ) => cexp (I * κ * p.1)).aestronglyMeasurable)
      (Eventually.of_forall fun p => ?_)
    rw [Complex.norm_exp]; simp

/-- For fixed `w`, `(s, τ) ↦ K_{1-τ}(s - w) F(s, τ)` is integrable. -/
lemma DensityRegG.integrable_section (w : ℝ) :
    Integrable (fun q : ℝ × ℝ => stripKernel (1 - q.2) (q.1 - w) * F q.1 q.2) := by
  obtain ⟨Φ, hΦi, hΦ0, hΦ⟩ := hF.bound
  have hmeas : Measurable (fun q : ℝ × ℝ => stripKernel (1 - q.2) (q.1 - w) * F q.1 q.2) :=
    (OQP27.StripL3a.measurable_stripKernel_comp (measurable_const.sub measurable_snd)
      (measurable_fst.sub measurable_const)).mul hF.measurable
  rw [Measure.volume_eq_prod, integrable_prod_iff' hmeas.aestronglyMeasurable]
  have hsec : ∀ τ : ℝ, ∫ s : ℝ, ‖stripKernel (1 - τ) (s - w) * F s τ‖ ≤ Φ τ := by
    intro τ
    by_cases hτ : 0 < τ ∧ τ < 1
    · have hK : ∀ s, 0 ≤ stripKernel (1 - τ) (s - w) :=
        fun s => (OQP27.StripL3a.stripKernel_pos (X := 1 - τ) (by linarith [hτ.2])
          (by linarith [hτ.1]) _).le
      have hint : Integrable (fun s : ℝ => stripKernel (1 - τ) (s - w) * Φ τ) :=
        ((OQP27.StripL3a.integrable_stripKernel (X := 1 - τ) (by linarith [hτ.2])
          (by linarith [hτ.1])).comp_sub_right w).mul_const _
      calc ∫ s : ℝ, ‖stripKernel (1 - τ) (s - w) * F s τ‖
          ≤ ∫ s : ℝ, stripKernel (1 - τ) (s - w) * Φ τ := by
            refine integral_mono_of_nonneg (Eventually.of_forall fun s => norm_nonneg _) hint
              (Eventually.of_forall fun s => ?_)
            dsimp only
            rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hK s) (hF.nonneg _ _))]
            exact mul_le_mul_of_nonneg_left (hΦ s τ) (hK s)
        _ = τ * Φ τ := by
            rw [integral_mul_const, OQP27.StripL3a.integral_stripKernel_one_sub_sub hτ.1 hτ.2]
        _ ≤ Φ τ := by nlinarith [hΦ0 τ, hτ.2]
    · simp [hF.zero_of_not_mem _ _ hτ, hΦ0 τ]
  constructor
  · refine Eventually.of_forall fun τ => ?_
    by_cases hτ : 0 < τ ∧ τ < 1
    · refine (((OQP27.StripL3a.integrable_stripKernel (X := 1 - τ) (by linarith [hτ.2])
        (by linarith [hτ.1])).comp_sub_right w).mul_const (Φ τ)).mono'
        (hmeas.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
        (Eventually.of_forall fun s => ?_)
      have hK := (OQP27.StripL3a.stripKernel_pos (X := 1 - τ) (by linarith [hτ.2])
        (by linarith [hτ.1]) (s - w)).le
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK (hF.nonneg _ _))]
      exact mul_le_mul_of_nonneg_left (hΦ s τ) hK
    · simp [hF.zero_of_not_mem _ _ hτ]
  · refine hΦi.mono' ?_ (Eventually.of_forall fun τ => ?_)
    · exact (hmeas.norm.comp measurable_swap).aestronglyMeasurable.integral_prod_right'
    · rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun s => norm_nonneg _)]
      exact hsec τ

/-- The iterated form of `V` equals the product form. -/
lemma DensityRegG.stripBalayage_eq (w : ℝ) : stripBalayage F w = balayageProd F w := by
  have h := hF.integrable_section w
  unfold stripBalayage balayageProd
  rw [Measure.volume_eq_prod] at h ⊢
  rw [integral_prod_symm _ h, intervalIntegral.integral_of_le zero_le_one]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro τ hτ
  have hτ' : ¬ (0 < τ ∧ τ < 1) := fun h => hτ ⟨h.1, h.2.le⟩
  simp [hF.zero_of_not_mem _ _ hτ']

lemma DensityRegG.stripBalayage_nonneg (w : ℝ) : 0 ≤ stripBalayage F w := by
  unfold stripBalayage
  refine intervalIntegral.integral_nonneg zero_le_one (fun τ _ => ?_)
  exact integral_nonneg fun s => hF.kernel_mul_nonneg s τ w

/-- **`V` is continuous** (dominated convergence with the bound `τ Φ(τ)`). -/
lemma DensityRegG.continuous_stripBalayage : Continuous (stripBalayage F) := by
  obtain ⟨R, hR, hsupp⟩ := hF.support
  obtain ⟨Φ, hΦi, hΦ0, hΦ⟩ := hF.bound
  have e : stripBalayage F = fun w => ∫ τ in Ioc (0:ℝ) 1, ∫ s : ℝ,
      stripKernel (1 - τ) (s - w) * F s τ := by
    funext w; unfold stripBalayage; rw [intervalIntegral.integral_of_le zero_le_one]
  rw [e]
  refine continuous_of_dominated (bound := Φ) (fun w => ?_) (fun w => ?_) hΦi.integrableOn ?_
  · have hmeas : Measurable (fun q : ℝ × ℝ => stripKernel (1 - q.1) (q.2 - w) * F q.2 q.1) :=
      (OQP27.StripL3a.measurable_stripKernel_comp (measurable_const.sub measurable_fst)
        (measurable_snd.sub measurable_const)).mul
        (hF.measurable.comp measurable_swap)
    exact hmeas.aestronglyMeasurable.integral_prod_right'.restrict
  · refine Eventually.of_forall fun τ => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun s => hF.kernel_mul_nonneg s τ w)]
    by_cases hτ : 0 < τ ∧ τ < 1
    · have hK : ∀ s, 0 ≤ stripKernel (1 - τ) (s - w) :=
        fun s => (OQP27.StripL3a.stripKernel_pos (X := 1 - τ) (by linarith [hτ.2])
          (by linarith [hτ.1]) _).le
      have hint : Integrable (fun s : ℝ => stripKernel (1 - τ) (s - w) * Φ τ) :=
        ((OQP27.StripL3a.integrable_stripKernel (X := 1 - τ) (by linarith [hτ.2])
          (by linarith [hτ.1])).comp_sub_right w).mul_const _
      calc ∫ s : ℝ, stripKernel (1 - τ) (s - w) * F s τ
          ≤ ∫ s : ℝ, stripKernel (1 - τ) (s - w) * Φ τ := by
            refine integral_mono_of_nonneg
              (Eventually.of_forall fun s => hF.kernel_mul_nonneg s τ w)
              hint (Eventually.of_forall fun s => ?_)
            exact mul_le_mul_of_nonneg_left (hΦ s τ) (hK s)
        _ = τ * Φ τ := by
            rw [integral_mul_const, OQP27.StripL3a.integral_stripKernel_one_sub_sub hτ.1 hτ.2]
        _ ≤ Φ τ := by nlinarith [hΦ0 τ, hτ.2]
    · simp [hF.zero_of_not_mem _ _ hτ, hΦ0 τ]
  · refine Eventually.of_forall fun τ => ?_
    by_cases hτ : 0 < τ ∧ τ < 1
    · have h0 : 0 < 1 - τ := by linarith [hτ.2]
      have h1 : 1 - τ < 1 := by linarith [hτ.1]
      have hFint : Integrable (fun s => F s τ) := by
        refine ((integrable_indicator_iff measurableSet_Icc).mpr
          (integrableOn_const (μ := volume) (s := Icc (-R) R) (C := Φ τ) (by simp))).mono'
          (hF.measurable_section τ).aestronglyMeasurable (Eventually.of_forall fun s => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (hF.nonneg _ _)]
        by_cases hs : s ∈ Icc (-R) R
        · rw [Set.indicator_of_mem hs]; exact hΦ s τ
        · rw [Set.indicator_of_notMem hs]
          have : R ≤ |s| := by
            simp only [mem_Icc, not_and_or, not_le] at hs
            rcases hs with h | h
            · rw [abs_of_neg (by linarith)]; linarith
            · rw [abs_of_pos (by linarith)]; linarith
          rw [hsupp s τ this]
      refine continuous_of_dominated (bound := fun s => stripKernel (1 - τ) 0 * F s τ)
        (fun w => ?_) (fun w => Eventually.of_forall fun s => ?_) (hFint.const_mul _)
        (Eventually.of_forall fun s => ?_)
      · exact (((OQP27.StripL3a.continuous_stripKernel h0 h1).comp
          (continuous_id.sub continuous_const)).measurable.mul
          (hF.measurable_section τ)).aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
          (OQP27.StripL3a.stripKernel_pos h0 h1 _).le (hF.nonneg _ _))]
        exact mul_le_mul_of_nonneg_right (OQP27.StripL3a.stripKernel_le_zero h0 h1 _)
          (hF.nonneg _ _)
      · exact ((OQP27.StripL3a.continuous_stripKernel h0 h1).comp
          (continuous_const.sub continuous_id)).mul continuous_const
    · simp only [hF.zero_of_not_mem _ _ hτ, mul_zero, integral_zero]
      exact continuous_const

/-- If `V(λ) = 0` for one `λ`, then `F = 0` almost everywhere. -/
lemma DensityRegG.ae_zero_of_stripBalayage_eq_zero {lam : ℝ} (h : stripBalayage F lam = 0) :
    (fun q : ℝ × ℝ => F q.1 q.2) =ᵐ[volume] 0 := by
  rw [hF.stripBalayage_eq] at h
  unfold balayageProd at h
  have hnn : 0 ≤ fun q : ℝ × ℝ => stripKernel (1 - q.2) (q.1 - lam) * F q.1 q.2 :=
    fun q => hF.kernel_mul_nonneg q.1 q.2 lam
  have hae := (integral_eq_zero_iff_of_nonneg hnn (hF.integrable_section lam)).mp h
  filter_upwards [hae] with q hq
  simp only [Pi.zero_apply] at hq ⊢
  by_cases hτ : 0 < q.2 ∧ q.2 < 1
  · have hK := OQP27.StripL3a.stripKernel_pos (X := 1 - q.2) (by linarith [hτ.2])
      (by linarith [hτ.1]) (q.1 - lam)
    rcases mul_eq_zero.mp hq with h' | h'
    · linarith
    · exact h'
  · exact hF.zero_of_not_mem _ _ hτ

/-- If `F = 0` almost everywhere then `V ≡ 0`. -/
lemma DensityRegG.stripBalayage_eq_zero_of_ae (h : (fun q : ℝ × ℝ => F q.1 q.2) =ᵐ[volume] 0)
    (lam : ℝ) : stripBalayage F lam = 0 := by
  rw [hF.stripBalayage_eq]
  unfold balayageProd
  apply integral_eq_zero_of_ae
  filter_upwards [h] with q hq
  simp only [Pi.zero_apply] at hq ⊢
  rw [hq, mul_zero]

end Density

/-! ### The two-sweep core -/

/-- `Φ(λ) = Σ_{ν ∈ S} h_λ(ν) - Σ_{ν ∈ S₀} h_λ(ν)`. -/
noncomputable def poissonDefect2 (S S₀ : Multiset ℂ) (lam : ℝ) : ℝ :=
  (S.map (hLam lam)).sum - (S₀.map (hLam lam)).sum

/-- Its ramp-corrected version `Ψ(λ) = Σ_{ν ∈ S} ψ_ν(λ) - Σ_{ν ∈ S₀} ψ_ν(λ)`. -/
noncomputable def rampDefect2 (S S₀ : Multiset ℂ) (lam : ℝ) : ℝ :=
  (S.map (fun ν => psiRamp ν lam)).sum - (S₀.map (fun ν => psiRamp ν lam)).sum

lemma continuous_poissonDefect2 (S S₀ : Multiset ℂ) : Continuous (poissonDefect2 S S₀) := by
  unfold poissonDefect2
  exact (continuous_multiset_sum S (f := fun ν lam => hLam lam ν)
    (fun ν _ => OQP27.StripL3a.continuous_hLam ν)).sub
    (continuous_multiset_sum S₀ (f := fun ν lam => hLam lam ν)
    (fun ν _ => OQP27.StripL3a.continuous_hLam ν))

lemma poissonDefect2_eq_rampDefect2 (S S₀ : Multiset ℂ) (hS : ∀ ν ∈ S, 0 ≤ ν.re ∧ ν.re ≤ 1)
    (hS₀ : ∀ ν ∈ S₀, 0 ≤ ν.re ∧ ν.re ≤ 1)
    (hmass : (S.map (fun ν => 1 - ν.re)).sum = (S₀.map (fun ν => 1 - ν.re)).sum)
    (hmom : (S.map (fun ν => (1 - ν.re) * ν.im)).sum = (S₀.map (fun ν => (1 - ν.re) * ν.im)).sum)
    (lam : ℝ) :
    poissonDefect2 S S₀ lam = rampDefect2 S S₀ lam := by
  unfold poissonDefect2 rampDefect2
  have h1 : ∀ T : Multiset ℂ, (∀ ν ∈ T, 0 ≤ ν.re ∧ ν.re ≤ 1) →
      (T.map (hLam lam)).sum = (T.map (fun ν => psiRamp ν lam)).sum
        + (T.map (fun ν => if 0 ≤ lam then 0 else (1 - ν.re) * ν.im - lam * (1 - ν.re))).sum := by
    intro T hT
    rw [← Multiset.sum_map_add]
    congr 1
    refine Multiset.map_congr rfl (fun ν hν => ?_)
    have := OQP27.StripL3a.hLam_sub_psiRamp (hT ν hν).1 (hT ν hν).2 lam
    linarith
  rw [h1 S hS, h1 S₀ hS₀]
  split_ifs with hl
  · simp
  · rw [Multiset.sum_map_sub, Multiset.sum_map_sub, Multiset.sum_map_mul_left,
      Multiset.sum_map_mul_left, hmom, hmass]
    ring

lemma integrable_rampDefect2 (S S₀ : Multiset ℂ) : Integrable (rampDefect2 S S₀) := by
  unfold rampDefect2
  exact (OQP27.StripL3a.integrable_multiset_sum_fun S psiRamp
    (fun ν _ => OQP27.StripL3a.integrable_psiRamp ν)).sub
    (OQP27.StripL3a.integrable_multiset_sum_fun S₀ psiRamp
    (fun ν _ => OQP27.StripL3a.integrable_psiRamp ν))

/-- Fourier transform of a single sweep: `∫ e^{iκλ} Σ_{ν∈T} ψ_ν(λ) dλ`. -/
lemma fourier_sum_psiRamp (T : Multiset ℂ) (hT : ∀ ν ∈ T, 0 ≤ ν.re ∧ ν.re ≤ 1) {κ : ℝ}
    (hκ : κ ≠ 0) :
    ∫ lam : ℝ, cexp (I * κ * lam) * (((T.map (fun ν => psiRamp ν lam)).sum : ℝ) : ℂ)
      = ((T.map (fun ν => ((1 - ν.re : ℝ) : ℂ))).sum
          + I * κ * (T.map (fun ν => (((1 - ν.re) * ν.im : ℝ) : ℂ))).sum
          - (T.map (fun ν => cexp (I * κ * ν.im) * (sinhRatio ν.re κ : ℂ))).sum) / κ ^ 2 := by
  have hbdd : ∀ g : ℝ → ℂ, Integrable g →
      Integrable (fun lam : ℝ => cexp (I * κ * lam) * g lam) := by
    intro g hg
    refine hg.bdd_mul (c := 1)
      ((by fun_prop : Continuous fun lam : ℝ => cexp (I * κ * lam)).aestronglyMeasurable)
      (Eventually.of_forall fun lam => ?_)
    rw [Complex.norm_exp]; simp
  have hA : ∀ ν ∈ T, Integrable (fun lam : ℝ => cexp (I * κ * lam) * (psiRamp ν lam : ℂ)) :=
    fun ν _ => hbdd _ (OQP27.StripL3a.integrable_psiRamp ν).ofReal
  have e : (fun lam : ℝ => cexp (I * κ * lam) * (((T.map (fun ν => psiRamp ν lam)).sum : ℝ) : ℂ))
      = fun lam : ℝ => (T.map (fun ν => cexp (I * κ * lam) * (psiRamp ν lam : ℂ))).sum := by
    funext lam
    rw [OQP27.StripL3a.ofReal_multiset_map_sum, ← Multiset.sum_map_mul_left]
  rw [e, OQP27.StripL3a.integral_multiset_sum_fun T _ hA]
  have e1 : (T.map (fun ν => ∫ lam : ℝ, cexp (I * κ * lam) * (psiRamp ν lam : ℂ))) =
      T.map (fun ν => (((1 - ν.re : ℝ) : ℂ) + I * κ * (((1 - ν.re) * ν.im : ℝ) : ℂ)
        - cexp (I * κ * ν.im) * (sinhRatio ν.re κ : ℂ)) / κ ^ 2) :=
    Multiset.map_congr rfl (fun ν hν => OQP27.StripL3a.fourier_psiRamp (hT ν hν).1 (hT ν hν).2 hκ)
  rw [e1, OQP27.StripL3a.multiset_sum_three]

/-- **Fourier transform of the two-sweep ramp defect**: with equal masses and first moments,
`∫ e^{iκλ} Ψ(λ) dλ = -(ρ̂_S(κ) - ρ̂_{S₀}(κ))/κ²`, `ρ̂_T(κ) = Σ_{ν∈T} e^{iκ Im ν} sinh(κ(1 - Re ν))/sinh κ`. -/
lemma fourier_rampDefect2 (S S₀ : Multiset ℂ) (hS : ∀ ν ∈ S, 0 ≤ ν.re ∧ ν.re ≤ 1)
    (hS₀ : ∀ ν ∈ S₀, 0 ≤ ν.re ∧ ν.re ≤ 1)
    (hmass : (S.map (fun ν => 1 - ν.re)).sum = (S₀.map (fun ν => 1 - ν.re)).sum)
    (hmom : (S.map (fun ν => (1 - ν.re) * ν.im)).sum = (S₀.map (fun ν => (1 - ν.re) * ν.im)).sum)
    {κ : ℝ} (hκ : κ ≠ 0) :
    ∫ lam : ℝ, cexp (I * κ * lam) * (rampDefect2 S S₀ lam : ℂ)
      = -((S.map (fun ν => cexp (I * κ * ν.im) * (sinhRatio ν.re κ : ℂ))).sum
          - (S₀.map (fun ν => cexp (I * κ * ν.im) * (sinhRatio ν.re κ : ℂ))).sum) / κ ^ 2 := by
  have hbdd : ∀ g : ℝ → ℂ, Integrable g →
      Integrable (fun lam : ℝ => cexp (I * κ * lam) * g lam) := by
    intro g hg
    refine hg.bdd_mul (c := 1)
      ((by fun_prop : Continuous fun lam : ℝ => cexp (I * κ * lam)).aestronglyMeasurable)
      (Eventually.of_forall fun lam => ?_)
    rw [Complex.norm_exp]; simp
  have hT : ∀ T : Multiset ℂ, Integrable (fun lam : ℝ =>
      cexp (I * κ * lam) * (((T.map (fun ν => psiRamp ν lam)).sum : ℝ) : ℂ)) := fun T =>
    hbdd _ (OQP27.StripL3a.integrable_multiset_sum_fun T psiRamp
      (fun ν _ => OQP27.StripL3a.integrable_psiRamp ν)).ofReal
  have e : (fun lam : ℝ => cexp (I * κ * lam) * (rampDefect2 S S₀ lam : ℂ))
      = fun lam : ℝ => cexp (I * κ * lam) * (((S.map (fun ν => psiRamp ν lam)).sum : ℝ) : ℂ)
        - cexp (I * κ * lam) * (((S₀.map (fun ν => psiRamp ν lam)).sum : ℝ) : ℂ) := by
    funext lam
    unfold rampDefect2
    push_cast
    ring
  rw [e, integral_sub (hT S) (hT S₀), fourier_sum_psiRamp S hS hκ, fourier_sum_psiRamp S₀ hS₀ hκ]
  have hm : (S.map (fun ν => ((1 - ν.re : ℝ) : ℂ))).sum
      = (S₀.map (fun ν => ((1 - ν.re : ℝ) : ℂ))).sum := by
    rw [← OQP27.StripL3a.ofReal_multiset_map_sum, ← OQP27.StripL3a.ofReal_multiset_map_sum, hmass]
  have hmo : (S.map (fun ν => (((1 - ν.re) * ν.im : ℝ) : ℂ))).sum
      = (S₀.map (fun ν => (((1 - ν.re) * ν.im : ℝ) : ℂ))).sum := by
    rw [← OQP27.StripL3a.ofReal_multiset_map_sum, ← OQP27.StripL3a.ofReal_multiset_map_sum, hmom]
  rw [hm, hmo]
  have hκ' : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ
  field_simp
  ring

end HarmonicMajorization
