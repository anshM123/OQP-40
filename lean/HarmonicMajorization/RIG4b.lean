import HarmonicMajorization.RIG4a
import HarmonicMajorization.TheoremAGen

/-!
# The multi-line Radon identity (proof of the multi-line RI, VI)

Authors: Ansh Mishra, Aryan Senthilkumar.  License: MIT.

`P` Hermitian (any spectrum), `A` Hermitian, `A_d = pinchH hP A` (pinching by the spectral
projections of `P`).
Main results:
* `tendsto_imAbsSum_vertical_gen` (Lemma E, general `P`): for `τ ∉ spec P` and real `c₀`,
  `Σ |Im roots(c₀ + iε)| → Σ |Im roots(c₀)|` as `ε → 0⁺`;
* `tendsto_im_PsiG` (Step 3): `Im Ψ(c₀ + iε) → (1/2) Σ_gaps ∫ Σ |Im y_i(τ, c₀)| dτ`;
* `radon_identity_gaps` (Step 4): `(1/2π) Σ_gaps ∫ Σ |Im y_i(τ)| dτ = Tr A_+ - Tr (A_d)_+`;
* `integral_eq_sum_gaps`, `integrable_imAbsSum_gen`;
* **`radon_identity_gen`**: `(1/2π) ∫_ℝ Σ |Im y_i(τ)| dτ = Tr A_+ - Tr (A_d)_+`;
* **`hyp_RI_gen`**: `Hyp_RI_gen M` (`HarmonicMajorization/TheoremAGen.lean`) holds for every `M`.

No hypotheses.
-/

set_option autoImplicit false

namespace HarmonicMajorization

open Matrix Polynomial Complex Metric Filter Topology Set Real MeasureTheory
open OQP27.StripL3b (pencilRoots imAbsSum frob Rt Sup Slo Lup Llo penPoly upperRoots lowerRoots
  upCenter upRadius loCenter Efun Theta1)

variable {M : ℕ}

/-! ### Lemma E for a general Hermitian `P` -/

section Vertical

variable {P A : Matrix (Fin M) (Fin M) ℂ} (hP : P.IsHermitian) (hA : A.IsHermitian)
include hP hA

lemma isHermitian_Nx_gen (τ c₀ x : ℝ) :
    (A + (c₀ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ) - (x : ℂ) • (P - (τ : ℂ) • 1)).IsHermitian :=
  (hA.add (isHermitian_one.smul (OQP27.StripL3b.isSelfAdjoint_ofReal c₀))).sub
    ((OQP27.StripL3b.isHermitian_P_sub hP τ).smul (OQP27.StripL3b.isSelfAdjoint_ofReal x))

/-- **Lemma E (general `P`).**  For real `c₀` and `τ ∉ spec P`,
`Σ |Im roots(c₀ + iε)| → Σ |Im roots(c₀)|` as `ε → 0⁺`. -/
theorem tendsto_imAbsSum_vertical_gen {τ : ℝ} (hτ : τ ∉ spec hP) (c₀ : ℝ) :
    Tendsto (fun ε : ℝ => imAbsSum (Rt P A τ ((c₀ : ℂ) + ε * I))) (𝓝[>] 0)
      (𝓝 (imAbsSum (Rt P A τ c₀))) := by
  set f : ℝ → ℂ[X] := fun ε => penPoly P A τ ((c₀ : ℂ) + ε * I) with hf
  have hfne : ∀ ε, f ε ≠ 0 := fun ε => penPoly_ne_zero_gen hP A hτ _
  have hlc : ∀ ε, (f ε).leadingCoeff = (-(P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ))).det :=
    fun ε => penPoly_leadingCoeff_gen hP A hτ _
  have hdeg : ∀ ε, (f ε).natDegree = M := fun ε => penPoly_natDegree_gen hP A hτ _
  have hroots : ∀ ε, (f ε).roots = Rt P A τ ((c₀ : ℂ) + ε * I) := fun ε =>
    roots_penPoly_gen hP A hτ _
  have hRt0 : Rt P A τ (c₀ : ℂ) = (f 0).roots := by rw [hroots]; simp
  rw [hRt0]
  -- a uniform bound on the roots for `0 ≤ ε ≤ 1`
  have hcont : ContinuousOn
      (fun ε : ℝ => frob (A + ((c₀ : ℂ) + ε * I) • (1 : Matrix (Fin M) (Fin M) ℂ))) (Icc 0 1) := by
    apply Continuous.continuousOn; unfold frob; fun_prop
  obtain ⟨K₀, hK₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  obtain ⟨m, hm0, hmd⟩ := exists_dist_spec_pos hP hτ
  set R₀ := √(max K₀ 0) / m with hR₀
  have hR₀0 : 0 ≤ R₀ := by positivity
  have hrootR : ∀ ε ∈ Icc (0 : ℝ) 1, ∀ z ∈ (f ε).roots, ‖z‖ ≤ R₀ := by
    intro ε hε z hz
    rw [hroots] at hz
    have hB := pencilRoot_norm_bound_dist hP hτ hmd hm0.le _ hz
    have hK : frob (A + ((c₀ : ℂ) + ε * I) • 1) ≤ max K₀ 0 := by
      have := hK₀ ε hε
      rw [Real.norm_eq_abs, abs_of_nonneg (OQP27.StripL3b.frob_nonneg _)] at this
      exact this.trans (le_max_left _ _)
    rw [hR₀, le_div_iff₀ hm0, ← Real.sqrt_sq (norm_nonneg z), ← Real.sqrt_sq hm0.le,
      ← Real.sqrt_mul (sq_nonneg _)]
    exact Real.sqrt_le_sqrt (by nlinarith [hB, hK])
  -- the integrals converge, for every fixed `L`
  have hint : ∀ L : ℝ, Tendsto (fun ε : ℝ => ∫ x in (-L)..L, Real.log ‖(f ε).eval (x : ℂ)‖)
      (𝓝[>] 0) (𝓝 (∫ x in (-L)..L, Real.log ‖(f 0).eval (x : ℂ)‖)) := by
    intro L
    have hnull : (volume : Measure ℝ) {x : ℝ | (x : ℂ) ∈ (f 0).roots} = 0 :=
      (OQP27.StripL3b.finite_real_roots (f 0)).measure_zero _
    have hmono : ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → ∀ x : ℝ,
        ‖(f 0).eval (x : ℂ)‖ ≤ ‖(f ε).eval (x : ℂ)‖ ∧ ‖(f ε).eval (x : ℂ)‖ ≤ ‖(f 1).eval (x : ℂ)‖ := by
      intro ε hε0 hε1 x
      have hN := isHermitian_Nx_gen hP hA τ c₀ x
      simp only [hf]
      rw [OQP27.StripL3b.eval_penPoly_vertical, OQP27.StripL3b.eval_penPoly_vertical,
        OQP27.StripL3b.eval_penPoly_vertical]
      exact ⟨OQP27.StripL3b.norm_det_add_I_mono hN le_rfl hε0,
        OQP27.StripL3b.norm_det_add_I_mono hN hε0 hε1⟩
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun x => |Real.log ‖(f 0).eval (x : ℂ)‖| + |Real.log ‖(f 1).eval (x : ℂ)‖|)
      (Eventually.of_forall fun ε => ?_) ?_ ?_ ?_
    · exact (((Polynomial.continuous _).comp Complex.continuous_ofReal).norm.measurable.log)
        |>.aestronglyMeasurable
    · have hev : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε ∧ ε < 1 := by
        filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (eventually_lt_nhds one_pos)]
          with ε hε1 hε2
        exact ⟨hε1, hε2⟩
      filter_upwards [hev] with ε hε
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with x hx _
      have hx' : (f 0).eval (x : ℂ) ≠ 0 := fun h => hx ((mem_roots (hfne 0)).mpr h)
      have hpos0 : 0 < ‖(f 0).eval (x : ℂ)‖ := norm_pos_iff.mpr hx'
      obtain ⟨hm1, hm2⟩ := hmono ε hε.1.le hε.2.le x
      have hl1 := Real.log_le_log hpos0 hm1
      have hl2 := Real.log_le_log (hpos0.trans_le hm1) hm2
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> [skip; skip] <;>
        cases abs_cases (Real.log ‖(f 0).eval (x : ℂ)‖) <;>
        cases abs_cases (Real.log ‖(f 1).eval (x : ℂ)‖) <;> linarith
    · exact ((OQP27.StripL3b.intervalIntegrable_log_norm_eval (f 0) (hfne 0) _ _).abs).add
        ((OQP27.StripL3b.intervalIntegrable_log_norm_eval (f 1) (hfne 1) _ _).abs)
    · filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with x hx _
      have hx' : (f 0).eval (x : ℂ) ≠ 0 := fun h => hx ((mem_roots (hfne 0)).mpr h)
      have hcε : Continuous fun ε : ℝ => (f ε).eval (x : ℂ) := by
        simp only [hf, OQP27.StripL3b.eval_penPoly']
        exact (Polynomial.continuous _).comp (by fun_prop)
      have hcl : ContinuousAt (fun ε : ℝ => Real.log ‖(f ε).eval (x : ℂ)‖) 0 :=
        (hcε.norm.continuousAt).log (norm_ne_zero_iff.mpr hx')
      exact hcl.tendsto.mono_left nhdsWithin_le_nhds
  -- the `ε`-`δ` argument
  rw [Metric.tendsto_nhds]
  intro η hη
  set L := 2 * R₀ + 1 + 40 * M * R₀ ^ 2 / (π * η) with hL
  have hLpos : 0 < L := by positivity
  have hL2 : 2 * R₀ ≤ L := by
    have : 0 ≤ 40 * M * R₀ ^ 2 / (π * η) := by positivity
    rw [hL]; linarith
  have herr : (M : ℝ) * (10 * R₀ ^ 2 / L) ≤ π * η / 4 := by
    rw [mul_div_assoc', div_le_iff₀ hLpos]
    have hL' : 40 * M * R₀ ^ 2 / (π * η) ≤ L := by rw [hL]; linarith
    have := (div_le_iff₀ (by positivity : 0 < π * η)).mp hL'
    nlinarith [Real.pi_pos]
  have hconv := (Metric.tendsto_nhds.mp (hint L)) (π * η / 2) (by positivity)
  have hev : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε ∧ ε < 1 := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (eventually_lt_nhds one_pos)]
      with ε hε1 hε2
    exact ⟨hε1, hε2⟩
  filter_upwards [hconv, hev] with ε hε hε'
  have hJε := OQP27.StripL3b.jensen_error (f ε) (hfne ε) (hrootR ε ⟨hε'.1.le, hε'.2.le⟩) hL2 hLpos
  have hJ0 := OQP27.StripL3b.jensen_error (f 0) (hfne 0) (hrootR 0 ⟨le_rfl, zero_le_one⟩) hL2 hLpos
  rw [hdeg, hlc] at hJε hJ0
  rw [Real.dist_eq] at hε ⊢
  rw [← hroots ε] at *
  -- combine
  have hπ : 0 < π := Real.pi_pos
  have key : π * |imAbsSum (f ε).roots - imAbsSum (f 0).roots| < π * η := by
    rw [← abs_of_pos hπ, ← abs_mul, abs_of_pos hπ]
    unfold imAbsSum
    have e : π * ((((f ε).roots.map fun z => |z.im|).sum) - ((f 0).roots.map fun z => |z.im|).sum)
        = ((∫ x in (-L)..L, Real.log ‖(f ε).eval (x : ℂ)‖)
            - ∫ x in (-L)..L, Real.log ‖(f 0).eval (x : ℂ)‖)
          - (((∫ x in (-L)..L, Real.log ‖(f ε).eval (x : ℂ)‖)
              - 2 * L * Real.log ‖(-(P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ))).det‖
              - M * (2 * L * Real.log L - 2 * L) - π * ((f ε).roots.map fun z => |z.im|).sum)
            - ((∫ x in (-L)..L, Real.log ‖(f 0).eval (x : ℂ)‖)
              - 2 * L * Real.log ‖(-(P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ))).det‖
              - M * (2 * L * Real.log L - 2 * L) - π * ((f 0).roots.map fun z => |z.im|).sum)) := by
      ring
    rw [e]
    calc |_| ≤ |(∫ x in (-L)..L, Real.log ‖(f ε).eval (x : ℂ)‖)
            - ∫ x in (-L)..L, Real.log ‖(f 0).eval (x : ℂ)‖|
          + (|(∫ x in (-L)..L, Real.log ‖(f ε).eval (x : ℂ)‖)
              - 2 * L * Real.log ‖(-(P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ))).det‖
              - M * (2 * L * Real.log L - 2 * L) - π * ((f ε).roots.map fun z => |z.im|).sum|
            + |(∫ x in (-L)..L, Real.log ‖(f 0).eval (x : ℂ)‖)
              - 2 * L * Real.log ‖(-(P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ))).det‖
              - M * (2 * L * Real.log L - 2 * L) - π * ((f 0).roots.map fun z => |z.im|).sum|) :=
          (abs_sub _ _).trans (add_le_add le_rfl (abs_sub _ _))
      _ < π * η / 2 + (π * η / 4 + π * η / 4) := by
          refine add_lt_add_of_lt_of_le hε (add_le_add (hJε.trans herr) (hJ0.trans herr))
      _ = π * η := by ring
  exact lt_of_mul_lt_mul_left key hπ.le

/-! ### Imaginary parts of the root sums -/

/-- `Im S_+ = (Σ |Im y| + Im Σ y) / 2` off the spectrum. -/
lemma im_Sup_gen {τ : ℝ} (hτ : τ ∉ spec hP) {c : ℂ} (hc : 0 < c.im) :
    (Sup P A τ c).im = (imAbsSum (Rt P A τ c) + ((Rt P A τ c).sum).im) / 2 := by
  obtain ⟨L, U, hL, hU⟩ := eig_bounds hP
  have hS := OQP27.StripL3b.upper_add_lower (Rt_im_ne_zero_gen hP hA hL hU hτ hc)
  unfold Sup
  set S := Rt P A τ c with hSdef
  have hup : ∀ z ∈ upperRoots S, |z.im| = z.im := fun z hz =>
    abs_of_pos (Multiset.of_mem_filter (p := fun z : ℂ => 0 < z.im) hz)
  have hlo : ∀ z ∈ lowerRoots S, |z.im| = -z.im := fun z hz =>
    abs_of_neg (Multiset.of_mem_filter (p := fun z : ℂ => z.im < 0) hz)
  have e1 : imAbsSum S
      = ((upperRoots S).map Complex.im).sum - ((lowerRoots S).map Complex.im).sum := by
    unfold imAbsSum
    conv_lhs => rw [← hS]
    rw [Multiset.map_add, Multiset.sum_add, Multiset.map_congr rfl hup,
      Multiset.map_congr rfl hlo, Multiset.sum_map_neg]
    ring
  have e2 : (S.sum).im
      = ((upperRoots S).map Complex.im).sum + ((lowerRoots S).map Complex.im).sum := by
    conv_lhs => rw [← hS]
    rw [Multiset.sum_add, Complex.add_im, OQP27.StripL3b.im_multiset_sum,
      OQP27.StripL3b.im_multiset_sum]
  rw [OQP27.StripL3b.im_multiset_sum, e1, e2]
  ring

/-- `Im F = (Σ |Im y(A)| - Σ |Im y(A_d)|) / 2` (the trace identity cancels the rest). -/
lemma im_FdG {τ : ℝ} (hτ : τ ∉ spec hP) {c : ℂ} (hc : 0 < c.im) :
    (FdG hP A τ c).im = (imAbsSum (Rt P A τ c) - imAbsSum (Rt P (pinchH hP A) τ c)) / 2 := by
  unfold FdG
  rw [Complex.sub_im, im_Sup_gen hP hA hτ hc, im_Sup_gen hP (isHermitian_pinchH hP hA) hτ hc,
    sum_Rt_pinchH hP A hτ c]
  ring

/-- For real `c₀` the pinched pencil has only real roots. -/
lemma imAbsSum_Rt_pinch_real_gen {τ : ℝ} (hτ : τ ∉ spec hP) (c₀ : ℝ) :
    imAbsSum (Rt P (pinchH hP A) τ c₀) = 0 := by
  have hH : (A + (c₀ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ)).IsHermitian :=
    OQP27.StripL3b.isHermitian_add_real hA c₀
  have hherm := isHermitian_inv_mul_pinchH hP hH hτ
  rw [pinchH_add_smul_one hP A (c₀ : ℂ)] at hherm
  unfold Rt pencilRoots imAbsSum
  rw [hherm.roots_charpoly_eq_eigenvalues, Multiset.map_map]
  simp

/-- For `c₀ ≥ -λ_min(A)` all pencil roots are real. -/
lemma imAbsSum_Rt_eq_zero_of_large_gen {c₀ : ℝ} (hc₀ : ∀ i, -c₀ ≤ hA.eigenvalues i) (τ : ℝ) :
    imAbsSum (Rt P A τ c₀) = 0 := by
  have hpsd := OQP27.StripL3b.posSemidef_sub_smul_one hA hc₀
  have e : A - (((-c₀ : ℝ)) : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ) = A + (c₀ : ℂ) • 1 := by
    rw [Complex.ofReal_neg, neg_smul, sub_neg_eq_add]
  rw [e] at hpsd
  exact imAbsSum_pencilRoots_eq_zero_of_posSemidef hP (Or.inl hpsd) τ

end Vertical

lemma exists_frob_bound_vertical_gen {P : Matrix (Fin M) (Fin M) ℂ} (hP : P.IsHermitian)
    (A : Matrix (Fin M) (Fin M) ℂ) (c₀ : ℝ) :
    ∃ K : ℝ, ∀ ε ∈ Icc (0 : ℝ) 1, frob (A + ((c₀ : ℂ) + ε * I) • 1) ≤ K ∧
      frob (pinchH hP A + ((c₀ : ℂ) + ε * I) • 1) ≤ K := by
  have hc1 : ContinuousOn
      (fun ε : ℝ => frob (A + ((c₀ : ℂ) + ε * I) • (1 : Matrix (Fin M) (Fin M) ℂ))) (Icc 0 1) := by
    apply Continuous.continuousOn; unfold frob; fun_prop
  have hc2 : ContinuousOn
      (fun ε : ℝ => frob (pinchH hP A + ((c₀ : ℂ) + ε * I) • (1 : Matrix (Fin M) (Fin M) ℂ)))
      (Icc 0 1) := by
    apply Continuous.continuousOn; unfold frob; fun_prop
  obtain ⟨K₁, hK₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hc1
  obtain ⟨K₂, hK₂⟩ := isCompact_Icc.exists_bound_of_continuousOn hc2
  refine ⟨max K₁ K₂, fun ε hε => ⟨?_, ?_⟩⟩
  · have := hK₁ ε hε
    rw [Real.norm_eq_abs, abs_of_nonneg (OQP27.StripL3b.frob_nonneg _)] at this
    exact this.trans (le_max_left _ _)
  · have := hK₂ ε hε
    rw [Real.norm_eq_abs, abs_of_nonneg (OQP27.StripL3b.frob_nonneg _)] at this
    exact this.trans (le_max_right _ _)

/-! ### Step 3: boundary values on the real axis -/

/-- `J(c₀) = Σ_gaps ∫_gap Σ |Im y_i(τ, c₀)| dτ`. -/
noncomputable def Jgap {P : Matrix (Fin M) (Fin M) ℂ} (hP : P.IsHermitian)
    (A : Matrix (Fin M) (Fin M) ℂ) (c₀ : ℝ) : ℝ :=
  ∑ k ∈ Finset.range ((spec hP).card - 1),
    ∫ τ in Ioo (sspec hP k) (sspec hP (k + 1)), imAbsSum (Rt P A τ c₀)

section Boundary

variable {P A : Matrix (Fin M) (Fin M) ℂ} (hP : P.IsHermitian) (hA : A.IsHermitian)
include hP hA

/-- **Boundary values on one gap**:
`Im ∫_α^β F(τ, c₀ + iε) dτ → (1/2) ∫_α^β Σ |Im y_i(τ, c₀)| dτ`. -/
theorem tendsto_im_PsiGap {α β : ℝ} (hαβ : α < β) (hgap : ∀ p ∈ spec hP, p ≤ α ∨ β ≤ p)
    (c₀ : ℝ) :
    Tendsto (fun ε : ℝ => (∫ τ in Ioo α β, FdG hP A τ ((c₀ : ℂ) + ε * I)).im) (𝓝[>] 0)
      (𝓝 ((∫ τ in Ioo α β, imAbsSum (Rt P A τ c₀)) / 2)) := by
  have hAd := isHermitian_pinchH hP hA
  obtain ⟨K, hK⟩ := exists_frob_bound_vertical_gen hP A c₀
  have hcpos : ∀ ε : ℝ, 0 < ε → 0 < ((c₀ : ℂ) + ε * I).im := fun ε hε => by simpa using hε
  have heq : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∫ τ in Ioo α β, (FdG hP A τ ((c₀ : ℂ) + (ε : ℂ) * I)).im
        = (∫ τ in Ioo α β, FdG hP A τ ((c₀ : ℂ) + (ε : ℂ) * I)).im := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact OQP27.StripL3b.integral_im_complex
      (integrableOn_FdG_gap hP A hA hαβ hgap (hcpos ε hε))
  refine Tendsto.congr' heq ?_
  rw [← integral_div]
  refine tendsto_integral_filter_of_dominated_convergence
    (fun τ => 2 * M * √K * (1 / √((τ - α) * (β - τ)))) ?_ ?_
    ((integrableOn_arcW hαβ).const_mul _) ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact Complex.continuous_im.comp_aestronglyMeasurable
      (integrableOn_FdG_gap hP A hA hαβ hgap (hcpos ε hε)).1
  · filter_upwards [Ioo_mem_nhdsGT one_pos] with ε hε
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with τ hτ
    rw [Real.norm_eq_abs]
    have hKε := hK ε ⟨hε.1.le, hε.2.le⟩
    exact (Complex.abs_im_le_norm _).trans
      (norm_FdG_le_gap hP A hA hτ.1 hτ.2 hgap (hcpos ε hε.1) hKε.1 hKε.2)
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with τ hτ
    have hτs := not_mem_spec_of_gap hP hτ.1 hτ.2 hgap
    have hlimA := tendsto_imAbsSum_vertical_gen hP hA hτs c₀
    have hlimD := tendsto_imAbsSum_vertical_gen hP hAd hτs c₀
    rw [imAbsSum_Rt_pinch_real_gen hP hA hτs c₀] at hlimD
    have hlim := (hlimA.sub hlimD).div_const 2
    rw [sub_zero] at hlim
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (im_FdG hP hA hτs (hcpos ε hε)).symm

/-- **Step 3**: `Im Ψ(c₀ + iε) → J(c₀)/2` as `ε → 0⁺`. -/
theorem tendsto_im_PsiG (c₀ : ℝ) :
    Tendsto (fun ε : ℝ => (PsiG hP A ((c₀ : ℂ) + ε * I)).im) (𝓝[>] 0) (𝓝 (Jgap hP A c₀ / 2)) := by
  unfold PsiG Jgap
  simp only [Complex.im_sum]
  rw [Finset.sum_div]
  refine tendsto_finsetSum _ fun k hk => ?_
  have hk' : k + 1 < (spec hP).card := by have := Finset.mem_range.mp hk; omega
  exact tendsto_im_PsiGap hP hA (sspec_lt hP (Nat.lt_succ_self k) hk') (sspec_gap hP hk') c₀

/-! ### Step 4: the Radon identity over the gaps -/

/-- **The multi-line Radon identity, gap form**:
`(1/2π) Σ_gaps ∫_gap Σ |Im y_i(τ)| dτ = Tr A_+ - Tr (A_d)_+`. -/
theorem radon_identity_gaps (hM : 0 < M) :
    (∑ k ∈ Finset.range ((spec hP).card - 1),
        ∫ τ in Ioo (sspec hP k) (sspec hP (k + 1)), imAbsSum (pencilRoots P A τ)) / (2 * π)
      = ∑ i, max (hA.eigenvalues i) 0
        - ∑ i, max ((isHermitian_pinchH hP hA).eigenvalues i) 0 := by
  have hAd := isHermitian_pinchH hP hA
  set lam := hA.eigenvalues with hlam
  set lam0 := hAd.eigenvalues with hlam0
  obtain ⟨k, hk⟩ := PsiG_sub_E_affine hP A hA hM
  set β := (PsiG hP A I - Efun lam lam0 I).im with hβ
  have htrace : ∑ i, lam i = ∑ i, lam0 i :=
    OQP27.StripL3b.sum_eigenvalues_eq_of_trace_eq hA hAd (trace_pinchH hP A).symm
  -- the boundary identity for every real `c₀`
  have hbd : ∀ c₀ : ℝ, Jgap hP A c₀ / 2
      - π * (∑ i, max (lam i + c₀) 0 - ∑ i, max (lam0 i + c₀) 0) = β - 2 * π * k * c₀ := by
    intro c₀
    have hconst : ∀ ε : ℝ, 0 < ε → (PsiG hP A ((c₀ : ℂ) + ε * I)).im
        - (Efun lam lam0 ((c₀ : ℂ) + ε * I)).im = β - 2 * π * k * c₀ := by
      intro ε hε
      have h := hk ((c₀ : ℂ) + ε * I) I (by simpa using hε) (by simp)
      have h' := congrArg Complex.im h
      rw [OQP27.StripL3b.im_affine] at h'
      simp only [Complex.sub_im] at h'
      rw [hβ, Complex.sub_im]
      linarith
    have hlim := (tendsto_im_PsiG hP hA c₀).sub (OQP27.StripL3b.tendsto_im_Efun lam lam0 c₀)
    have hlim2 : Tendsto (fun ε : ℝ => (PsiG hP A ((c₀ : ℂ) + ε * I)).im
        - (Efun lam lam0 ((c₀ : ℂ) + ε * I)).im) (𝓝[>] 0) (𝓝 (β - 2 * π * k * c₀)) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact (hconst ε hε).symm
    have huniq := tendsto_nhds_unique hlim hlim2
    rw [← huniq]
    simp only [OQP27.StripL3b.min_zero_eq, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [htrace]
    ring
  -- large `c₀`: both sides vanish
  set C : ℝ := 1 + ∑ i, |lam i| + ∑ i, |lam0 i| with hC
  have hlarge : ∀ c₀ : ℝ, C ≤ c₀ → β - 2 * π * k * c₀ = 0 := by
    intro c₀ hc₀
    have hl : ∀ i, |lam i| ≤ ∑ j, |lam j| := fun i =>
      Finset.single_le_sum (f := fun j => |lam j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    have hl0 : ∀ i, |lam0 i| ≤ ∑ j, |lam0 j| := fun i =>
      Finset.single_le_sum (f := fun j => |lam0 j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    have hs0 : 0 ≤ ∑ j, |lam j| := Finset.sum_nonneg fun j _ => abs_nonneg _
    have hs1 : 0 ≤ ∑ j, |lam0 j| := Finset.sum_nonneg fun j _ => abs_nonneg _
    have hpos : ∀ i, 0 ≤ lam i + c₀ := fun i => by
      linarith [neg_abs_le (lam i), hl i]
    have hpos0 : ∀ i, 0 ≤ lam0 i + c₀ := fun i => by
      linarith [neg_abs_le (lam0 i), hl0 i]
    have hJ : Jgap hP A c₀ = 0 := by
      unfold Jgap
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [setIntegral_congr_fun measurableSet_Ioo (g := fun _ => (0 : ℝ))
        (fun τ _ => imAbsSum_Rt_eq_zero_of_large_gen hP hA (fun i => by linarith [hpos i]) τ)]
      simp
    have hR : ∑ i, max (lam i + c₀) 0 - ∑ i, max (lam0 i + c₀) 0 = 0 := by
      rw [Finset.sum_congr rfl (fun i _ => max_eq_left (hpos i)),
        Finset.sum_congr rfl (fun i _ => max_eq_left (hpos0 i)), Finset.sum_add_distrib,
        Finset.sum_add_distrib, htrace]
      ring
    have := hbd c₀
    rw [hJ, hR] at this
    linarith
  have hk0 : (k : ℝ) = 0 := by
    have h1 := hlarge C le_rfl
    have h2 := hlarge (C + 1) (by linarith)
    have : 2 * π * (k : ℝ) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (by positivity)
    · exact h
  have hβ0 : β = 0 := by
    have := hlarge C le_rfl
    rw [hk0] at this
    linarith
  have h0 := hbd 0
  rw [hβ0, hk0] at h0
  have hRt0 : ∀ τ, Rt P A τ ((0 : ℝ) : ℂ) = pencilRoots P A τ := fun τ => by
    simp [Rt]
  have hJ0 : Jgap hP A 0 = ∑ k ∈ Finset.range ((spec hP).card - 1),
      ∫ τ in Ioo (sspec hP k) (sspec hP (k + 1)), imAbsSum (pencilRoots P A τ) := by
    unfold Jgap
    simp only [hRt0]
  rw [hJ0] at h0
  simp only [add_zero] at h0
  have hπ : (0 : ℝ) < π := Real.pi_pos
  field_simp
  linarith

end Boundary

/-! ### From the gaps to the whole line -/

section Line

variable {P : Matrix (Fin M) (Fin M) ℂ} (hP : P.IsHermitian)

/-- An integrable function vanishing outside `(min spec, max spec)` integrates as the sum over the
gaps. -/
theorem integral_eq_sum_gaps (hM : 0 < M) {f : ℝ → ℝ} (hf : Integrable f)
    (hout : ∀ τ, (τ ≤ sspec hP 0 ∨ sspec hP ((spec hP).card - 1) ≤ τ) → f τ = 0) :
    ∫ τ, f τ = ∑ k ∈ Finset.range ((spec hP).card - 1),
      ∫ τ in Ioo (sspec hP k) (sspec hP (k + 1)), f τ := by
  have hm := card_spec_pos hP hM
  have hLU : sspec hP 0 ≤ sspec hP ((spec hP).card - 1) := sspec_le hP (Nat.zero_le _) (by omega)
  have h1 : ∫ τ in Ioc (sspec hP 0) (sspec hP ((spec hP).card - 1)), f τ = ∫ τ, f τ := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun τ hτ => hout τ ?_
    simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at hτ
    rcases hτ with h | h
    · exact Or.inl h
    · exact Or.inr h.le
  rw [← h1, ← intervalIntegral.integral_of_le hLU,
    ← intervalIntegral.sum_integral_adjacent_intervals (a := sspec hP)
      (n := (spec hP).card - 1) (fun k _ => hf.intervalIntegrable)]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k + 1 < (spec hP).card := by have := Finset.mem_range.mp hk; omega
  rw [intervalIntegral.integral_of_le (sspec_lt hP (Nat.lt_succ_self k) hk').le,
    integral_Ioc_eq_integral_Ioo]

include hP in
/-- `τ ↦ Σ |Im y_i(τ)|` is integrable on `ℝ`. -/
theorem integrable_imAbsSum_gen {H : Matrix (Fin M) (Fin M) ℂ} (hH : H.IsHermitian) :
    Integrable (fun τ => imAbsSum (pencilRoots P H τ)) := by
  have hmeas : Measurable fun τ : ℝ => imAbsSum (pencilRoots P H τ) := by
    have h1 : Measurable fun τ : ℝ => Function.uncurry (rhoG P H) ((0 : ℝ), τ) :=
      (measurable_rhoG hP H).comp (measurable_const.prodMk measurable_id)
    have h2 := h1.const_mul (2 * π)
    have e : (fun τ : ℝ => imAbsSum (pencilRoots P H τ))
        = fun τ => 2 * π * Function.uncurry (rhoG P H) ((0 : ℝ), τ) := by
      funext τ
      simp only [Function.uncurry_apply_pair, rhoG, Complex.ofReal_zero, zero_smul, sub_zero]
      field_simp
    rw [e]
    exact h2
  refine Integrable.mono' ((integrable_domG hP).const_mul (M * √(frob H)))
    hmeas.aestronglyMeasurable (Eventually.of_forall fun τ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (OQP27.StripL3b.imAbsSum_nonneg _)]
  exact imAbsSum_pencilRoots_le_domG hP hH τ

/-- **The multi-line Radon identity** (Theorem RI for a Hermitian `P` with any spectrum):
`(1/2π) ∫_ℝ Σ |Im y_i(τ)| dτ = Tr A_+ - Tr (A_d)_+`, where `y_i(τ)` are the roots of
`det(A - y(P - τ))` and `A_d` is the pinching of `A` by the spectral projections of `P`. -/
theorem radon_identity_gen {A : Matrix (Fin M) (Fin M) ℂ} (hA : A.IsHermitian) :
    (∫ τ, imAbsSum (pencilRoots P A τ)) / (2 * π)
      = ∑ i, max (hA.eigenvalues i) 0
        - ∑ i, max ((isHermitian_pinchH hP hA).eigenvalues i) 0 := by
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM
    have h0 : ∀ τ, imAbsSum (pencilRoots P A τ) = 0 := by
      intro τ
      have hc : (pencilRoots P A τ).card = 0 := OQP27.StripL3b.card_pencilRoots P A τ
      rw [Multiset.card_eq_zero.mp hc]
      simp [imAbsSum]
    simp [h0]
  · have hm := card_spec_pos hP hM
    rw [integral_eq_sum_gaps hP hM (integrable_imAbsSum_gen hP hA) (fun τ hτ => ?_)]
    · exact radon_identity_gaps hP hA hM
    · by_cases hτs : τ ∈ spec hP
      · exact imAbsSum_pencilRoots_of_mem_spec hP hτs A
      · refine imAbsSum_pencilRoots_eq_zero_of_definite hP hA ?_
        rcases hτ with h | h
        · left
          intro p hp
          obtain ⟨j, hj, rfl⟩ := exists_sspec hP hp
          have h1 := sspec_le hP (Nat.zero_le j) hj
          rcases lt_or_eq_of_le (h.trans h1) with h2 | h2
          · exact h2
          · exact (hτs (h2 ▸ sspec_mem hP hj)).elim
        · right
          intro p hp
          obtain ⟨j, hj, rfl⟩ := exists_sspec hP hp
          have h1 := sspec_le hP (show j ≤ (spec hP).card - 1 by omega) (by omega)
          rcases lt_or_eq_of_le (h1.trans h) with h2 | h2
          · exact h2
          · exact (hτs (h2 ▸ sspec_mem hP hj)).elim

end Line

/-- **`Hyp_RI_gen M` holds for every `M`**: the multi-line Radon identity, with integrability. -/
theorem hyp_RI_gen (M : ℕ) : Hyp_RI_gen M := fun _ _ hP hH =>
  ⟨integrable_imAbsSum_gen hP hH, radon_identity_gen hP hH⟩

end HarmonicMajorization
