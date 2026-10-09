import HarmonicMajorization.RIG3b

/-!
# Assembly over the gaps: `Ψ - E` is affine (proof of the multi-line RI, V)

Authors: Ansh Mishra, Aryan Senthilkumar.  License: MIT.

`P` Hermitian with sorted distinct eigenvalues `σ 0 < … < σ (m - 1)` (`sspec`), `A` Hermitian,
`A_d = pinchH hP A`.  Notation: `F = S_+(A) - S_+(A_d)` (`FdG`), `G = Λ_+(A) - Λ_+(A_d)` (`GupG`),
`Ψ(c) = Σ_k ∫_{σ k}^{σ (k+1)} F(τ, c) dτ` (`PsiG`), and `E`, `Θ₁` as in `OQP27/StripRIAssembly.lean`
(with the eigenvalues of `A` and `A_d`).
Main results:
* `diff_global_gen`: Burgers identity `∂_τ G = ∂_c F` off the spectrum, continuity;
* `hasDerivAt_PsiGap`, `tendsto_PsiGap`: Step 1 on one gap;
* `exists_int_GupG_left`: left of the spectrum `G - Θ₁ ≡ 2πik` (all roots lie in `ℂ₊` there);
  `GupG_eq_zero_of_gt`: right of the spectrum `G = 0`;
* `telescope_gaps` and `Gup_cancel` (`RIG3b`): the boundary terms at the interior eigenvalues cancel;
* `PsiG_sub_E_affine` (**Steps 1-2**): `(Ψ - E)(c) - (Ψ - E)(c') = -2πik (c - c')` on `ℂ₊`.

No hypotheses.
-/

set_option autoImplicit false

namespace HarmonicMajorization

open Matrix Polynomial Complex Metric Filter Topology Set Real MeasureTheory
open OQP27.StripL3b (pencilRoots imAbsSum frob Rt Sup Slo Lup Llo penPoly upperRoots lowerRoots
  upCenter upRadius loCenter Efun Theta1)
open scoped Interval

variable {M : ℕ}

/-! ### The sorted spectrum -/

section Sorted

variable {P : Matrix (Fin M) (Fin M) ℂ} (hP : P.IsHermitian)

/-- The sorted distinct eigenvalues `σ 0 < σ 1 < … < σ (m - 1)`, `m = #spec P`
(and `σ k = 0` for `k ≥ m`). -/
noncomputable def sspec (k : ℕ) : ℝ :=
  if h : k < (spec hP).card then (spec hP).orderEmbOfFin rfl ⟨k, h⟩ else 0

lemma sspec_of_lt {k : ℕ} (h : k < (spec hP).card) :
    sspec hP k = (spec hP).orderEmbOfFin rfl ⟨k, h⟩ := dif_pos h

lemma sspec_mem {k : ℕ} (h : k < (spec hP).card) : sspec hP k ∈ spec hP := by
  rw [sspec_of_lt hP h]
  exact Finset.orderEmbOfFin_mem _ _ _

lemma sspec_lt {k l : ℕ} (hkl : k < l) (hl : l < (spec hP).card) :
    sspec hP k < sspec hP l := by
  rw [sspec_of_lt hP (hkl.trans hl), sspec_of_lt hP hl]
  exact ((spec hP).orderEmbOfFin rfl).strictMono (Fin.mk_lt_mk.mpr hkl)

lemma sspec_le {k l : ℕ} (hkl : k ≤ l) (hl : l < (spec hP).card) :
    sspec hP k ≤ sspec hP l := by
  rcases lt_or_eq_of_le hkl with h | h
  · exact (sspec_lt hP h hl).le
  · rw [h]

lemma exists_sspec {p : ℝ} (hp : p ∈ spec hP) : ∃ k < (spec hP).card, sspec hP k = p := by
  have : p ∈ Set.range ((spec hP).orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin]
    exact hp
  obtain ⟨⟨k, hk⟩, hkp⟩ := this
  exact ⟨k, hk, by rw [sspec_of_lt hP hk]; exact hkp⟩

/-- Consecutive sorted eigenvalues bound a gap. -/
lemma sspec_gap {k : ℕ} (hk : k + 1 < (spec hP).card) :
    ∀ p ∈ spec hP, p ≤ sspec hP k ∨ sspec hP (k + 1) ≤ p := by
  intro p hp
  obtain ⟨j, hj, rfl⟩ := exists_sspec hP hp
  rcases le_or_gt j k with h | h
  · exact Or.inl (sspec_le hP h (by omega))
  · exact Or.inr (sspec_le hP h hj)

lemma sum_spec_eq_sum_range (f : ℝ → ℂ) :
    ∑ p ∈ spec hP, f p = ∑ k ∈ Finset.range (spec hP).card, f (sspec hP k) := by
  symm
  refine Finset.sum_nbij (sspec hP) (fun k hk => sspec_mem hP (Finset.mem_range.mp hk)) ?_ ?_
    (fun _ _ => rfl)
  · intro k hk l hl hkl
    have hk' : k < (spec hP).card := Finset.mem_range.mp (Finset.mem_coe.mp hk)
    have hl' : l < (spec hP).card := Finset.mem_range.mp (Finset.mem_coe.mp hl)
    rcases lt_trichotomy k l with h | h | h
    · exact absurd hkl (sspec_lt hP h hl').ne
    · exact h
    · exact absurd hkl (sspec_lt hP h hk').ne'
  · intro p hp
    obtain ⟨k, hk, rfl⟩ := exists_sspec hP (Finset.mem_coe.mp hp)
    exact ⟨k, Finset.mem_coe.mpr (Finset.mem_range.mpr hk), rfl⟩

lemma card_spec_pos (hM : 0 < M) : 0 < (spec hP).card :=
  Finset.card_pos.mpr ⟨hP.eigenvalues ⟨0, hM⟩, eigenvalues_mem_spec hP _⟩

lemma sspec_zero_le_eig (i : Fin M) :
    sspec hP 0 ≤ hP.eigenvalues i := by
  obtain ⟨j, hj, hji⟩ := exists_sspec hP (eigenvalues_mem_spec hP i)
  rw [← hji]
  exact sspec_le hP (Nat.zero_le j) hj

lemma eig_le_sspec_last (i : Fin M) : hP.eigenvalues i ≤ sspec hP ((spec hP).card - 1) := by
  obtain ⟨j, hj, hji⟩ := exists_sspec hP (eigenvalues_mem_spec hP i)
  rw [← hji]
  exact sspec_le hP (by omega) (by omega)

/-- Crude bounds on the eigenvalues. -/
lemma eig_bounds : ∃ L U : ℝ, (∀ i, L ≤ hP.eigenvalues i) ∧ (∀ i, hP.eigenvalues i ≤ U) := by
  have hsl : ∀ i, |hP.eigenvalues i| ≤ ∑ j, |hP.eigenvalues j| := fun i =>
    Finset.single_le_sum (f := fun j => |hP.eigenvalues j|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ i)
  exact ⟨-(∑ j, |hP.eigenvalues j|), ∑ j, |hP.eigenvalues j|,
    fun i => by linarith [neg_abs_le (hP.eigenvalues i), hsl i],
    fun i => by linarith [le_abs_self (hP.eigenvalues i), hsl i]⟩

lemma not_mem_spec_of_gap {α β τ : ℝ} (hατ : α < τ) (hτβ : τ < β)
    (hgap : ∀ p ∈ spec hP, p ≤ α ∨ β ≤ p) : τ ∉ spec hP := fun h => by
  rcases hgap τ h with h' | h' <;> linarith

end Sorted

/-! ### The differences `F`, `G` and the function `Ψ` -/

section Defs

variable {P : Matrix (Fin M) (Fin M) ℂ} (hP : P.IsHermitian) (A : Matrix (Fin M) (Fin M) ℂ)

/-- `F(τ, c) = S_+(A)(τ, c) - S_+(A_d)(τ, c)`. -/
noncomputable def FdG (τ : ℝ) (c : ℂ) : ℂ := Sup P A τ c - Sup P (pinchH hP A) τ c

/-- `∂_c F`. -/
noncomputable def FdG' (τ : ℝ) (c : ℂ) : ℂ :=
  deriv (fun c => Sup P A τ c) c - deriv (fun c => Sup P (pinchH hP A) τ c) c

/-- `G(τ, c) = Λ_+(A)(τ, c) - Λ_+(A_d)(τ, c)`. -/
noncomputable def GupG (τ : ℝ) (c : ℂ) : ℂ := Lup P A τ c - Lup P (pinchH hP A) τ c

/-- `Ψ(c) = Σ_k ∫_{σ k}^{σ (k+1)} F(τ, c) dτ` (sum over the gaps of the spectrum). -/
noncomputable def PsiG (c : ℂ) : ℂ :=
  ∑ k ∈ Finset.range ((spec hP).card - 1),
    ∫ τ in Ioo (sspec hP k) (sspec hP (k + 1)), FdG hP A τ c

/-- `Ψ_δ(c) = Σ_k ∫_{σ k + δ}^{σ (k+1) - δ} F(τ, c) dτ`. -/
noncomputable def PsiGd (δ : ℝ) (c : ℂ) : ℂ :=
  ∑ k ∈ Finset.range ((spec hP).card - 1),
    ∫ τ in (sspec hP k + δ)..(sspec hP (k + 1) - δ), FdG hP A τ c

end Defs

section Diff

variable {P : Matrix (Fin M) (Fin M) ℂ} (hP : P.IsHermitian) (A : Matrix (Fin M) (Fin M) ℂ)
  (hA : A.IsHermitian)
include hA

theorem diff_global_gen :
    (∀ q ∈ domRIG hP, HasDerivAt (fun c => FdG hP A q.1 c) (FdG' hP A q.1 q.2) q.2) ∧
    (∀ q ∈ domRIG hP, HasDerivAt (fun τ => GupG hP A τ q.2) (FdG' hP A q.1 q.2) q.1) ∧
    ContinuousOn (fun q : ℝ × ℂ => FdG' hP A q.1 q.2) (domRIG hP) ∧
    ContinuousOn (fun q : ℝ × ℂ => FdG hP A q.1 q.2) (domRIG hP) ∧
    ContinuousOn (fun q : ℝ × ℂ => GupG hP A q.1 q.2) (domRIG hP) := by
  obtain ⟨L, U, hL, hU⟩ := eig_bounds hP
  obtain ⟨a1, a2, a3, a4, a5⟩ := upper_global_gen hP hA hL hU
  obtain ⟨b1, b2, b3, b4, b5⟩ := upper_global_gen hP (isHermitian_pinchH hP hA) hL hU
  refine ⟨fun q hq => ?_, fun q hq => ?_, ?_, ?_, ?_⟩
  · have h := (a1 q hq).sub (b1 q hq)
    unfold FdG FdG'
    exact h
  · have h := (a2 q hq).sub (b2 q hq)
    unfold GupG FdG'
    exact h
  · have h := a3.sub b3
    unfold FdG'
    exact h
  · have h := a4.sub b4
    unfold FdG
    exact h
  · have h := a5.sub b5
    unfold GupG
    exact h

/-- **Lemma B(iii)** on a gap: `|F(τ, c)| ≤ 2 M √K / √((τ - α)(β - τ))`. -/
lemma norm_FdG_le_gap {α β τ : ℝ} (hατ : α < τ) (hτβ : τ < β)
    (hgap : ∀ p ∈ spec hP, p ≤ α ∨ β ≤ p) {c : ℂ} (hc : 0 < c.im) {K : ℝ}
    (hK1 : frob (A + c • 1) ≤ K) (hK2 : frob (pinchH hP A + c • 1) ≤ K) :
    ‖FdG hP A τ c‖ ≤ 2 * M * √K * (1 / √((τ - α) * (β - τ))) := by
  have hτ : τ ∉ spec hP := fun h => by rcases hgap τ h with h' | h' <;> linarith
  obtain ⟨L, U, hL, hU⟩ := eig_bounds hP
  have := norm_Sup_sub_le_gap hP hA hατ hτβ hgap hτ hL hU hc hK1 hK2
  unfold FdG
  calc _ ≤ 2 * M * (√K / √((τ - α) * (β - τ))) := this
    _ = _ := by rw [div_eq_mul_one_div]; ring

lemma integrableOn_FdG_gap {α β : ℝ} (hαβ : α < β) (hgap : ∀ p ∈ spec hP, p ≤ α ∨ β ≤ p)
    {c : ℂ} (hc : 0 < c.im) : IntegrableOn (fun τ => FdG hP A τ c) (Ioo α β) := by
  obtain ⟨-, -, -, hcont, -⟩ := diff_global_gen hP A hA
  have hmeas : AEStronglyMeasurable (fun τ => FdG hP A τ c) (volume.restrict (Ioo α β)) := by
    have h := hcont.comp (s := Ioo α β) (Continuous.prodMk_left c).continuousOn
      (fun τ hτ => ⟨not_mem_spec_of_gap hP hτ.1 hτ.2 hgap, hc⟩)
    exact h.aestronglyMeasurable measurableSet_Ioo
  set K := max (frob (A + c • 1)) (frob (pinchH hP A + c • 1))
  refine Integrable.mono' ((integrableOn_arcW hαβ).const_mul (2 * M * √K)) hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with τ hτ
  exact norm_FdG_le_gap hP A hA hτ.1 hτ.2 hgap hc (le_max_left _ _) (le_max_right _ _)

/-- **Step 1 on a gap**: `d/dc ∫_{α+δ}^{β-δ} F dτ = G(β - δ, c) - G(α + δ, c)`. -/
theorem hasDerivAt_PsiGap {α β : ℝ} (hgap : ∀ p ∈ spec hP, p ≤ α ∨ β ≤ p) {δ : ℝ}
    (hδ0 : 0 < δ) (hab : α + δ ≤ β - δ) {c : ℂ} (hc : 0 < c.im) :
    HasDerivAt (fun c => ∫ τ in (α + δ)..(β - δ), FdG hP A τ c)
      (GupG hP A (β - δ) c - GupG hP A (α + δ) c) c := by
  obtain ⟨g1, g2, g3, g4, -⟩ := diff_global_gen hP A hA
  have hr0 : 0 < c.im / 2 := by positivity
  have hbox : Icc (α + δ) (β - δ) ×ˢ closedBall c (c.im / 2) ⊆ domRIG hP := fun q hq =>
    ⟨not_mem_spec_of_gap hP (by linarith [hq.1.1]) (by linarith [hq.1.2]) hgap,
      OQP27.StripL3b.closedBall_im_pos hc q.2 hq.2⟩
  have hderiv := OQP27.StripL3b.hasDerivAt_intervalIntegral_param (F := FdG hP A)
    (F' := FdG' hP A) hab hr0 (g4.mono hbox) (g3.mono hbox)
    (fun τ hτ c' hc' => g1 (τ, c') (hbox ⟨hτ, ball_subset_closedBall hc'⟩))
  refine hderiv.congr_deriv ?_
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun τ => GupG hP A τ c)
    (fun τ hτ => ?_) ?_
  · rw [uIcc_of_le hab] at hτ
    exact g2 (τ, c) (hbox ⟨hτ, mem_closedBall_self hr0.le⟩)
  · apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    have h := g3.comp (s := Icc (α + δ) (β - δ)) (Continuous.prodMk_left c).continuousOn
      (fun τ hτ => hbox ⟨hτ, mem_closedBall_self hr0.le⟩)
    exact h

/-- `∫_{α+δ}^{β-δ} F(τ, c) dτ → ∫_α^β F(τ, c) dτ` as `δ → 0⁺`. -/
theorem tendsto_PsiGap {α β : ℝ} (hαβ : α < β) (hgap : ∀ p ∈ spec hP, p ≤ α ∨ β ≤ p) {c : ℂ}
    (hc : 0 < c.im) :
    Tendsto (fun δ => ∫ τ in (α + δ)..(β - δ), FdG hP A τ c) (𝓝[>] 0)
      (𝓝 (∫ τ in Ioo α β, FdG hP A τ c)) := by
  have hint := integrableOn_FdG_gap hP A hA hαβ hgap hc
  set K := max (frob (A + c • 1)) (frob (pinchH hP A + c • 1))
  have heq : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∫ τ in Ioo α β,
      (Ioc (α + δ) (β - δ)).indicator (fun τ => FdG hP A τ c) τ
        = ∫ τ in (α + δ)..(β - δ), FdG hP A τ c := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < (β - α) / 2 by linarith)] with δ hδ
    have hsub : Ioc (α + δ) (β - δ) ⊆ Ioo α β := fun τ hτ =>
      ⟨by linarith [hδ.1, hτ.1], by linarith [hδ.1, hτ.2]⟩
    rw [intervalIntegral.integral_of_le (by linarith [hδ.2]),
      setIntegral_indicator measurableSet_Ioc, Set.inter_eq_right.mpr hsub]
  refine Tendsto.congr' heq ?_
  refine tendsto_integral_filter_of_dominated_convergence
    (fun τ => 2 * M * √K * (1 / √((τ - α) * (β - τ))))
    (Eventually.of_forall fun δ => hint.1.indicator measurableSet_Ioc)
    (Eventually.of_forall fun δ => ?_) ((integrableOn_arcW hαβ).const_mul _) ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with τ hτ
    rw [Set.indicator_apply]
    split_ifs
    · exact norm_FdG_le_gap hP A hA hτ.1 hτ.2 hgap hc (le_max_left _ _) (le_max_right _ _)
    · rw [norm_zero]; positivity
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with τ hτ
    apply tendsto_const_nhds.congr'
    have hpos : (0 : ℝ) < min (τ - α) (β - τ) := lt_min (by linarith [hτ.1]) (by linarith [hτ.2])
    filter_upwards [Ioo_mem_nhdsGT hpos] with δ hδ
    have h1 := min_le_left (τ - α) (β - τ)
    have h2 := min_le_right (τ - α) (β - τ)
    have hmem : τ ∈ Ioc (α + δ) (β - δ) := ⟨by linarith [hδ.2], by linarith [hδ.2]⟩
    exact (Set.indicator_of_mem (s := Ioc (α + δ) (β - δ)) hmem (fun τ => FdG hP A τ c)).symm

end Diff

/-! ### The two outer regions -/

section Outer

variable {P : Matrix (Fin M) (Fin M) ℂ} (hP : P.IsHermitian)

/-- Right of the spectrum there are no roots in `ℂ₊`. -/
lemma Lup_eq_zero_of_gt {B : Matrix (Fin M) (Fin M) ℂ} (hB : B.IsHermitian) {τ : ℝ}
    (hτ : ∀ i, hP.eigenvalues i < τ) {c : ℂ} (hc : 0 < c.im) : Lup P B τ c = 0 := by
  have hτs : τ ∉ spec hP := fun h => by
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp h
    linarith [hτ i]
  obtain ⟨L, -, hL, -⟩ := eig_bounds hP
  have : upperRoots (Rt P B τ c) = 0 := by
    unfold upperRoots
    rw [Multiset.filter_eq_nil]
    intro y hy hpos
    have h := (pencilRoot_im_bounds_gen hP hB hL (U := τ) (fun i => (hτ i).le) hτs hc hy).2.1 hpos
    rw [sub_self, zero_mul] at h
    linarith
  unfold Lup
  rw [this, Multiset.map_zero, Multiset.sum_zero]

lemma GupG_eq_zero_of_gt {A : Matrix (Fin M) (Fin M) ℂ} (hA : A.IsHermitian) {τ : ℝ}
    (hτ : ∀ i, hP.eigenvalues i < τ) {c : ℂ} (hc : 0 < c.im) : GupG hP A τ c = 0 := by
  unfold GupG
  rw [Lup_eq_zero_of_gt hP hA hτ hc, Lup_eq_zero_of_gt hP (isHermitian_pinchH hP hA) hτ hc,
    sub_zero]

/-- Left of the spectrum all roots lie in `ℂ₊`. -/
lemma upperRoots_eq_of_lt {B : Matrix (Fin M) (Fin M) ℂ} (hB : B.IsHermitian) {τ : ℝ}
    (hτ : ∀ i, τ < hP.eigenvalues i) {c : ℂ} (hc : 0 < c.im) :
    upperRoots (Rt P B τ c) = Rt P B τ c := by
  have hτs : τ ∉ spec hP := fun h => by
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp h
    linarith [hτ i]
  obtain ⟨-, U, -, hU⟩ := eig_bounds hP
  unfold upperRoots
  rw [Multiset.filter_eq_self]
  intro y hy
  obtain ⟨hne, -, hlo⟩ := pencilRoot_im_bounds_gen hP hB (L := τ) (fun i => (hτ i).le) hU hτs hc hy
  rcases lt_or_gt_of_ne hne with h | h
  · have h2 := hlo h
    rw [sub_self, zero_mul] at h2
    linarith
  · exact h

lemma exp_Lup_of_lt {B : Matrix (Fin M) (Fin M) ℂ} (hB : B.IsHermitian) {τ : ℝ}
    (hτ : ∀ i, τ < hP.eigenvalues i) {c : ℂ} (hc : 0 < c.im) :
    Complex.exp (Lup P B τ c)
      = ((P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ))⁻¹ * (B + c • 1)).det := by
  have hτs : τ ∉ spec hP := fun h => by
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp h
    linarith [hτ i]
  obtain ⟨L, U, hL, hU⟩ := eig_bounds hP
  have hne : ∀ y ∈ Rt P B τ c, y ≠ 0 := fun y hy h =>
    (Rt_im_ne_zero_gen hP hB hL hU hτs hc y hy) (by rw [h]; simp)
  unfold Lup
  rw [upperRoots_eq_of_lt hP hB hτ hc, Complex.exp_multiset_sum, Multiset.map_map,
    Multiset.map_congr rfl (f := Complex.exp ∘ Complex.log) (g := fun y => y)
      (fun y hy => Complex.exp_log (hne y hy)),
    Multiset.map_id', Matrix.det_eq_prod_roots_charpoly]
  rfl

lemma exp_GupG_of_lt {A : Matrix (Fin M) (Fin M) ℂ} (hA : A.IsHermitian) {τ : ℝ}
    (hτ : ∀ i, τ < hP.eigenvalues i) {c : ℂ} (hc : 0 < c.im) :
    Complex.exp (GupG hP A τ c)
      = Complex.exp (Theta1 hA.eigenvalues (isHermitian_pinchH hP hA).eigenvalues c) := by
  have hAd := isHermitian_pinchH hP hA
  have hτs : τ ∉ spec hP := fun h => by
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp h
    linarith [hτ i]
  have hD : ((P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ))⁻¹).det ≠ 0 :=
    (Matrix.isUnit_nonsing_inv_det _ (isUnit_det_sub hP hτs)).ne_zero
  unfold GupG Theta1
  rw [Complex.exp_sub, exp_Lup_of_lt hP hA hτ hc, exp_Lup_of_lt hP hAd hτ hc, Complex.exp_sub,
    OQP27.StripL3b.exp_sum_log_eigen hA hc, OQP27.StripL3b.exp_sum_log_eigen hAd hc,
    Matrix.det_mul, Matrix.det_mul, mul_div_mul_left _ _ hD]

/-- Left of the spectrum `G - Θ₁` is a constant in `2πiℤ`. -/
theorem exists_int_GupG_left {A : Matrix (Fin M) (Fin M) ℂ} (hA : A.IsHermitian) :
    ∃ k : ℤ, ∀ τ : ℝ, (∀ i, τ < hP.eigenvalues i) → ∀ c : ℂ, 0 < c.im →
      GupG hP A τ c - Theta1 hA.eigenvalues (isHermitian_pinchH hP hA).eigenvalues c
        = 2 * π * I * k := by
  have hAd := isHermitian_pinchH hP hA
  set S₁ : Set ℝ := ⋂ i, Iio (hP.eigenvalues i) with hS₁
  set D : Set (ℝ × ℂ) := S₁ ×ˢ {c : ℂ | 0 < c.im} with hD
  have hmemS₁ : ∀ τ : ℝ, τ ∈ S₁ ↔ ∀ i, τ < hP.eigenvalues i := by
    intro τ; simp [hS₁]
  have hDsub : D ⊆ domRIG hP := by
    intro q hq
    refine ⟨fun h => ?_, hq.2⟩
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp h
    have := ((hmemS₁ q.1).mp hq.1) i
    linarith
  obtain ⟨-, -, -, -, h5⟩ := diff_global_gen hP A hA
  have hcont : ContinuousOn (fun q : ℝ × ℂ => GupG hP A q.1 q.2
      - Theta1 hA.eigenvalues hAd.eigenvalues q.2) D :=
    (h5.mono hDsub).sub ((OQP27.StripL3b.continuousOn_Theta1 _ _).comp continuous_snd.continuousOn
      (fun q hq => hq.2))
  have hint : ∀ q ∈ D, ∃ n : ℤ, GupG hP A q.1 q.2
      - Theta1 hA.eigenvalues hAd.eigenvalues q.2 = 2 * π * I * n := by
    intro q hq
    have he := exp_GupG_of_lt hP hA ((hmemS₁ q.1).mp hq.1) hq.2
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp he
    exact ⟨n, by rw [hn]; ring⟩
  have hconv : Convex ℝ D :=
    (convex_iInter fun i => convex_Iio (hP.eigenvalues i)).prod (convex_halfSpace_im_gt 0)
  obtain ⟨L, -, hL, -⟩ := eig_bounds hP
  have hq0 : ((L - 1 : ℝ), I) ∈ D :=
    ⟨(hmemS₁ _).mpr fun i => by linarith [hL i], by simp⟩
  obtain ⟨k, hk⟩ := hint _ hq0
  refine ⟨k, fun τ hτ c hc => ?_⟩
  have hq : ((τ, c) : ℝ × ℂ) ∈ D := ⟨(hmemS₁ τ).mpr hτ, hc⟩
  exact (OQP27.StripL3b.eq_of_continuousOn_int hconv.isPreconnected hcont hint hq hq0).trans hk

end Outer

/-! ### Telescoping over the gaps -/

lemma telescope_gaps (G : ℝ → ℂ) (σ : ℕ → ℝ) (n : ℕ) (δ : ℝ) :
    ∑ k ∈ Finset.range n, (G (σ (k + 1) - δ) - G (σ k + δ))
      = ∑ k ∈ Finset.range (n + 1), (G (σ k - δ) - G (σ k + δ)) - G (σ 0 - δ) + G (σ n + δ) := by
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    Finset.sum_range_succ' (fun k => G (σ k - δ)), Finset.sum_range_succ (fun k => G (σ k + δ))]
  ring

/-! ### Steps 1-2: `Ψ - E` is affine -/

section Affine

variable {P : Matrix (Fin M) (Fin M) ℂ} (hP : P.IsHermitian) (A : Matrix (Fin M) (Fin M) ℂ)
  (hA : A.IsHermitian)
include hA

/-- `Ψ_δ(c) → Ψ(c)` as `δ → 0⁺`. -/
theorem tendsto_PsiGd (hM : 0 < M) {c : ℂ} (hc : 0 < c.im) :
    Tendsto (fun δ => PsiGd hP A δ c) (𝓝[>] 0) (𝓝 (PsiG hP A c)) := by
  have hm := card_spec_pos hP hM
  unfold PsiGd PsiG
  refine tendsto_finsetSum _ fun k hk => ?_
  have hk' : k + 1 < (spec hP).card := by have := Finset.mem_range.mp hk; omega
  exact tendsto_PsiGap hP A hA (sspec_lt hP (Nat.lt_succ_self k) hk') (sspec_gap hP hk') hc

/-- The derivative of `Ψ_δ` telescopes into the boundary terms at the eigenvalues. -/
theorem hasDerivAt_PsiGd (hM : 0 < M) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ : ∀ k ∈ Finset.range ((spec hP).card - 1), sspec hP k + δ ≤ sspec hP (k + 1) - δ)
    {k₀ : ℤ}
    (hk₀ : ∀ τ : ℝ, (∀ i, τ < hP.eigenvalues i) → ∀ c : ℂ, 0 < c.im →
      GupG hP A τ c - Theta1 hA.eigenvalues (isHermitian_pinchH hP hA).eigenvalues c
        = 2 * π * I * k₀)
    {c : ℂ} (hc : 0 < c.im) :
    HasDerivAt (fun c => PsiGd hP A δ c)
      (∑ p ∈ spec hP, (GupG hP A (p - δ) c - GupG hP A (p + δ) c)
        - (Theta1 hA.eigenvalues (isHermitian_pinchH hP hA).eigenvalues c + 2 * π * I * k₀)) c := by
  have hm := card_spec_pos hP hM
  have h1 : HasDerivAt (fun c => PsiGd hP A δ c)
      (∑ k ∈ Finset.range ((spec hP).card - 1),
        (GupG hP A (sspec hP (k + 1) - δ) c - GupG hP A (sspec hP k + δ) c)) c := by
    unfold PsiGd
    refine HasDerivAt.fun_sum fun k hk => ?_
    have hk' : k + 1 < (spec hP).card := by have := Finset.mem_range.mp hk; omega
    exact hasDerivAt_PsiGap hP A hA (sspec_gap hP hk') hδ0 (hδ k hk) hc
  refine h1.congr_deriv ?_
  rw [telescope_gaps (fun τ => GupG hP A τ c) (sspec hP), Nat.sub_add_cancel hm,
    ← sum_spec_eq_sum_range hP (fun p => GupG hP A (p - δ) c - GupG hP A (p + δ) c)]
  have hleft := hk₀ (sspec hP 0 - δ) (fun i => by
    have := sspec_zero_le_eig hP i; linarith) c hc
  have hright : GupG hP A (sspec hP ((spec hP).card - 1) + δ) c = 0 :=
    GupG_eq_zero_of_gt hP hA (fun i => by have := eig_le_sspec_last hP i; linarith) hc
  rw [hright]
  linear_combination -hleft

/-- **Steps 1-2 of the proof of the multi-line RI**: there is `k ∈ ℤ` with
`(Ψ - E)(c) - (Ψ - E)(c') = -2πik (c - c')` on `ℂ₊`. -/
theorem PsiG_sub_E_affine (hM : 0 < M) :
    ∃ k : ℤ, ∀ c c' : ℂ, 0 < c.im → 0 < c'.im →
      (PsiG hP A c - Efun hA.eigenvalues (isHermitian_pinchH hP hA).eigenvalues c)
        - (PsiG hP A c' - Efun hA.eigenvalues (isHermitian_pinchH hP hA).eigenvalues c')
        = -(2 * π * I * k) * (c - c') := by
  set lam := hA.eigenvalues with hlam
  set lam0 := (isHermitian_pinchH hP hA).eigenvalues with hlam0
  have hm := card_spec_pos hP hM
  obtain ⟨k, hk⟩ := exists_int_GupG_left hP hA
  refine ⟨k, fun c c' hc hc' => ?_⟩
  set κ : ℂ := 2 * π * I * k with hκ
  set Kseg := segment ℝ c' c with hKseg
  have hKc : IsCompact Kseg := by
    rw [hKseg, segment_eq_image]
    exact isCompact_Icc.image (by fun_prop)
  have hKpos : ∀ z ∈ Kseg, 0 < z.im := fun z hz =>
    (convex_halfSpace_im_gt 0).segment_subset hc' hc hz
  have hKconv : Convex ℝ Kseg := convex_segment c' c
  set X := ‖(PsiG hP A c - Efun lam lam0 c + κ * c) - (PsiG hP A c' - Efun lam lam0 c' + κ * c')‖
    with hX
  have key : ∀ η > 0, X ≤ η * ‖c - c'‖ := by
    intro η hη
    have hmR : (0 : ℝ) < (spec hP).card := by exact_mod_cast hm
    have hev1 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ p ∈ spec hP, ∀ z ∈ Kseg,
        ‖GupG hP A (p - δ) z - GupG hP A (p + δ) z‖ < η / (spec hP).card := by
      rw [Filter.eventually_all_finset]
      intro p hp
      obtain ⟨δ₀, hδ₀, h⟩ := Gup_cancel hP hA hp hKc hKpos (ε := η / (spec hP).card)
        (div_pos hη hmR)
      filter_upwards [Ioo_mem_nhdsGT hδ₀] with δ hδ
      intro z hz
      exact h δ hδ.1 hδ.2 z hz
    have hev2 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ j ∈ Finset.range ((spec hP).card - 1),
        sspec hP j + δ ≤ sspec hP (j + 1) - δ := by
      rw [Filter.eventually_all_finset]
      intro j hj
      have hj' : j + 1 < (spec hP).card := by have := Finset.mem_range.mp hj; omega
      have hlt := sspec_lt hP (Nat.lt_succ_self j) hj'
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < (sspec hP (j + 1) - sspec hP j) / 2 by
        linarith)] with δ hδ
      linarith [hδ.2]
    have hbound : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
        ‖(PsiGd hP A δ c - Efun lam lam0 c + κ * c) - (PsiGd hP A δ c' - Efun lam lam0 c' + κ * c')‖
          ≤ η * ‖c - c'‖ := by
      filter_upwards [hev1, hev2, self_mem_nhdsWithin] with δ h1 h2 hδ
      have hδ0 : 0 < δ := hδ
      have hderiv : ∀ z ∈ Kseg, HasDerivWithinAt
          (fun z => PsiGd hP A δ z - Efun lam lam0 z + κ * z)
          (∑ p ∈ spec hP, (GupG hP A (p - δ) z - GupG hP A (p + δ) z)) Kseg z := by
        intro z hz
        have hz0 := hKpos z hz
        have d1 := hasDerivAt_PsiGd hP A hA hM hδ0 h2 hk hz0
        have d2 := OQP27.StripL3b.hasDerivAt_Efun lam lam0 hz0
        have d3 := (hasDerivAt_id' z).const_mul κ
        have d4 := (d1.sub d2).add d3
        refine (d4.congr_deriv ?_).hasDerivWithinAt
        rw [hκ]
        ring
      have hbd : ∀ z ∈ Kseg, ‖∑ p ∈ spec hP, (GupG hP A (p - δ) z - GupG hP A (p + δ) z)‖ ≤ η := by
        intro z hz
        calc _ ≤ ∑ p ∈ spec hP, ‖GupG hP A (p - δ) z - GupG hP A (p + δ) z‖ := norm_sum_le _ _
          _ ≤ ∑ _p ∈ spec hP, η / (spec hP).card :=
              Finset.sum_le_sum fun p hp => (h1 p hp z hz).le
          _ = η := by
              rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
              exact div_mul_cancel₀ η hmR.ne'
      have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbd hKconv
        (left_mem_segment ℝ c' c) (right_mem_segment ℝ c' c)
      exact hmv
    have hlim : Tendsto (fun δ =>
        ‖(PsiGd hP A δ c - Efun lam lam0 c + κ * c) - (PsiGd hP A δ c' - Efun lam lam0 c' + κ * c')‖)
        (𝓝[>] 0) (𝓝 X) :=
      ((((tendsto_PsiGd hP A hA hM hc).sub_const _).add_const _).sub
        (((tendsto_PsiGd hP A hA hM hc').sub_const _).add_const _)).norm
    exact le_of_tendsto hlim hbound
  have hX0 : X ≤ 0 := by
    by_contra hXpos
    have hXp : 0 < X := not_le.mp hXpos
    have hY : 0 ≤ ‖c - c'‖ := norm_nonneg _
    have h := key (X / (2 * (‖c - c'‖ + 1))) (by positivity)
    have h2 : X / (2 * (‖c - c'‖ + 1)) * ‖c - c'‖ < X := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  have hz : (PsiG hP A c - Efun lam lam0 c + κ * c) - (PsiG hP A c' - Efun lam lam0 c' + κ * c')
      = 0 := norm_eq_zero.mp (le_antisymm hX0 (norm_nonneg _))
  linear_combination hz

end Affine

end HarmonicMajorization
