import HarmonicMajorization.RIG1

/-!
# Local regularity and the Burgers identity off the spectrum (proof of the multi-line RI, II)

Authors: Ansh Mishra, Aryan Senthilkumar.  License: MIT.

`P` Hermitian with eigenvalues in `[L, U]`, `A` Hermitian.  On the open set
`domRIG hP = {(τ, c) : τ ∉ spec P, Im c > 0}`:
* `upper_global_gen`, `lower_global_gen` (Lemma C of [27, Appendix RI], general `P`): `S_±` are
  holomorphic in `c` with jointly continuous derivative, `S_±`, `Λ_±` are continuous, and the Burgers
  identities `∂_τ Λ_± = ∂_c S_±` hold.
The proof reuses `OQP27.StripL3b.local_reg_generic` (contour representation on a fixed circle).

No hypotheses.
-/

set_option autoImplicit false

namespace HarmonicMajorization

open Matrix Polynomial Complex Metric Filter Topology Set Real
open OQP27.StripL3b (pencilRoots imAbsSum frob Rt Sup Slo Lup Llo penPoly upperRoots lowerRoots
  upCenter upRadius loCenter LocalData)

variable {M : ℕ}

/-- A positive lower bound on the distance from `τ ∉ spec P` to the eigenvalues. -/
lemma exists_dist_spec_pos {P : Matrix (Fin M) (Fin M) ℂ} (hP : P.IsHermitian) {τ : ℝ}
    (hτ : τ ∉ spec hP) : ∃ d > 0, ∀ i, d ≤ |hP.eigenvalues i - τ| := by
  rcases isEmpty_or_nonempty (Fin M) with hE | hNE
  · exact ⟨1, one_pos, fun i => isEmptyElim i⟩
  · obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image Finset.univ
      (fun i => |hP.eigenvalues i - τ|) Finset.univ_nonempty
    refine ⟨|hP.eigenvalues i₀ - τ|, ?_, fun i => hi₀ i (Finset.mem_univ i)⟩
    show 0 < |hP.eigenvalues i₀ - τ|
    rw [abs_pos, sub_ne_zero]
    intro h
    exact hτ (h ▸ eigenvalues_mem_spec hP i₀)

section Local

variable {P A : Matrix (Fin M) (Fin M) ℂ} (hP : P.IsHermitian) (hA : A.IsHermitian)
  {L U : ℝ} (hL : ∀ i, L ≤ hP.eigenvalues i) (hU : ∀ i, hP.eigenvalues i ≤ U)
include hP hA hL hU

/-- **Local box.**  Around `(τ₀, c₀)` with `τ₀ ∉ spec P`, `Im c₀ > 0`, the roots stay in fixed compact
parts of `ℂ₊` and `ℂ₋`. -/
theorem local_box_gen {τ₀ : ℝ} (hτ₀ : τ₀ ∉ spec hP) {c₀ : ℂ} (hc₀ : 0 < c₀.im) :
    ∃ δ r η ρ : ℝ, 0 < δ ∧ 0 < r ∧ 0 < η ∧
      (∀ τ ∈ Icc (τ₀ - δ) (τ₀ + δ), τ ∉ spec hP) ∧
      (∀ c ∈ closedBall c₀ r, η ≤ c.im) ∧
      ∀ τ ∈ Icc (τ₀ - δ) (τ₀ + δ), ∀ c ∈ closedBall c₀ r, ∀ y ∈ Rt P A τ c,
        (0 < y.im → η ≤ y.im ∧ ‖y‖ ≤ ρ) ∧ (y.im < 0 → y.im ≤ -η ∧ ‖y‖ ≤ ρ) := by
  obtain ⟨d₀, hd₀, hd⟩ := exists_dist_spec_pos hP hτ₀
  set δ := d₀ / 2 with hδ
  set r := c₀.im / 2 with hr
  set W := |U| + |L| + |τ₀| + d₀ + 1 with hW
  have hW0 : 0 < W := by positivity
  have hcont : ContinuousOn (fun c : ℂ => frob (A + c • (1 : Matrix (Fin M) (Fin M) ℂ)))
      (closedBall c₀ r) := by
    apply Continuous.continuousOn
    unfold frob
    fun_prop
  obtain ⟨K, hK⟩ := (isCompact_closedBall c₀ r).exists_bound_of_continuousOn hcont
  have hdist : ∀ τ ∈ Icc (τ₀ - δ) (τ₀ + δ), ∀ i, d₀ / 2 ≤ |hP.eigenvalues i - τ| := by
    intro τ hτ i
    have h1 := hd i
    have h2 : |τ - τ₀| ≤ d₀ / 2 := by rw [abs_le]; constructor <;> linarith [hτ.1, hτ.2]
    have h3 := abs_sub_abs_le_abs_sub (hP.eigenvalues i - τ₀) (τ - τ₀)
    have h4 : hP.eigenvalues i - τ₀ - (τ - τ₀) = hP.eigenvalues i - τ := by ring
    rw [h4] at h3
    linarith
  have hnotin : ∀ τ ∈ Icc (τ₀ - δ) (τ₀ + δ), τ ∉ spec hP := by
    intro τ hτ hmem
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hmem
    have := hdist τ hτ i
    rw [hi, sub_self, abs_zero] at this
    linarith
  refine ⟨δ, r, r / W, √(max K 0) / (d₀ / 2), by positivity, by positivity, by positivity,
    hnotin, ?_, ?_⟩
  · intro c hc
    have := (Complex.abs_im_le_norm (c - c₀)).trans (le_of_eq (dist_eq_norm c c₀).symm)
    rw [Complex.sub_im] at this
    have h2 := (abs_le.mp (this.trans (mem_closedBall.mp hc))).1
    have hW1 : 1 ≤ W := by
      rw [hW]; linarith [abs_nonneg U, abs_nonneg L, abs_nonneg τ₀]
    have hle : r / W ≤ r := div_le_self (by positivity) hW1
    linarith
  · intro τ hτ c hc y hy
    have hτs := hnotin τ hτ
    have hcim : r ≤ c.im := by
      have := (Complex.abs_im_le_norm (c - c₀)).trans (le_of_eq (dist_eq_norm c c₀).symm)
      rw [Complex.sub_im] at this
      have := (abs_le.mp (this.trans (mem_closedBall.mp hc))).1
      linarith
    have hcpos : 0 < c.im := lt_of_lt_of_le (by positivity) hcim
    obtain ⟨-, hup, hlo⟩ := pencilRoot_im_bounds_gen hP hA hL hU hτs hcpos hy
    have hB := pencilRoot_norm_bound_dist hP hτs (hdist τ hτ) (by positivity) c hy
    have hKc : frob (A + c • 1) ≤ max K 0 := by
      have := hK c hc
      rw [Real.norm_eq_abs, abs_of_nonneg (OQP27.StripL3b.frob_nonneg _)] at this
      exact this.trans (le_max_left _ _)
    have hnorm : ‖y‖ ≤ √(max K 0) / (d₀ / 2) := by
      rw [le_div_iff₀ (by positivity), ← Real.sqrt_sq (norm_nonneg y),
        ← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ d₀ / 2), ← Real.sqrt_mul (sq_nonneg _)]
      exact Real.sqrt_le_sqrt (hB.trans hKc)
    have hτbd : |τ| ≤ |τ₀| + d₀ := by
      have h2 : |τ - τ₀| ≤ d₀ / 2 := by rw [abs_le]; constructor <;> linarith [hτ.1, hτ.2]
      have := abs_sub_abs_le_abs_sub τ τ₀
      linarith
    refine ⟨fun hpos => ⟨?_, hnorm⟩, fun hneg => ⟨?_, hnorm⟩⟩
    · have h1 := hup hpos
      have hUW : U - τ ≤ W := by
        rw [hW]; linarith [le_abs_self U, neg_abs_le τ, abs_nonneg L]
      have h2 : c.im ≤ W * y.im := h1.trans (mul_le_mul_of_nonneg_right hUW hpos.le)
      rw [div_le_iff₀ hW0]
      nlinarith
    · have h1 := hlo hneg
      have hLW : τ - L ≤ W := by
        rw [hW]; linarith [neg_abs_le L, le_abs_self τ, abs_nonneg U]
      have h2 : c.im ≤ W * (-y.im) := by nlinarith
      have : r / W ≤ -y.im := by
        rw [div_le_iff₀ hW0]; nlinarith
      linarith

/-- If the upper roots lie in `{Im ≥ η, |y| ≤ ρ}`, their `φ`-sum is a circle integral. -/
theorem upper_sum_eq_circleIntegral_gen {τ : ℝ} (hτ : τ ∉ spec hP) {c : ℂ} (hc : 0 < c.im)
    {η ρ : ℝ} (hη : 0 < η) (hup : ∀ y ∈ Rt P A τ c, 0 < y.im → η ≤ y.im ∧ ‖y‖ ≤ ρ) {φ : ℂ → ℂ}
    (hφ : DiffContOnCl ℂ φ (ball (upCenter η ρ) (upRadius η ρ))) :
    ((upperRoots (Rt P A τ c)).map φ).sum
      = (2 * π * I)⁻¹ * ∮ z in C(upCenter η ρ, upRadius η ρ),
          φ z * ((penPoly P A τ c).derivative.eval z / (penPoly P A τ c).eval z) := by
  rw [← roots_penPoly_gen hP A hτ c]
  refine OQP27.StripL3b.upper_sum_poly _ (penPoly_ne_zero_gen hP A hτ c) ?_ hη ?_ hφ
  · rw [roots_penPoly_gen hP A hτ c]; exact Rt_im_ne_zero_gen hP hA hL hU hτ hc
  · rw [roots_penPoly_gen hP A hτ c]; exact hup

/-- If the lower roots lie in `{Im ≤ -η, |y| ≤ ρ}`, their `φ`-sum is a circle integral. -/
theorem lower_sum_eq_circleIntegral_gen {τ : ℝ} (hτ : τ ∉ spec hP) {c : ℂ} (hc : 0 < c.im)
    {η ρ : ℝ} (hη : 0 < η) (hlo : ∀ y ∈ Rt P A τ c, y.im < 0 → y.im ≤ -η ∧ ‖y‖ ≤ ρ) {φ : ℂ → ℂ}
    (hφ : DiffContOnCl ℂ φ (ball (loCenter η ρ) (upRadius η ρ))) :
    ((lowerRoots (Rt P A τ c)).map φ).sum
      = (2 * π * I)⁻¹ * ∮ z in C(loCenter η ρ, upRadius η ρ),
          φ z * ((penPoly P A τ c).derivative.eval z / (penPoly P A τ c).eval z) := by
  rw [← roots_penPoly_gen hP A hτ c]
  refine OQP27.StripL3b.lower_sum_poly _ (penPoly_ne_zero_gen hP A hτ c) ?_ hη ?_ hφ
  · rw [roots_penPoly_gen hP A hτ c]; exact Rt_im_ne_zero_gen hP hA hL hU hτ hc
  · rw [roots_penPoly_gen hP A hτ c]; exact hlo

omit hA hL hU in
lemma penPoly_ne_zero_on_sphere_gen {τ : ℝ} (hτ : τ ∉ spec hP) {c : ℂ} {z₀ : ℂ} {R : ℝ}
    (hroot : ∀ y ∈ Rt P A τ c, dist y z₀ ≠ R) :
    ∀ z ∈ sphere z₀ R, (penPoly P A τ c).eval z ≠ 0 := by
  intro z hz h0z
  have hz' : z ∈ Rt P A τ c := by
    rw [← roots_penPoly_gen hP A hτ c]
    exact (mem_roots (penPoly_ne_zero_gen hP A hτ c)).mpr h0z
  exact hroot z hz' (mem_sphere.mp hz)

theorem upper_local_gen {τ₀ : ℝ} (hτ₀ : τ₀ ∉ spec hP) {c₀ : ℂ} (hc₀ : 0 < c₀.im) :
    LocalData (Sup P A) (Lup P A) τ₀ c₀ := by
  obtain ⟨δ, r, η, ρ, hδ, hr, hη, hτbox, hcim, hroots⟩ := local_box_gen hP hA hL hU hτ₀ hc₀
  have hR : 0 < upRadius η ρ := OQP27.StripL3b.upRadius_pos hη
  have hup : ∀ q ∈ Icc (τ₀ - δ) (τ₀ + δ) ×ˢ closedBall c₀ r, ∀ y ∈ Rt P A q.1 q.2,
      0 < y.im → η ≤ y.im ∧ ‖y‖ ≤ ρ :=
    fun q hq y hy => (hroots q.1 hq.1 q.2 hq.2 y hy).1
  have hdist : ∀ q ∈ Icc (τ₀ - δ) (τ₀ + δ) ×ˢ closedBall c₀ r, ∀ y ∈ Rt P A q.1 q.2,
      dist y (upCenter η ρ) ≠ upRadius η ρ := by
    intro q hq y hy heq
    have him := OQP27.StripL3b.im_ge_of_dist_upCenter_le (ρ := ρ) hη heq.le
    obtain ⟨h1', h2'⟩ := hup q hq y hy (by linarith)
    have := OQP27.StripL3b.dist_upCenter_lt hη h1' h2'
    rw [heq] at this
    exact lt_irrefl _ this
  refine ⟨δ, r, hδ, hr, ?_⟩
  refine OQP27.StripL3b.local_reg_generic P A hδ hr hR (Sup P A) (Lup P A)
    (fun q hq => penPoly_ne_zero_on_sphere_gen hP (hτbox q.1 hq.1) (hdist q hq))
    (fun z hz => Or.inr (by
      have := OQP27.StripL3b.im_ge_of_dist_upCenter_le (ρ := ρ) hη (mem_sphere.mp hz).le
      linarith))
    (fun q hq => ?_) (fun q hq => ?_)
  · have := upper_sum_eq_circleIntegral_gen hP hA hL hU (hτbox q.1 hq.1)
      (lt_of_lt_of_le hη (hcim q.2 hq.2)) hη (hup q hq) (φ := fun z => z)
      differentiable_id.diffContOnCl
    simpa [Sup, OQP27.StripL3b.intS] using this
  · exact upper_sum_eq_circleIntegral_gen hP hA hL hU (hτbox q.1 hq.1)
      (lt_of_lt_of_le hη (hcim q.2 hq.2)) hη (hup q hq) (OQP27.StripL3b.diffContOnCl_log_upper hη)

theorem lower_local_gen {τ₀ : ℝ} (hτ₀ : τ₀ ∉ spec hP) {c₀ : ℂ} (hc₀ : 0 < c₀.im) :
    LocalData (Slo P A) (Llo P A) τ₀ c₀ := by
  obtain ⟨δ, r, η, ρ, hδ, hr, hη, hτbox, hcim, hroots⟩ := local_box_gen hP hA hL hU hτ₀ hc₀
  have hR : 0 < upRadius η ρ := OQP27.StripL3b.upRadius_pos hη
  have hlo : ∀ q ∈ Icc (τ₀ - δ) (τ₀ + δ) ×ˢ closedBall c₀ r, ∀ y ∈ Rt P A q.1 q.2,
      y.im < 0 → y.im ≤ -η ∧ ‖y‖ ≤ ρ :=
    fun q hq y hy => (hroots q.1 hq.1 q.2 hq.2 y hy).2
  have hdist : ∀ q ∈ Icc (τ₀ - δ) (τ₀ + δ) ×ˢ closedBall c₀ r, ∀ y ∈ Rt P A q.1 q.2,
      dist y (loCenter η ρ) ≠ upRadius η ρ := by
    intro q hq y hy heq
    have him := OQP27.StripL3b.im_le_of_dist_loCenter_le (ρ := ρ) hη heq.le
    obtain ⟨h1', h2'⟩ := hlo q hq y hy (by linarith)
    have := OQP27.StripL3b.dist_loCenter_lt hη h1' h2'
    rw [heq] at this
    exact lt_irrefl _ this
  refine ⟨δ, r, hδ, hr, ?_⟩
  refine OQP27.StripL3b.local_reg_generic P A hδ hr hR (Slo P A) (Llo P A)
    (fun q hq => penPoly_ne_zero_on_sphere_gen hP (hτbox q.1 hq.1) (hdist q hq))
    (fun z hz => Or.inr (by
      have := OQP27.StripL3b.im_le_of_dist_loCenter_le (ρ := ρ) hη (mem_sphere.mp hz).le
      linarith))
    (fun q hq => ?_) (fun q hq => ?_)
  · have := lower_sum_eq_circleIntegral_gen hP hA hL hU (hτbox q.1 hq.1)
      (lt_of_lt_of_le hη (hcim q.2 hq.2)) hη (hlo q hq) (φ := fun z => z)
      differentiable_id.diffContOnCl
    simpa [Slo, OQP27.StripL3b.intS] using this
  · exact lower_sum_eq_circleIntegral_gen hP hA hL hU (hτbox q.1 hq.1)
      (lt_of_lt_of_le hη (hcim q.2 hq.2)) hη (hlo q hq) (OQP27.StripL3b.diffContOnCl_log_lower hη)

end Local

/-! ### Global statements on `(ℝ ∖ spec P) × ℂ₊` -/

/-- The open domain `{(τ, c) : τ ∉ spec P, Im c > 0}`. -/
def domRIG {P : Matrix (Fin M) (Fin M) ℂ} (hP : P.IsHermitian) : Set (ℝ × ℂ) :=
  {q | q.1 ∉ spec hP ∧ 0 < q.2.im}

lemma isOpen_domRIG {P : Matrix (Fin M) (Fin M) ℂ} (hP : P.IsHermitian) : IsOpen (domRIG hP) := by
  have h1 : IsOpen {q : ℝ × ℂ | q.1 ∉ spec hP} :=
    (Finset.isClosed (spec hP)).isOpen_compl.preimage continuous_fst
  have h2 : IsOpen {q : ℝ × ℂ | 0 < q.2.im} :=
    isOpen_lt continuous_const (Complex.continuous_im.comp continuous_snd)
  exact h1.inter h2

/-- From local data everywhere on a set `D` to global statements on `D`. -/
theorem global_of_local_on {D : Set (ℝ × ℂ)} {Ssum Lsum : ℝ → ℂ → ℂ}
    (hloc : ∀ q ∈ D, LocalData Ssum Lsum q.1 q.2) :
    (∀ q ∈ D, HasDerivAt (fun c => Ssum q.1 c) (deriv (fun c => Ssum q.1 c) q.2) q.2) ∧
    (∀ q ∈ D, HasDerivAt (fun τ => Lsum τ q.2) (deriv (fun c => Ssum q.1 c) q.2) q.1) ∧
    ContinuousOn (fun q : ℝ × ℂ => deriv (fun c => Ssum q.1 c) q.2) D ∧
    ContinuousOn (fun q : ℝ × ℂ => Ssum q.1 q.2) D ∧
    ContinuousOn (fun q : ℝ × ℂ => Lsum q.1 q.2) D := by
  have hbox_nhds : ∀ (q : ℝ × ℂ) (δ r : ℝ), 0 < δ → 0 < r →
      Icc (q.1 - δ) (q.1 + δ) ×ˢ closedBall q.2 r ∈ 𝓝 q := by
    intro q δ r hδ hr
    rw [nhds_prod_eq]
    exact Filter.prod_mem_prod (Icc_mem_nhds (by linarith) (by linarith))
      (closedBall_mem_nhds q.2 hr)
  have hderiv_eq : ∀ q ∈ D, ∃ δ r : ℝ, 0 < δ ∧ 0 < r ∧ ∃ Sd : ℝ → ℂ → ℂ,
      ContinuousOn (fun q' : ℝ × ℂ => Sd q'.1 q'.2) (Icc (q.1 - δ) (q.1 + δ) ×ˢ closedBall q.2 r) ∧
      (∀ q' ∈ Ioo (q.1 - δ) (q.1 + δ) ×ˢ ball q.2 r,
        deriv (fun c => Ssum q'.1 c) q'.2 = Sd q'.1 q'.2) ∧
      (∀ τ ∈ Ioo (q.1 - δ) (q.1 + δ), ∀ c ∈ closedBall q.2 r,
        HasDerivAt (fun τ => Lsum τ c) (Sd τ c) τ) ∧
      HasDerivAt (fun c => Ssum q.1 c) (Sd q.1 q.2) q.2 := by
    intro q hq
    obtain ⟨δ, r, hδ, hr, Sd, hSd, -, -, hc, ht⟩ := hloc q hq
    refine ⟨δ, r, hδ, hr, Sd, hSd,
      fun q' hq' => (hc q'.1 (Ioo_subset_Icc_self hq'.1) q'.2 hq'.2).deriv,
      ht, hc q.1 ⟨by linarith, by linarith⟩ q.2 (mem_ball_self hr)⟩
  refine ⟨fun q hq => ?_, fun q hq => ?_, fun q hq => ?_, fun q hq => ?_, fun q hq => ?_⟩
  · obtain ⟨δ, r, hδ, hr, Sd, -, -, -, hc⟩ := hderiv_eq q hq
    rw [hc.deriv]; exact hc
  · obtain ⟨δ, r, hδ, hr, Sd, -, -, ht, hc⟩ := hderiv_eq q hq
    rw [hc.deriv]
    exact ht q.1 ⟨by linarith, by linarith⟩ q.2 (mem_closedBall_self hr.le)
  · obtain ⟨δ, r, hδ, hr, Sd, hSd, heq, -, -⟩ := hderiv_eq q hq
    have hopen : Ioo (q.1 - δ) (q.1 + δ) ×ˢ ball q.2 r ∈ 𝓝 q := by
      rw [nhds_prod_eq]
      exact Filter.prod_mem_prod (Ioo_mem_nhds (by linarith) (by linarith)) (ball_mem_nhds q.2 hr)
    have hcont : ContinuousAt (fun q' : ℝ × ℂ => Sd q'.1 q'.2) q :=
      hSd.continuousAt (hbox_nhds q δ r hδ hr)
    refine (hcont.congr ?_).continuousWithinAt
    filter_upwards [hopen] with q' hq'
    exact (heq q' hq').symm
  · obtain ⟨δ, r, hδ, hr, Sd, -, hS, -, -, -⟩ := hloc q hq
    exact (hS.continuousAt (hbox_nhds q δ r hδ hr)).continuousWithinAt
  · obtain ⟨δ, r, hδ, hr, Sd, -, -, hL, -, -⟩ := hloc q hq
    exact (hL.continuousAt (hbox_nhds q δ r hδ hr)).continuousWithinAt

section Global

variable {P A : Matrix (Fin M) (Fin M) ℂ} (hP : P.IsHermitian) (hA : A.IsHermitian)
  {L U : ℝ} (hL : ∀ i, L ≤ hP.eigenvalues i) (hU : ∀ i, hP.eigenvalues i ≤ U)
include hP hA hL hU

/-- **Regularity of `S_+`, `Λ_+` off the spectrum and the Burgers identity** `∂_τ Λ_+ = ∂_c S_+`. -/
theorem upper_global_gen :
    (∀ q ∈ domRIG hP, HasDerivAt (fun c => Sup P A q.1 c) (deriv (fun c => Sup P A q.1 c) q.2) q.2) ∧
    (∀ q ∈ domRIG hP, HasDerivAt (fun τ => Lup P A τ q.2) (deriv (fun c => Sup P A q.1 c) q.2) q.1) ∧
    ContinuousOn (fun q : ℝ × ℂ => deriv (fun c => Sup P A q.1 c) q.2) (domRIG hP) ∧
    ContinuousOn (fun q : ℝ × ℂ => Sup P A q.1 q.2) (domRIG hP) ∧
    ContinuousOn (fun q : ℝ × ℂ => Lup P A q.1 q.2) (domRIG hP) :=
  global_of_local_on fun _ hq => upper_local_gen hP hA hL hU hq.1 hq.2

/-- **Regularity of `S_-`, `Λ_-` off the spectrum and the Burgers identity** `∂_τ Λ_- = ∂_c S_-`. -/
theorem lower_global_gen :
    (∀ q ∈ domRIG hP, HasDerivAt (fun c => Slo P A q.1 c) (deriv (fun c => Slo P A q.1 c) q.2) q.2) ∧
    (∀ q ∈ domRIG hP, HasDerivAt (fun τ => Llo P A τ q.2) (deriv (fun c => Slo P A q.1 c) q.2) q.1) ∧
    ContinuousOn (fun q : ℝ × ℂ => deriv (fun c => Slo P A q.1 c) q.2) (domRIG hP) ∧
    ContinuousOn (fun q : ℝ × ℂ => Slo P A q.1 q.2) (domRIG hP) ∧
    ContinuousOn (fun q : ℝ × ℂ => Llo P A q.1 q.2) (domRIG hP) :=
  global_of_local_on fun _ hq => lower_local_gen hP hA hL hU hq.1 hq.2

end Global

end HarmonicMajorization
