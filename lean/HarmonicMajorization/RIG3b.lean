import HarmonicMajorization.RIG3a

/-!
# Cancellation at a point of the spectrum (proof of the multi-line RI, IV)

Authors: Ansh Mishra, Aryan Senthilkumar.  License: MIT.

`P` Hermitian, `A` Hermitian, `A_d = pinchH hP A`, `G(τ, c) = Λ_+(A)(τ, c) - Λ_+(A_d)(τ, c)`.
Main result:
* `Gup_cancel`: for every `p ∈ spec P`, `G(p - δ, c) - G(p + δ, c) → 0` as `δ → 0⁺`, uniformly on
  compact subsets of `ℂ₊` (the cancellation of [27, Remark RIgeneralB]; at `p = max spec` it is the
  end `G(p - δ) → 0`).

Route.  Near `τ = p` every root is bounded (`|y| < Y`) or large (`dichotomy`).  The bounded roots in
`ℂ₊` are counted by a fixed circle `C_y`, and their log-sum is a circle integral that is continuous in
`τ` across `τ = p` (the pencil polynomial is continuous and does not vanish on `C_y`, also at `τ = p`).
The large roots lie in `ℂ₊` for `τ < p` and in `ℂ₋` for `τ > p`; for `τ < p` they are
`w / (p - τ)` with `w` the roots of the rescaled pencil `WmatP` inside a fixed circle `C_w`, whose
characteristic polynomials for `A` and `A_d` agree at `τ = p` (`uniform_end_limit`).

No hypotheses.
-/

set_option autoImplicit false

namespace HarmonicMajorization

open Matrix Polynomial Complex Metric Filter Topology Set Real
open OQP27.StripL3b (pencilRoots imAbsSum frob Rt Sup Slo Lup Llo penPoly upperRoots lowerRoots
  upCenter upRadius loCenter)

variable {M : ℕ}

/-- `∮_{C(z₀,R)} φ(z) f'(z)/f(z) dz` for the pencil polynomial `f = penPoly P B τ c`. -/
noncomputable def penInt (P B : Matrix (Fin M) (Fin M) ℂ) (φ : ℂ → ℂ) (z₀ : ℂ) (R : ℝ)
    (q : ℝ × ℂ) : ℂ :=
  ∮ z in C(z₀, R), φ z * ((penPoly P B q.1 q.2).derivative.eval z / (penPoly P B q.1 q.2).eval z)

/-- `∮_{C(z₀,R)} φ(z) χ'(z)/χ(z) dz` for the characteristic polynomial `χ` of `N`. -/
noncomputable def chiInt (N : Matrix (Fin M) (Fin M) ℂ) (φ : ℂ → ℂ) (z₀ : ℂ) (R : ℝ) : ℂ :=
  ∮ z in C(z₀, R), φ z * ((Matrix.charpoly N).derivative.eval z / (Matrix.charpoly N).eval z)

/-- The number of roots `y` with `(p - τ) y` inside `C(z₀, R)`. -/
noncomputable def cntW (P B : Matrix (Fin M) (Fin M) ℂ) (p τ : ℝ) (c z₀ : ℂ) (R : ℝ) : ℕ :=
  ((Rt P B τ c).filter fun y => dist (((p - τ : ℝ) : ℂ) * y) z₀ < R).card

lemma two_pi_I_ne_zero : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]

lemma norm_two_pi_I_inv : ‖(2 * π * I : ℂ)⁻¹‖ = (2 * π)⁻¹ := by
  rw [norm_inv]
  congr 1
  simp [abs_of_pos Real.pi_pos]

section Contour

variable {P : Matrix (Fin M) (Fin M) ℂ} (hP : P.IsHermitian)
include hP

/-- `Λ_+` as a contour integral when the upper roots are exactly the roots inside `C(z₀, R)`. -/
lemma Lup_eq_penInt {B : Matrix (Fin M) (Fin M) ℂ} {τ : ℝ} (hτ : τ ∉ spec hP) {c : ℂ}
    {z₀ : ℂ} {R : ℝ} (hR : 0 < R) (hlog : DiffContOnCl ℂ Complex.log (ball z₀ R))
    (hiff : ∀ y ∈ Rt P B τ c, (0 < y.im ↔ dist y z₀ < R))
    (hne : ∀ y ∈ Rt P B τ c, dist y z₀ ≠ R) :
    Lup P B τ c = (2 * π * I)⁻¹ * penInt P B Complex.log z₀ R (τ, c) := by
  have hp := penPoly_ne_zero_gen hP B hτ c
  have hRt := roots_penPoly_gen hP B hτ c
  unfold Lup upperRoots
  rw [Multiset.filter_congr hiff, ← hRt]
  rw [← hRt] at hne
  exact sum_filter_eq_circleIntegral _ hp hR hne hlog

/-- `Λ_+` split into the roots inside `C(z₁, R₁)` and the roots `y` with `(p - τ) y` inside
`C(z₂, R₂)`; the second part is a contour integral for the rescaled pencil. -/
lemma Lup_eq_penInt_add {B : Matrix (Fin M) (Fin M) ℂ} {p τ : ℝ} (hτ : τ ∉ spec hP)
    (hpτ : τ < p) {c : ℂ} {z₁ z₂ : ℂ} {R₁ R₂ : ℝ} (hR₁ : 0 < R₁) (hR₂ : 0 < R₂)
    (hlog₁ : DiffContOnCl ℂ Complex.log (ball z₁ R₁)) (hlog₂ : DiffContOnCl ℂ Complex.log (ball z₂ R₂))
    (hiff : ∀ y ∈ Rt P B τ c,
      (0 < y.im ↔ (dist y z₁ < R₁ ∨ dist (((p - τ : ℝ) : ℂ) * y) z₂ < R₂)))
    (hdisj : ∀ y ∈ Rt P B τ c, ¬ (dist y z₁ < R₁ ∧ dist (((p - τ : ℝ) : ℂ) * y) z₂ < R₂))
    (hne₁ : ∀ y ∈ Rt P B τ c, dist y z₁ ≠ R₁)
    (hne₂ : ∀ y ∈ Rt P B τ c, dist (((p - τ : ℝ) : ℂ) * y) z₂ ≠ R₂)
    (hy0 : ∀ y ∈ Rt P B τ c, y ≠ 0) :
    Lup P B τ c = (2 * π * I)⁻¹ * penInt P B Complex.log z₁ R₁ (τ, c)
        + ((2 * π * I)⁻¹ * chiInt (WmatP hP p B (τ, c)) Complex.log z₂ R₂
          - (cntW P B p τ c z₂ R₂ : ℂ) * (Real.log (p - τ) : ℂ)) ∧
    (cntW P B p τ c z₂ R₂ : ℂ)
      = (2 * π * I)⁻¹ * chiInt (WmatP hP p B (τ, c)) (fun _ => 1) z₂ R₂ := by
  have hp := penPoly_ne_zero_gen hP B hτ c
  have hRt := roots_penPoly_gen hP B hτ c
  have hpτ' : 0 < p - τ := by linarith
  have hsplit : upperRoots (Rt P B τ c) = (Rt P B τ c).filter (fun a => dist a z₁ < R₁)
      + (Rt P B τ c).filter (fun y => dist (((p - τ : ℝ) : ℂ) * y) z₂ < R₂) :=
    filter_eq_add_filter hiff hdisj
  have hroots2 := roots_WmatP hP p B hτ hpτ.ne' c
  have hTmap : ((Rt P B τ c).filter (fun y => dist (((p - τ : ℝ) : ℂ) * y) z₂ < R₂)).map
      (fun y => ((p - τ : ℝ) : ℂ) * y)
      = (Matrix.charpoly (WmatP hP p B (τ, c))).roots.filter (fun a => dist a z₂ < R₂) := by
    rw [hroots2, Multiset.filter_map]
    rfl
  have hne₂' : ∀ a ∈ (Matrix.charpoly (WmatP hP p B (τ, c))).roots, dist a z₂ ≠ R₂ := by
    intro a ha
    rw [hroots2] at ha
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp ha
    exact hne₂ y hy
  have hχ : Matrix.charpoly (WmatP hP p B (τ, c)) ≠ 0 := (Matrix.charpoly_monic _).ne_zero
  have hlogsum := sum_filter_eq_circleIntegral _ hχ hR₂ hne₂' hlog₂
  have honesum := sum_filter_eq_circleIntegral _ hχ hR₂ hne₂' (φ := fun _ => (1 : ℂ))
    diffContOnCl_const
  rw [← hTmap] at hlogsum honesum
  have hT0 : ∀ y ∈ (Rt P B τ c).filter (fun y => dist (((p - τ : ℝ) : ℂ) * y) z₂ < R₂), y ≠ 0 :=
    fun y hy => hy0 y (Multiset.mem_of_mem_filter hy)
  have hmap := OQP27.StripL3b.sum_log_map_mul _ hpτ' hT0
  have hcard : ((((Rt P B τ c).filter (fun y => dist (((p - τ : ℝ) : ℂ) * y) z₂ < R₂)).map
      (fun y => ((p - τ : ℝ) : ℂ) * y)).map fun _ => (1 : ℂ)).sum
      = (cntW P B p τ c z₂ R₂ : ℂ) := by
    unfold cntW
    simp only [Multiset.map_map, Function.comp_def, Multiset.map_const', Multiset.sum_replicate,
      nsmul_eq_mul, mul_one]
  have h1 : (((Rt P B τ c).filter (fun a => dist a z₁ < R₁)).map Complex.log).sum
      = (2 * π * I)⁻¹ * penInt P B Complex.log z₁ R₁ (τ, c) := by
    rw [← hRt]
    rw [← hRt] at hne₁
    exact sum_filter_eq_circleIntegral _ hp hR₁ hne₁ hlog₁
  refine ⟨?_, ?_⟩
  · unfold Lup cntW
    rw [hsplit, Multiset.map_add, Multiset.sum_add, h1]
    congr 1
    unfold chiInt
    rw [← hlogsum, hmap]
    ring
  · rw [← hcard]
    unfold chiInt
    exact honesum

end Contour

set_option maxHeartbeats 1000000 in
/-- **Cancellation at a point of the spectrum**: for `p ∈ spec P`,
`(Λ_+(A) - Λ_+(A_d))(p - δ, c) - (Λ_+(A) - Λ_+(A_d))(p + δ, c) → 0` as `δ → 0⁺`, uniformly for `c`
in a compact subset of `ℂ₊`. -/
theorem Gup_cancel {P A : Matrix (Fin M) (Fin M) ℂ} (hP : P.IsHermitian) (hA : A.IsHermitian)
    {p : ℝ} (hp : p ∈ spec hP) {K : Set ℂ} (hK : IsCompact K) (hKpos : ∀ c ∈ K, 0 < c.im)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ₀ > 0, ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∀ c ∈ K,
      ‖(Lup P A (p - δ) c - Lup P (pinchH hP A) (p - δ) c)
        - (Lup P A (p + δ) c - Lup P (pinchH hP A) (p + δ) c)‖ < ε := by
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · exact ⟨1, one_pos, fun δ _ _ c hc => by rw [hKe] at hc; exact absurd hc (Set.notMem_empty c)⟩
  obtain ⟨c₁, hc₁K, hc₁min⟩ := hK.exists_isMinOn hKne Complex.continuous_im.continuousOn
  set η := c₁.im with hη_def
  have hη : 0 < η := hKpos c₁ hc₁K
  have hηle : ∀ c ∈ K, η ≤ c.im := fun c hc => hc₁min hc
  set A₀ := pinchH hP A with hA₀_def
  have hA₀ : A₀.IsHermitian := isHermitian_pinchH hP hA
  -- the Frobenius bound
  have hcf : ContinuousOn (fun c : ℂ => frob (A + c • 1) + frob (A₀ + c • 1)) K := by
    apply Continuous.continuousOn; unfold frob; fun_prop
  obtain ⟨Kf, hKf⟩ := hK.exists_bound_of_continuousOn hcf
  set F := max Kf 0 + 1 with hF_def
  have hF : 0 < F := by positivity
  have hfrob : ∀ B : Matrix (Fin M) (Fin M) ℂ, (B = A ∨ B = A₀) → ∀ c ∈ K,
      frob (B + c • 1) ≤ F := by
    intro B hB c hc
    have h1 := hKf c hc
    rw [Real.norm_eq_abs] at h1
    have hA1 := OQP27.StripL3b.frob_nonneg (A + c • 1)
    have hA2 := OQP27.StripL3b.frob_nonneg (A₀ + c • 1)
    rw [abs_of_nonneg (by linarith)] at h1
    have hm := le_max_left Kf 0
    rcases hB with hB | hB <;> rw [hB] <;> linarith
  -- separation and spectral bounds
  obtain ⟨d₀, hd₀, hd₀1, hsep⟩ := exists_sep hP p
  set sl := ∑ i, |hP.eigenvalues i| with hsl_def
  have hsl : ∀ i, |hP.eigenvalues i| ≤ sl := fun i =>
    Finset.single_le_sum (f := fun j => |hP.eigenvalues j|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ i)
  have hsl0 : 0 ≤ sl := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hL : ∀ i, -sl ≤ hP.eigenvalues i := fun i => by
    linarith [neg_abs_le (hP.eigenvalues i), hsl i]
  have hU : ∀ i, hP.eigenvalues i ≤ sl := fun i => by
    linarith [le_abs_self (hP.eigenvalues i), hsl i]
  set D := 2 * sl + |p| + 1 with hD_def
  have hD0 : 0 ≤ D := by positivity
  set W := sl + |p| + 1 with hW_def
  have hW : 0 < W := by positivity
  set η' := η / W with hη'_def
  have hη' : 0 < η' := div_pos hη hW
  set Y := √(32 * F) / d₀ + 32 * F * D / (η * d₀ ^ 2) + 1 with hY_def
  have hY : 0 < Y := by positivity
  have hlarge : ∀ y : ℂ, Y ≤ ‖y‖ → 32 * F ≤ ‖y‖ ^ 2 * d₀ ^ 2 ∧ 32 * F * D ≤ η * d₀ ^ 2 * ‖y‖ := by
    intro y hy
    have h1 : √(32 * F) / d₀ ≤ ‖y‖ := by
      have : 0 ≤ 32 * F * D / (η * d₀ ^ 2) := by positivity
      linarith
    have h2 : 32 * F * D / (η * d₀ ^ 2) ≤ ‖y‖ := by
      have : 0 ≤ √(32 * F) / d₀ := by positivity
      linarith
    constructor
    · rw [div_le_iff₀ hd₀] at h1
      have h3 : √(32 * F) ^ 2 ≤ (‖y‖ * d₀) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
      rw [Real.sq_sqrt (by positivity)] at h3
      linarith [h3]
    · rw [div_le_iff₀ (by positivity)] at h2
      linarith
  set zy := upCenter η' Y with hzy
  set Ry := upRadius η' Y with hRy
  have hRy0 : 0 < Ry := OQP27.StripL3b.upRadius_pos hη'
  set Ey := ‖zy‖ + Ry with hEy
  have hEy0 : 0 < Ey := by positivity
  set ρw := √(2 * F) with hρw
  have hη2 : 0 < η / 2 := by positivity
  set zw := upCenter (η / 2) ρw with hzw
  set Rw := upRadius (η / 2) ρw with hRw
  have hRw0 : 0 < Rw := OQP27.StripL3b.upRadius_pos hη2
  set δ₁ := min (d₀ / 2) (min (η / (8 * Y)) (η / (2 * (Ey + 1)))) with hδ₁_def
  have hδ₁ : 0 < δ₁ := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hδ₁d : δ₁ ≤ d₀ / 2 := min_le_left _ _
  have hδ₁Y : δ₁ * Y ≤ η / 8 := by
    have h : δ₁ ≤ η / (8 * Y) := (min_le_right _ _).trans (min_le_left _ _)
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  have hδ₁E : δ₁ * (Ey + 1) ≤ η / 2 := by
    have h : δ₁ ≤ η / (2 * (Ey + 1)) := (min_le_right _ _).trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  have hδ₁1 : δ₁ ≤ 1 / 2 := by linarith
  -- bounds on the `τ`-range
  have hτrange : ∀ τ ∈ Icc (p - δ₁) (p + δ₁), |τ - p| ≤ δ₁ ∧ (∀ i, |hP.eigenvalues i - τ| ≤ D)
      ∧ sl - τ ≤ W := by
    intro τ hτ
    have h1 : |τ - p| ≤ δ₁ := abs_le.mpr ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    have h2 : |τ| ≤ |p| + 1 := by
      have := abs_sub_abs_le_abs_sub τ p
      linarith
    refine ⟨h1, fun i => ?_, ?_⟩
    · have := abs_sub (hP.eigenvalues i) τ
      linarith [hsl i]
    · linarith [neg_abs_le τ]
  -- classification of the roots near `τ = p`
  have hroot : ∀ B : Matrix (Fin M) (Fin M) ℂ, (B = A ∨ B = A₀) → B.IsHermitian →
      ∀ τ ∈ Icc (p - δ₁) (p + δ₁), ∀ c ∈ K, ∀ y ∈ (penPoly P B τ c).roots,
        y.im ≠ 0 ∧ (0 < y.im → η' ≤ y.im) ∧
        (¬ ‖y‖ < Y → τ ≠ p ∧ c.im / 2 ≤ (p - τ) * y.im ∧ ((p - τ) * ‖y‖) ^ 2 ≤ 2 * F ∧
          Ey + 1 ≤ ‖y‖) := by
    intro B hB hBh τ hτ c hc y hy
    have hcpos := hKpos c hc
    obtain ⟨hτp, hDτ, hWτ⟩ := hτrange τ hτ
    obtain ⟨v, hv0, hv⟩ := exists_eigvec_of_root (penPoly_ne_zero_of_im_pos P hBh τ hcpos) hy
    obtain ⟨hyim, hup, -⟩ := im_bounds_of_eigvec hP hBh hL hU τ hcpos hv0 hv
    refine ⟨hyim, fun hpos => ?_, fun hbig => ?_⟩
    · have h1 := hup hpos
      have h2 : c.im ≤ W * y.im := h1.trans (mul_le_mul_of_nonneg_right hWτ hpos.le)
      rw [hη'_def, div_le_iff₀ hW]
      linarith [hηle c hc]
    · push Not at hbig
      obtain ⟨h1, h2⟩ := hlarge y hbig
      obtain ⟨hw1, hw2⟩ := dichotomy hP hBh hd₀ hsep (hτp.trans hδ₁d) hDτ hD0 hF hη (hηle c hc)
        (hfrob B hB c hc) hv0 hv h1 h2
      have hci := hηle c hc
      have hτne : τ ≠ p := by
        intro h
        rw [h, sub_self, zero_mul] at hw1
        linarith
      refine ⟨hτne, hw1, hw2, ?_⟩
      have h3 : (p - τ) * y.im ≤ |p - τ| * ‖y‖ := by
        calc (p - τ) * y.im ≤ |(p - τ) * y.im| := le_abs_self _
          _ = |p - τ| * |y.im| := abs_mul _ _
          _ ≤ |p - τ| * ‖y‖ :=
            mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm y) (abs_nonneg _)
      have h4 : |p - τ| ≤ δ₁ := by rw [abs_sub_comm]; exact hτp
      have h5 : η / 2 ≤ δ₁ * ‖y‖ := by
        have := mul_le_mul_of_nonneg_right h4 (norm_nonneg y)
        linarith
      by_contra hcon
      push Not at hcon
      have h6 : δ₁ * ‖y‖ < δ₁ * (Ey + 1) := mul_lt_mul_of_pos_left hcon hδ₁
      linarith
  -- the circle `C_y`
  have hCy : ∀ B : Matrix (Fin M) (Fin M) ℂ, (B = A ∨ B = A₀) → B.IsHermitian →
      ∀ τ ∈ Icc (p - δ₁) (p + δ₁), ∀ c ∈ K, ∀ y ∈ (penPoly P B τ c).roots,
        (dist y zy < Ry ↔ (0 < y.im ∧ ‖y‖ < Y)) ∧ dist y zy ≠ Ry := by
    intro B hB hBh τ hτ c hc y hy
    obtain ⟨hyim, hup, hbig⟩ := hroot B hB hBh τ hτ c hc y hy
    by_cases hyY : ‖y‖ < Y
    · rcases lt_or_gt_of_ne hyim with hneg | hpos
      · have hgt : Ry < dist y zy := by
          by_contra h
          push Not at h
          have := OQP27.StripL3b.im_ge_of_dist_upCenter_le hη' h
          linarith
        exact ⟨⟨fun h => absurd h (not_lt.mpr hgt.le), fun h => absurd h.1 (not_lt.mpr hneg.le)⟩,
          hgt.ne'⟩
      · have hin : dist y zy < Ry := OQP27.StripL3b.dist_upCenter_lt hη' (hup hpos) hyY.le
        exact ⟨⟨fun _ => ⟨hpos, hyY⟩, fun _ => hin⟩, hin.ne⟩
    · obtain ⟨-, -, -, hE⟩ := hbig hyY
      have hgt : Ry < dist y zy := by
        have := norm_sub_norm_le y zy
        rw [dist_eq_norm]
        linarith
      exact ⟨⟨fun h => absurd h (not_lt.mpr hgt.le), fun h => absurd h.2 hyY⟩, hgt.ne'⟩
  -- the circle `C_w`, for `τ < p`
  have hCw : ∀ B : Matrix (Fin M) (Fin M) ℂ, (B = A ∨ B = A₀) → B.IsHermitian →
      ∀ τ, p - δ₁ ≤ τ → τ < p → ∀ c ∈ K, ∀ y ∈ (penPoly P B τ c).roots,
        (dist (((p - τ : ℝ) : ℂ) * y) zw < Rw ↔ ¬ ‖y‖ < Y) ∧
          dist (((p - τ : ℝ) : ℂ) * y) zw ≠ Rw := by
    intro B hB hBh τ hτ1 hτ2 c hc y hy
    have hτ : τ ∈ Icc (p - δ₁) (p + δ₁) := ⟨hτ1, by linarith⟩
    obtain ⟨hyim, hup, hbig⟩ := hroot B hB hBh τ hτ c hc y hy
    have hpτ : 0 < p - τ := by linarith
    have hwim : ((((p - τ : ℝ)) : ℂ) * y).im = (p - τ) * y.im := by simp [Complex.mul_im]
    have hwn : ‖(((p - τ : ℝ)) : ℂ) * y‖ = (p - τ) * ‖y‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpτ]
    by_cases hyY : ‖y‖ < Y
    · have hsmall : ‖(((p - τ : ℝ)) : ℂ) * y‖ ≤ η / 8 := by
        rw [hwn]
        have h1 : (p - τ) * ‖y‖ ≤ δ₁ * Y :=
          mul_le_mul (by linarith) hyY.le (norm_nonneg y) hδ₁.le
        linarith
      have hgt : Rw < dist (((p - τ : ℝ) : ℂ) * y) zw := by
        by_contra h
        push Not at h
        have h1 := OQP27.StripL3b.im_ge_of_dist_upCenter_le hη2 h
        have h2 := (Complex.im_le_norm ((((p - τ : ℝ)) : ℂ) * y)).trans hsmall
        linarith
      exact ⟨⟨fun h => absurd h (not_lt.mpr hgt.le), fun h => absurd hyY h⟩, hgt.ne'⟩
    · obtain ⟨-, hw1, hw2, -⟩ := hbig hyY
      have hin : dist (((p - τ : ℝ) : ℂ) * y) zw < Rw := by
        refine OQP27.StripL3b.dist_upCenter_lt hη2 ?_ ?_
        · rw [hwim]; linarith [hηle c hc]
        · rw [hwn, hρw]
          exact Real.le_sqrt_of_sq_le hw2
      exact ⟨⟨fun _ => hyY, fun _ => hin⟩, hin.ne⟩
  -- the circle `C_w` at `τ = p`
  have hCw0 : ∀ B : Matrix (Fin M) (Fin M) ℂ, (B = A ∨ B = A₀) → B.IsHermitian →
      ∀ c ∈ K, ∀ w ∈ (Matrix.charpoly (WmatP hP p B (p, c))).roots, dist w zw ≠ Rw := by
    intro B hB hBh c hc w hw
    rcases roots_WmatP_self hP p hBh c hw with h0 | ⟨h1, h2⟩
    · intro h
      have := OQP27.StripL3b.im_ge_of_dist_upCenter_le hη2 h.le
      rw [h0, Complex.zero_im] at this
      linarith
    · have hin : dist w zw < Rw := by
        refine OQP27.StripL3b.dist_upCenter_lt hη2 ?_ ?_
        · rw [h1]; linarith [hηle c hc]
        · rw [hρw]
          exact Real.le_sqrt_of_sq_le (by linarith [hfrob B hB c hc])
      exact hin.ne
  -- the parameter sets
  set Sy := Icc (p - δ₁) (p + δ₁) ×ˢ K with hSy
  have hSyc : IsCompact Sy := isCompact_Icc.prod hK
  set Sw := Icc (p - δ₁) p ×ˢ K with hSw
  have hSwc : IsCompact Sw := isCompact_Icc.prod hK
  -- non-vanishing on the circles
  have hneY : ∀ B : Matrix (Fin M) (Fin M) ℂ, (B = A ∨ B = A₀) → B.IsHermitian →
      ∀ q ∈ Sy, ∀ z ∈ sphere zy Ry, (penPoly P B q.1 q.2).eval z ≠ 0 := by
    intro B hB hBh q hq z hz h0
    have hpne := penPoly_ne_zero_of_im_pos P hBh q.1 (hKpos q.2 hq.2)
    have hzr : z ∈ (penPoly P B q.1 q.2).roots := (Polynomial.mem_roots hpne).mpr h0
    exact (hCy B hB hBh q.1 hq.1 q.2 hq.2 z hzr).2 (mem_sphere.mp hz)
  have hneW : ∀ B : Matrix (Fin M) (Fin M) ℂ, (B = A ∨ B = A₀) → B.IsHermitian →
      ∀ q ∈ Sw, ∀ w ∈ sphere zw Rw, (Matrix.charpoly (WmatP hP p B q)).eval w ≠ 0 := by
    intro B hB hBh q hq w hw h0
    have hwr : w ∈ (Matrix.charpoly (WmatP hP p B q)).roots :=
      (Polynomial.mem_roots (Matrix.charpoly_monic _).ne_zero).mpr h0
    obtain ⟨τ, c⟩ := q
    have hτ1 : p - δ₁ ≤ τ := hq.1.1
    have hτ2 : τ ≤ p := hq.1.2
    have hc : c ∈ K := hq.2
    rcases lt_or_eq_of_le hτ2 with hlt | heq
    · have hτs : τ ∉ spec hP := not_mem_spec_of_near hP hsep hlt.ne
        (by rw [abs_lt]; constructor <;> linarith)
      rw [roots_WmatP hP p B hτs hlt.ne' c] at hwr
      obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hwr
      rw [← roots_penPoly_gen hP B hτs c] at hy
      exact (hCw B hB hBh τ hτ1 hlt c hc y hy).2 (mem_sphere.mp hw)
    · rw [heq] at hwr
      exact hCw0 B hB hBh c hc w hwr (mem_sphere.mp hw)
  -- continuity of `log` on the circles
  have hlogY : ContinuousOn Complex.log (sphere zy Ry) := fun z hz =>
    (continuousAt_clog (Or.inr (by
      have := OQP27.StripL3b.im_ge_of_dist_upCenter_le hη' (mem_sphere.mp hz).le
      linarith))).continuousWithinAt
  have hlogW : ContinuousOn Complex.log (sphere zw Rw) := fun z hz =>
    (continuousAt_clog (Or.inr (by
      have := OQP27.StripL3b.im_ge_of_dist_upCenter_le hη2 (mem_sphere.mp hz).le
      linarith))).continuousWithinAt
  -- uniform continuity of the bounded parts
  have hunifY : ∀ B : Matrix (Fin M) (Fin M) ℂ, (B = A ∨ B = A₀) → B.IsHermitian →
      ∃ δf > 0, ∀ q ∈ Sy, ∀ q' ∈ Sy, dist q q' < δf →
        ‖penInt P B Complex.log zy Ry q - penInt P B Complex.log zy Ry q'‖ < π * ε / 2 := by
    intro B hB hBh
    have hG : ContinuousOn (fun x : (ℝ × ℂ) × ℂ => Complex.log x.2
        * ((penPoly P B x.1.1 x.1.2).derivative.eval x.2 / (penPoly P B x.1.1 x.1.2).eval x.2))
        (Sy ×ˢ sphere zy Ry) := by
      refine (hlogY.comp continuousOn_snd fun x hx => hx.2).mul ?_
      exact ((OQP27.StripL3b.continuous_eval_penPoly_deriv P B).continuousOn).div
        ((OQP27.StripL3b.continuous_eval_penPoly P B).continuousOn)
        fun x hx => hneY B hB hBh x.1 hx.1 x.2 hx.2
    exact uniform_circleIntegral (G := fun q z => Complex.log z
      * ((penPoly P B q.1 q.2).derivative.eval z / (penPoly P B q.1 q.2).eval z))
      hSyc hRy0.le hG (by positivity)
  obtain ⟨δfA, hδfA, hfA⟩ := hunifY A (Or.inl rfl) hA
  obtain ⟨δfA₀, hδfA₀, hfA₀⟩ := hunifY A₀ (Or.inr rfl) hA₀
  -- the large roots: `uniform_end_limit` for the rescaled pencils
  have hSwsub : Sw ⊆ {q : ℝ × ℂ | ∀ i, hP.eigenvalues i ≠ p → hP.eigenvalues i ≠ q.1} := by
    intro q hq
    have h1 : |q.1 - p| ≤ d₀ / 2 := by
      rw [abs_le]; constructor <;> linarith [hq.1.1, hq.1.2]
    exact eigenvalue_ne_of_near hP hd₀ hsep h1
  have hZA := (continuousOn_WmatP hP p A).mono hSwsub
  have hZA₀ := (continuousOn_WmatP hP p A₀).mono hSwsub
  have hneWA := hneW A (Or.inl rfl) hA
  have hneWA₀ := hneW A₀ (Or.inr rfl) hA₀
  have heqp : ∀ q ∈ Sw, q.1 = p →
      Matrix.charpoly (WmatP hP p A q) = Matrix.charpoly (WmatP hP p A₀ q) := by
    intro q _ hq1
    obtain ⟨τ, c⟩ := q
    simp only at hq1
    subst hq1
    exact (charpoly_WmatP_self_pinch hP hp A c).symm
  obtain ⟨δL, hδL, hL⟩ := OQP27.StripL3b.uniform_end_limit hSwc (WmatP hP p A) (WmatP hP p A₀)
    hZA hZA₀ hRw0 hneWA hneWA₀ hlogW heqp (ε := π * ε) (by positivity)
  obtain ⟨δ1, hδ1, h1⟩ := OQP27.StripL3b.uniform_end_limit hSwc (WmatP hP p A) (WmatP hP p A₀)
    hZA hZA₀ hRw0 hneWA hneWA₀ (φ := fun _ => 1) continuousOn_const heqp (ε := π) Real.pi_pos
  -- the choice of `δ₀`
  refine ⟨min δ₁ (min (δfA / 2) (min (δfA₀ / 2) (min δL δ1))), lt_min hδ₁ (lt_min (by positivity)
    (lt_min (by positivity) (lt_min hδL hδ1))), fun δ hδ hδm c hc => ?_⟩
  have hδδ₁ : δ < δ₁ := lt_of_lt_of_le hδm (min_le_left _ _)
  have hδfA' : δ < δfA / 2 :=
    lt_of_lt_of_le hδm ((min_le_right _ _).trans (min_le_left _ _))
  have hδfA₀' : δ < δfA₀ / 2 :=
    lt_of_lt_of_le hδm ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδL' : δ < δL := lt_of_lt_of_le hδm ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))))
  have hδ1' : δ < δ1 := lt_of_lt_of_le hδm ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))))
  have hcpos := hKpos c hc
  have hci := hηle c hc
  have hτm : p - δ ∉ spec hP := not_mem_spec_of_near hP hsep (by linarith)
    (by rw [abs_lt]; constructor <;> linarith)
  have hτp : p + δ ∉ spec hP := not_mem_spec_of_near hP hsep (by linarith)
    (by rw [abs_lt]; constructor <;> linarith)
  have hmemm : p - δ ∈ Icc (p - δ₁) (p + δ₁) := ⟨by linarith, by linarith⟩
  have hmemp : p + δ ∈ Icc (p - δ₁) (p + δ₁) := ⟨by linarith, by linarith⟩
  have hlogy : DiffContOnCl ℂ Complex.log (ball zy Ry) := OQP27.StripL3b.diffContOnCl_log_upper hη'
  have hlogw : DiffContOnCl ℂ Complex.log (ball zw Rw) := OQP27.StripL3b.diffContOnCl_log_upper hη2
  -- the right side `τ = p + δ`
  have hright : ∀ B : Matrix (Fin M) (Fin M) ℂ, (B = A ∨ B = A₀) → B.IsHermitian →
      Lup P B (p + δ) c = (2 * π * I)⁻¹ * penInt P B Complex.log zy Ry (p + δ, c) := by
    intro B hB hBh
    have hRt := roots_penPoly_gen hP B hτp c
    refine Lup_eq_penInt hP hτp hRy0 hlogy (fun y hy => ?_) (fun y hy => ?_)
    · rw [← hRt] at hy
      rw [(hCy B hB hBh (p + δ) hmemp c hc y hy).1]
      constructor
      · intro hpos
        refine ⟨hpos, ?_⟩
        by_contra hbig
        obtain ⟨-, hw1, -, -⟩ := (hroot B hB hBh (p + δ) hmemp c hc y hy).2.2 hbig
        have : (p - (p + δ)) * y.im < 0 := by
          have e : p - (p + δ) = -δ := by ring
          have h5 : 0 < δ * y.im := mul_pos hδ hpos
          rw [e]
          linarith
        linarith
      · exact fun h => h.1
    · rw [← hRt] at hy
      exact (hCy B hB hBh (p + δ) hmemp c hc y hy).2
  -- the left side `τ = p - δ`
  have hleft : ∀ B : Matrix (Fin M) (Fin M) ℂ, (B = A ∨ B = A₀) → B.IsHermitian →
      Lup P B (p - δ) c = (2 * π * I)⁻¹ * penInt P B Complex.log zy Ry (p - δ, c)
        + ((2 * π * I)⁻¹ * chiInt (WmatP hP p B (p - δ, c)) Complex.log zw Rw
          - (cntW P B p (p - δ) c zw Rw : ℂ) * (Real.log (p - (p - δ)) : ℂ)) ∧
      (cntW P B p (p - δ) c zw Rw : ℂ)
        = (2 * π * I)⁻¹ * chiInt (WmatP hP p B (p - δ, c)) (fun _ => 1) zw Rw := by
    intro B hB hBh
    have hRt := roots_penPoly_gen hP B hτm c
    have hτ1 : p - δ₁ ≤ p - δ := by linarith
    have hτ2 : p - δ < p := by linarith
    refine Lup_eq_penInt_add hP hτm hτ2 hRy0 hRw0 hlogy hlogw (fun y hy => ?_) (fun y hy => ?_)
      (fun y hy => ?_) (fun y hy => ?_) (fun y hy => ?_)
    · rw [← hRt] at hy
      rw [(hCy B hB hBh (p - δ) hmemm c hc y hy).1, (hCw B hB hBh (p - δ) hτ1 hτ2 c hc y hy).1]
      by_cases hyY : ‖y‖ < Y
      · simp only [hyY, and_true, not_true_eq_false, or_false, iff_self]
      · obtain ⟨-, hw1, -, -⟩ := (hroot B hB hBh (p - δ) hmemm c hc y hy).2.2 hyY
        have hpos : 0 < y.im := by
          have : p - (p - δ) = δ := by ring
          rw [this] at hw1
          by_contra hneg
          push Not at hneg
          have h5 : 0 ≤ δ * (-y.im) := mul_nonneg hδ.le (by linarith)
          linarith
        simp only [hyY, and_false, not_false_eq_true, or_true, iff_true]
        exact hpos
    · rw [← hRt] at hy
      rw [(hCy B hB hBh (p - δ) hmemm c hc y hy).1, (hCw B hB hBh (p - δ) hτ1 hτ2 c hc y hy).1]
      intro h
      exact h.2 h.1.2
    · rw [← hRt] at hy
      exact (hCy B hB hBh (p - δ) hmemm c hc y hy).2
    · rw [← hRt] at hy
      exact (hCw B hB hBh (p - δ) hτ1 hτ2 c hc y hy).2
    · rw [← hRt] at hy
      intro h0
      have := (hroot B hB hBh (p - δ) hmemm c hc y hy).1
      rw [h0, Complex.zero_im] at this
      exact this rfl
  obtain ⟨hLA, hNA⟩ := hleft A (Or.inl rfl) hA
  obtain ⟨hLA₀, hNA₀⟩ := hleft A₀ (Or.inr rfl) hA₀
  have hRA := hright A (Or.inl rfl) hA
  have hRA₀ := hright A₀ (Or.inr rfl) hA₀
  -- membership in the parameter sets
  have hqm : ((p - δ, c) : ℝ × ℂ) ∈ Sw := ⟨⟨by linarith, by linarith⟩, hc⟩
  have hq0 : ((p, c) : ℝ × ℂ) ∈ Sw := ⟨⟨by linarith, le_rfl⟩, hc⟩
  have habs : |(p - δ, c).1 - p| < δL := by
    simp only
    rw [show p - δ - p = -δ by ring, abs_neg, abs_of_pos hδ]
    exact hδL'
  have habs1 : |(p - δ, c).1 - p| < δ1 := by
    simp only
    rw [show p - δ - p = -δ by ring, abs_neg, abs_of_pos hδ]
    exact hδ1'
  have hGL := hL (p - δ, c) hqm habs hq0
  have hG1 := h1 (p - δ, c) hqm habs1 hq0
  -- integrability on `C_w`
  have hintW : ∀ B : Matrix (Fin M) (Fin M) ℂ, (B = A ∨ B = A₀) → B.IsHermitian →
      ∀ φ : ℂ → ℂ, ContinuousOn φ (sphere zw Rw) →
        CircleIntegrable (fun w => φ w * ((Matrix.charpoly (WmatP hP p B (p - δ, c))).derivative.eval w
          / (Matrix.charpoly (WmatP hP p B (p - δ, c))).eval w)) zw Rw := by
    intro B hB hBh φ hφ
    refine ContinuousOn.circleIntegrable hRw0.le (hφ.mul ?_)
    exact ((Polynomial.continuous _).continuousOn).div ((Polynomial.continuous _).continuousOn)
      fun w hw => hneW B hB hBh (p - δ, c) hqm w hw
  -- the counts agree
  have hcnt : (cntW P A p (p - δ) c zw Rw : ℂ) = (cntW P A₀ p (p - δ) c zw Rw : ℂ) := by
    have hdiff : (cntW P A p (p - δ) c zw Rw : ℂ) - (cntW P A₀ p (p - δ) c zw Rw : ℂ)
        = (2 * π * I)⁻¹ * ∮ w in C(zw, Rw), (fun _ => (1 : ℂ)) w
          * ((Matrix.charpoly (WmatP hP p A (p - δ, c))).derivative.eval w
            / (Matrix.charpoly (WmatP hP p A (p - δ, c))).eval w
          - (Matrix.charpoly (WmatP hP p A₀ (p - δ, c))).derivative.eval w
            / (Matrix.charpoly (WmatP hP p A₀ (p - δ, c))).eval w) := by
      rw [hNA, hNA₀, ← mul_sub]
      unfold chiInt
      rw [← circleIntegral.integral_sub (hintW A (Or.inl rfl) hA _ continuousOn_const)
        (hintW A₀ (Or.inr rfl) hA₀ _ continuousOn_const)]
      congr 2
      funext w
      ring
    have hsmall : ‖(cntW P A p (p - δ) c zw Rw : ℂ) - (cntW P A₀ p (p - δ) c zw Rw : ℂ)‖ < 1 := by
      rw [hdiff, norm_mul, norm_two_pi_I_inv]
      calc (2 * π)⁻¹ * _ < (2 * π)⁻¹ * π := by gcongr
        _ < 1 := by
            rw [inv_mul_lt_iff₀ (by positivity)]; linarith [Real.pi_pos]
    have hint' := OQP27.StripL3b.int_cast_eq_zero_of_norm_lt
      (n := (cntW P A p (p - δ) c zw Rw : ℤ) - (cntW P A₀ p (p - δ) c zw Rw : ℤ))
      (by push_cast; exact hsmall)
    have := sub_eq_zero.mp hint'
    exact_mod_cast this
  -- the large parts
  have hgdiff : chiInt (WmatP hP p A (p - δ, c)) Complex.log zw Rw
      - chiInt (WmatP hP p A₀ (p - δ, c)) Complex.log zw Rw
      = ∮ w in C(zw, Rw), Complex.log w
          * ((Matrix.charpoly (WmatP hP p A (p - δ, c))).derivative.eval w
            / (Matrix.charpoly (WmatP hP p A (p - δ, c))).eval w
          - (Matrix.charpoly (WmatP hP p A₀ (p - δ, c))).derivative.eval w
            / (Matrix.charpoly (WmatP hP p A₀ (p - δ, c))).eval w) := by
    unfold chiInt
    rw [← circleIntegral.integral_sub (hintW A (Or.inl rfl) hA _ hlogW)
      (hintW A₀ (Or.inr rfl) hA₀ _ hlogW)]
    congr 1
    funext w
    ring
  -- the bounded parts
  have hdist : dist ((p - δ, c) : ℝ × ℂ) (p + δ, c) < δfA := by
    rw [Prod.dist_eq, Real.dist_eq, dist_self, max_eq_left (abs_nonneg _),
      show p - δ - (p + δ) = -(2 * δ) by ring, abs_neg, abs_of_pos (by linarith)]
    linarith
  have hdist₀ : dist ((p - δ, c) : ℝ × ℂ) (p + δ, c) < δfA₀ := by
    rw [Prod.dist_eq, Real.dist_eq, dist_self, max_eq_left (abs_nonneg _),
      show p - δ - (p + δ) = -(2 * δ) by ring, abs_neg, abs_of_pos (by linarith)]
    linarith
  have hfAb := hfA (p - δ, c) ⟨hmemm, hc⟩ (p + δ, c) ⟨hmemp, hc⟩ hdist
  have hfA₀b := hfA₀ (p - δ, c) ⟨hmemm, hc⟩ (p + δ, c) ⟨hmemp, hc⟩ hdist₀
  -- assembly
  have hfinal : (Lup P A (p - δ) c - Lup P A₀ (p - δ) c) - (Lup P A (p + δ) c - Lup P A₀ (p + δ) c)
      = (2 * π * I)⁻¹ * ((penInt P A Complex.log zy Ry (p - δ, c)
          - penInt P A Complex.log zy Ry (p + δ, c))
        - (penInt P A₀ Complex.log zy Ry (p - δ, c) - penInt P A₀ Complex.log zy Ry (p + δ, c))
        + (chiInt (WmatP hP p A (p - δ, c)) Complex.log zw Rw
          - chiInt (WmatP hP p A₀ (p - δ, c)) Complex.log zw Rw)) := by
    rw [hLA, hLA₀, hRA, hRA₀, hcnt]
    ring
  rw [hfinal, hgdiff, norm_mul, norm_two_pi_I_inv]
  have hbound : ‖(penInt P A Complex.log zy Ry (p - δ, c) - penInt P A Complex.log zy Ry (p + δ, c))
        - (penInt P A₀ Complex.log zy Ry (p - δ, c) - penInt P A₀ Complex.log zy Ry (p + δ, c))
        + ∮ w in C(zw, Rw), Complex.log w
          * ((Matrix.charpoly (WmatP hP p A (p - δ, c))).derivative.eval w
            / (Matrix.charpoly (WmatP hP p A (p - δ, c))).eval w
          - (Matrix.charpoly (WmatP hP p A₀ (p - δ, c))).derivative.eval w
            / (Matrix.charpoly (WmatP hP p A₀ (p - δ, c))).eval w)‖ < 2 * π * ε := by
    calc _ ≤ ‖(penInt P A Complex.log zy Ry (p - δ, c) - penInt P A Complex.log zy Ry (p + δ, c))
          - (penInt P A₀ Complex.log zy Ry (p - δ, c) - penInt P A₀ Complex.log zy Ry (p + δ, c))‖
          + ‖∮ w in C(zw, Rw), Complex.log w
            * ((Matrix.charpoly (WmatP hP p A (p - δ, c))).derivative.eval w
              / (Matrix.charpoly (WmatP hP p A (p - δ, c))).eval w
            - (Matrix.charpoly (WmatP hP p A₀ (p - δ, c))).derivative.eval w
              / (Matrix.charpoly (WmatP hP p A₀ (p - δ, c))).eval w)‖ := norm_add_le _ _
      _ ≤ (‖penInt P A Complex.log zy Ry (p - δ, c) - penInt P A Complex.log zy Ry (p + δ, c)‖
          + ‖penInt P A₀ Complex.log zy Ry (p - δ, c) - penInt P A₀ Complex.log zy Ry (p + δ, c)‖)
          + ‖∮ w in C(zw, Rw), Complex.log w
            * ((Matrix.charpoly (WmatP hP p A (p - δ, c))).derivative.eval w
              / (Matrix.charpoly (WmatP hP p A (p - δ, c))).eval w
            - (Matrix.charpoly (WmatP hP p A₀ (p - δ, c))).derivative.eval w
              / (Matrix.charpoly (WmatP hP p A₀ (p - δ, c))).eval w)‖ :=
          add_le_add (norm_sub_le _ _) le_rfl
      _ < (π * ε / 2 + π * ε / 2) + π * ε := by
          refine add_lt_add (add_lt_add hfAb hfA₀b) hGL
      _ = 2 * π * ε := by ring
  calc (2 * π)⁻¹ * _ < (2 * π)⁻¹ * (2 * π * ε) := by gcongr
    _ = ε := by field_simp

end HarmonicMajorization
