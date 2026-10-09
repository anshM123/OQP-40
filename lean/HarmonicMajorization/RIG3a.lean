import HarmonicMajorization.RIG2

/-!
# The pencil near a point of the spectrum (proof of the multi-line RI, III)

Authors: Ansh Mishra, Aryan Senthilkumar.  License: MIT.

`P` Hermitian, `p ∈ ℝ`, `B` Hermitian, `Im c > 0`.
* `penPoly_ne_zero_of_im_pos`: `z ↦ det(B + c - z(P - τ))` is a nonzero polynomial for every real `τ`
  (its value at `0` is `det(B + c) ≠ 0`); `exists_eigvec_of_root`: its roots come with eigenvectors;
* `im_bounds_of_eigvec`: Lemma A for every real `τ` (also on the spectrum);
* `dichotomy`: for `|τ - p| ≤ d₀/2` (`d₀` the distance from `p` to the other eigenvalues) every
  large root `y` has `w = (p - τ) y` with `Im w ≥ Im c / 2` and `|w|² ≤ 2F`;
* `WmatP`: the rescaled pencil `(p - τ)(P - τ)⁻¹(B + c)`, continuous up to `τ = p` with value
  `Q_p (B + c)` there; `charpoly_WmatP_self_pinch`: at `τ = p` the matrices for `A` and `A_d` have the
  same characteristic polynomial; `roots_WmatP_self`: its non-zero roots lie on `Im w = Im c`.

No hypotheses.
-/

set_option autoImplicit false

namespace HarmonicMajorization

open Matrix Polynomial Complex Metric Filter Topology Set Real
open OQP27.StripL3b (pencilRoots imAbsSum frob Rt Sup Slo Lup Llo penPoly upperRoots lowerRoots
  upCenter upRadius loCenter)

variable {M : ℕ}

/-! ### The pencil polynomial for `Im c > 0` -/

lemma det_add_smul_ne_zero {B : Matrix (Fin M) (Fin M) ℂ} (hB : B.IsHermitian) {c : ℂ}
    (hc : 0 < c.im) : (B + c • (1 : Matrix (Fin M) (Fin M) ℂ)).det ≠ 0 := by
  rw [OQP27.StripL3b.det_add_smul_one_eq_prod hB c, Finset.prod_ne_zero_iff]
  intro i _ h
  have h2 : ((hB.eigenvalues i : ℂ) + c).im = c.im := by simp
  rw [h, Complex.zero_im] at h2
  linarith

lemma penPoly_ne_zero_of_im_pos (P : Matrix (Fin M) (Fin M) ℂ) {B : Matrix (Fin M) (Fin M) ℂ}
    (hB : B.IsHermitian) (τ : ℝ) {c : ℂ} (hc : 0 < c.im) : penPoly P B τ c ≠ 0 := by
  intro h
  have h2 := congrArg (Polynomial.eval 0) h
  rw [OQP27.StripL3b.eval_penPoly, Polynomial.eval_zero, zero_smul, sub_zero] at h2
  exact det_add_smul_ne_zero hB hc h2

lemma exists_eigvec_of_root {P B : Matrix (Fin M) (Fin M) ℂ} {τ : ℝ} {c z : ℂ}
    (hp : penPoly P B τ c ≠ 0) (hz : z ∈ (penPoly P B τ c).roots) :
    ∃ v : Fin M → ℂ, v ≠ 0 ∧ (B + c • 1) *ᵥ v = z • ((P - (τ : ℂ) • 1) *ᵥ v) := by
  have h0 : (penPoly P B τ c).eval z = 0 := (Polynomial.mem_roots hp).mp hz
  rw [OQP27.StripL3b.eval_penPoly] at h0
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  refine ⟨v, hv0, ?_⟩
  rw [Matrix.sub_mulVec, sub_eq_zero, Matrix.smul_mulVec] at hv
  exact hv

/-! ### Lemma A and the dichotomy, for every real `τ` -/

section Dichotomy

variable {P B : Matrix (Fin M) (Fin M) ℂ} (hP : P.IsHermitian) (hB : B.IsHermitian)
include hP hB

/-- **Lemma A** for an eigenvector at any real `τ`. -/
lemma im_bounds_of_eigvec {L U : ℝ} (hL : ∀ i, L ≤ hP.eigenvalues i)
    (hU : ∀ i, hP.eigenvalues i ≤ U) (τ : ℝ) {c : ℂ} (hc : 0 < c.im) {y : ℂ}
    {v : Fin M → ℂ} (hv0 : v ≠ 0) (hv : (B + c • 1) *ᵥ v = y • ((P - (τ : ℂ) • 1) *ᵥ v)) :
    y.im ≠ 0 ∧ (0 < y.im → c.im ≤ (U - τ) * y.im) ∧ (y.im < 0 → c.im ≤ (L - τ) * y.im) := by
  have hkey := root_im_identity_gen hP hB τ c hv
  have hn := re_dot_self_eq_sum hP v
  have ha := re_dot_sub_eq_sum hP τ v
  have hnpos := OQP27.StripL3b.re_star_dotProduct_self_pos hv0
  set n := (star v ⬝ᵥ v).re
  set a := (star v ⬝ᵥ ((P - (τ : ℂ) • 1) *ᵥ v)).re
  have hup : a ≤ (U - τ) * n := by
    rw [ha, hn, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (by linarith [hU i]) (by positivity)
  have hlo : (L - τ) * n ≤ a := by
    rw [ha, hn, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (by linarith [hL i]) (by positivity)
  have hcn : 0 < c.im * n := mul_pos hc hnpos
  refine ⟨fun h => by rw [h, zero_mul] at hkey; linarith, fun hy0 => ?_, fun hy0 => ?_⟩
  · have : c.im * n ≤ (U - τ) * y.im * n := by
      rw [hkey]; nlinarith
    nlinarith
  · have : c.im * n ≤ (L - τ) * y.im * n := by
      rw [hkey]; nlinarith
    nlinarith

omit hP hB in
/-- The real-variable core of the dichotomy. -/
lemma dichotomy_real {lam x : Fin M → ℝ} (hx : ∀ i, 0 ≤ x i) {p d₀ τ D F η ci yn yi : ℝ}
    (hd₀ : 0 < d₀) (hsep : ∀ i, lam i ≠ p → d₀ ≤ |lam i - p|) (hτ : |τ - p| ≤ d₀ / 2)
    (hD : ∀ i, |lam i - τ| ≤ D) (hD0 : 0 ≤ D) (hF : 0 < F) (hη : 0 < η) (hηc : η ≤ ci)
    (hn : 0 < ∑ i, x i)
    (hkey : ci * ∑ i, x i = yi * ∑ i, (lam i - τ) * x i)
    (hfro : yn ^ 2 * ∑ i, (lam i - τ) ^ 2 * x i ≤ F * ∑ i, x i)
    (hyi : |yi| ≤ yn) (hy1 : 32 * F ≤ yn ^ 2 * d₀ ^ 2) (hy2 : 32 * F * D ≤ η * d₀ ^ 2 * yn) :
    ci / 2 ≤ (p - τ) * yi ∧ ((p - τ) * yn) ^ 2 ≤ 2 * F := by
  classical
  have hyn : 0 ≤ yn := (abs_nonneg yi).trans hyi
  have hci : 0 < ci := lt_of_lt_of_le hη hηc
  set S := Finset.univ.filter (fun i : Fin M => lam i = p) with hS
  set T := Finset.univ.filter (fun i : Fin M => ¬ lam i = p) with hT
  set nu := ∑ i ∈ S, x i with hnu
  set n' := ∑ i ∈ T, x i with hn'
  have hnu0 : 0 ≤ nu := Finset.sum_nonneg fun i _ => hx i
  have hn'0 : 0 ≤ n' := Finset.sum_nonneg fun i _ => hx i
  have hsplit : ∑ i, x i = nu + n' := (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  set R := ∑ i ∈ T, (lam i - τ) * x i with hR
  have hsplit1 : ∑ i, (lam i - τ) * x i = (p - τ) * nu + R := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => lam i = p), hnu,
      Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [(Finset.mem_filter.mp hi).2]
  have hRb : |R| ≤ D * n' := by
    rw [hR, hn', Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul, abs_of_nonneg (hx i)]
    exact mul_le_mul_of_nonneg_right (hD i) (hx i)
  set R2 := ∑ i ∈ T, (lam i - τ) ^ 2 * x i with hR2
  have hsplit2 : ∑ i, (lam i - τ) ^ 2 * x i = (p - τ) ^ 2 * nu + R2 := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => lam i = p), hnu,
      Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [(Finset.mem_filter.mp hi).2]
  have hR2b : d₀ ^ 2 / 4 * n' ≤ R2 := by
    rw [hR2, hn', Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right ?_ (hx i)
    have hne := (Finset.mem_filter.mp hi).2
    have h1 := hsep i hne
    have h2 : d₀ / 2 ≤ |lam i - τ| := by
      have h3 := abs_sub_abs_le_abs_sub (lam i - p) (τ - p)
      have h4 : lam i - p - (τ - p) = lam i - τ := by ring
      rw [h4] at h3
      linarith
    have h5 : (d₀ / 2) ^ 2 ≤ |lam i - τ| ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
    rw [sq_abs] at h5
    linarith
  set t := yn ^ 2 * d₀ ^ 2 with ht
  have htpos : 0 < t := by linarith
  -- `7 t n' ≤ 32 F nu`
  have hA : t * n' ≤ 4 * F * (nu + n') := by
    have h1 : yn ^ 2 * R2 ≤ F * (nu + n') := by
      have h2 : 0 ≤ yn ^ 2 * ((p - τ) ^ 2 * nu) := by positivity
      rw [hsplit2, hsplit] at hfro
      linarith
    have h3 : yn ^ 2 * (d₀ ^ 2 / 4 * n') ≤ yn ^ 2 * R2 :=
      mul_le_mul_of_nonneg_left hR2b (by positivity)
    have h4 : t * n' = 4 * (yn ^ 2 * (d₀ ^ 2 / 4 * n')) := by rw [ht]; ring
    linarith
  have hB7 : 7 * t * n' ≤ 32 * F * nu := by
    have h := mul_le_mul_of_nonneg_right hy1 hn'0
    linarith
  have hnupos : 0 < nu := by
    rcases lt_or_eq_of_le hnu0 with h | h
    · exact h
    · exfalso
      rw [← h] at hB7
      have : n' = 0 := by
        have h7 : 7 * t * n' ≤ 0 := by linarith
        have h8 : 0 ≤ 7 * t * n' := by positivity
        have h9 : 7 * t * n' = 0 := le_antisymm h7 h8
        rcases mul_eq_zero.mp h9 with h10 | h10
        · exfalso; linarith
        · exact h10
      rw [hsplit, ← h, this] at hn
      linarith
  have hn'le : n' ≤ nu := by
    have h := mul_le_mul_of_nonneg_right hy1 hnu0
    have h2 : t * (7 * n') ≤ t * nu := by linarith
    have h3 := le_of_mul_le_mul_left h2 htpos
    linarith
  -- the imaginary part
  have hI : ((p - τ) * yi - ci) * nu = ci * n' - yi * R := by
    rw [hsplit, hsplit1] at hkey
    linarith
  have hI2 : |(p - τ) * yi - ci| * nu ≤ (ci + yn * D) * n' := by
    rw [← abs_of_pos hnupos, ← abs_mul, hI]
    have h1 : |ci * n' - yi * R| ≤ ci * n' + |yi| * |R| := by
      have := abs_sub (ci * n') (yi * R)
      rw [abs_mul (ci) (n'), abs_of_pos hci, abs_of_nonneg hn'0, abs_mul] at this
      exact this
    have h2 : |yi| * |R| ≤ yn * (D * n') :=
      mul_le_mul hyi hRb (abs_nonneg _) hyn
    linarith
  have hI3 : 7 * t * |(p - τ) * yi - ci| ≤ 2 * t * ci := by
    have h1 : 7 * t * (|(p - τ) * yi - ci| * nu) ≤ (ci + yn * D) * (7 * t * n') := by
      have := mul_le_mul_of_nonneg_left hI2 (by positivity : (0 : ℝ) ≤ 7 * t)
      linarith
    have h2 : (ci + yn * D) * (7 * t * n') ≤ (ci + yn * D) * (32 * F * nu) :=
      mul_le_mul_of_nonneg_left hB7 (by positivity)
    have h3 : (ci + yn * D) * 32 * F ≤ 2 * t * ci := by
      have h4 : 32 * F * D * yn ≤ η * d₀ ^ 2 * yn * yn := mul_le_mul_of_nonneg_right hy2 hyn
      have h5 : η * d₀ ^ 2 * yn * yn = η * t := by rw [ht]; ring
      have h6 : η * t ≤ ci * t := mul_le_mul_of_nonneg_right hηc htpos.le
      have h7 : 32 * F * ci ≤ t * ci := mul_le_mul_of_nonneg_right hy1 hci.le
      linarith
    have h9 := mul_le_mul_of_nonneg_right h3 hnu0
    have h8 : 7 * t * |(p - τ) * yi - ci| * nu ≤ 2 * t * ci * nu := by linarith
    exact le_of_mul_le_mul_right h8 hnupos
  have hI4 : |(p - τ) * yi - ci| ≤ 2 / 7 * ci := by
    have h1 : t * (7 * |(p - τ) * yi - ci|) ≤ t * (2 * ci) := by linarith
    have h2 := le_of_mul_le_mul_left h1 htpos
    linarith
  refine ⟨?_, ?_⟩
  · have := (abs_le.mp hI4).1
    linarith
  · -- `|w|² nu ≤ yn² Σ (λ - τ)² x ≤ F (nu + n') ≤ 2 F nu`
    have h1 : ((p - τ) * yn) ^ 2 * nu ≤ F * (nu + n') := by
      have h2 : 0 ≤ yn ^ 2 * R2 := mul_nonneg (by positivity)
        (Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (hx i))
      rw [hsplit2, hsplit] at hfro
      linarith
    have h4 := mul_le_mul_of_nonneg_left hn'le hF.le
    have h3 : ((p - τ) * yn) ^ 2 * nu ≤ 2 * F * nu := by linarith
    exact le_of_mul_le_mul_right h3 hnupos

/-- **The dichotomy near a spectral point.**  Let `d₀ ≤ |λ_i - p|` whenever `λ_i ≠ p`,
`|τ - p| ≤ d₀/2`, `|λ_i - τ| ≤ D`, `‖B + c‖_F² ≤ F`, `η ≤ Im c`.  If a root `y` (with eigenvector `v`)
is large, `32 F ≤ |y|² d₀²` and `32 F D ≤ η d₀² |y|`, then `w = (p - τ) y` satisfies
`Im w ≥ Im c / 2` and `|w|² ≤ 2F`. -/
lemma dichotomy {p d₀ τ D F η : ℝ} (hd₀ : 0 < d₀)
    (hsep : ∀ i, hP.eigenvalues i ≠ p → d₀ ≤ |hP.eigenvalues i - p|) (hτ : |τ - p| ≤ d₀ / 2)
    (hD : ∀ i, |hP.eigenvalues i - τ| ≤ D) (hD0 : 0 ≤ D) (hF : 0 < F) {c : ℂ} (hη : 0 < η)
    (hηc : η ≤ c.im)
    (hFc : frob (B + c • 1) ≤ F) {y : ℂ} {v : Fin M → ℂ} (hv0 : v ≠ 0)
    (hv : (B + c • 1) *ᵥ v = y • ((P - (τ : ℂ) • 1) *ᵥ v))
    (hy1 : 32 * F ≤ ‖y‖ ^ 2 * d₀ ^ 2) (hy2 : 32 * F * D ≤ η * d₀ ^ 2 * ‖y‖) :
    c.im / 2 ≤ (p - τ) * y.im ∧ ((p - τ) * ‖y‖) ^ 2 ≤ 2 * F := by
  have hkey := root_im_identity_gen hP hB τ c hv
  have hn := re_dot_self_eq_sum hP v
  have ha := re_dot_sub_eq_sum hP τ v
  have hq := re_norm_sub_sq_eq_sum hP τ v
  have hnpos := OQP27.StripL3b.re_star_dotProduct_self_pos hv0
  -- the Frobenius bound: `|y|² |(P - τ) v|² ≤ F |v|²`
  have hfro : ‖y‖ ^ 2 * (star ((P - (τ : ℂ) • 1) *ᵥ v) ⬝ᵥ ((P - (τ : ℂ) • 1) *ᵥ v)).re
      ≤ F * (star v ⬝ᵥ v).re := by
    have hAv : star ((B + c • 1) *ᵥ v) ⬝ᵥ ((B + c • 1) *ᵥ v)
        = ((‖y‖ : ℂ) ^ 2) * (star ((P - (τ : ℂ) • 1) *ᵥ v) ⬝ᵥ ((P - (τ : ℂ) • 1) *ᵥ v)) := by
      rw [hv, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
        Complex.star_def, Complex.conj_mul']
    have hle := OQP27.StripL3b.re_dot_mulVec_le_frob (B + c • 1) v
    rw [hAv] at hle
    have hre : (((‖y‖ : ℂ) ^ 2) * (star ((P - (τ : ℂ) • 1) *ᵥ v) ⬝ᵥ ((P - (τ : ℂ) • 1) *ᵥ v))).re
        = ‖y‖ ^ 2 * (star ((P - (τ : ℂ) • 1) *ᵥ v) ⬝ᵥ ((P - (τ : ℂ) • 1) *ᵥ v)).re := by
      have e : ((‖y‖ : ℂ) ^ 2) = ((‖y‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
      rw [e, Complex.re_ofReal_mul]
    rw [hre] at hle
    exact hle.trans (mul_le_mul_of_nonneg_right hFc hnpos.le)
  rw [hn, hq] at hfro
  rw [hn, ha] at hkey
  rw [hn] at hnpos
  exact dichotomy_real (lam := hP.eigenvalues) (x := fun i => ‖(star (eU hP) *ᵥ v) i‖ ^ 2)
    (fun i => by positivity) hd₀ hsep hτ hD hD0 hF hη hηc hnpos hkey hfro
    (Complex.abs_im_le_norm y) hy1 hy2

end Dichotomy

/-! ### Separation from the other eigenvalues -/

lemma exists_sep {P : Matrix (Fin M) (Fin M) ℂ} (hP : P.IsHermitian) (p : ℝ) :
    ∃ d₀ > 0, d₀ ≤ 1 ∧ ∀ i, hP.eigenvalues i ≠ p → d₀ ≤ |hP.eigenvalues i - p| := by
  classical
  set T := Finset.univ.filter (fun i : Fin M => hP.eigenvalues i ≠ p) with hT
  rcases T.eq_empty_or_nonempty with hTe | hTne
  · refine ⟨1, one_pos, le_rfl, fun i hi => ?_⟩
    have : i ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
    rw [hTe] at this
    exact absurd this (Finset.notMem_empty i)
  · obtain ⟨i₀, hi₀, hmin⟩ := T.exists_min_image (fun i => |hP.eigenvalues i - p|) hTne
    have hpos : 0 < |hP.eigenvalues i₀ - p| :=
      abs_pos.mpr (sub_ne_zero.mpr (Finset.mem_filter.mp hi₀).2)
    refine ⟨min (|hP.eigenvalues i₀ - p|) 1, lt_min hpos one_pos, min_le_right _ _, fun i hi => ?_⟩
    exact (min_le_left _ _).trans (hmin i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩))

lemma not_mem_spec_of_near {P : Matrix (Fin M) (Fin M) ℂ} (hP : P.IsHermitian) {p d₀ τ : ℝ}
    (hsep : ∀ i, hP.eigenvalues i ≠ p → d₀ ≤ |hP.eigenvalues i - p|) (h1 : τ ≠ p)
    (h2 : |τ - p| < d₀) : τ ∉ spec hP := by
  intro h
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp h
  have hne : hP.eigenvalues i ≠ p := by rw [hi]; exact h1
  have := hsep i hne
  rw [hi] at this
  linarith

lemma eigenvalue_ne_of_near {P : Matrix (Fin M) (Fin M) ℂ} (hP : P.IsHermitian) {p d₀ τ : ℝ}
    (hd₀ : 0 < d₀) (hsep : ∀ i, hP.eigenvalues i ≠ p → d₀ ≤ |hP.eigenvalues i - p|)
    (h2 : |τ - p| ≤ d₀ / 2) : ∀ i, hP.eigenvalues i ≠ p → hP.eigenvalues i ≠ τ := by
  intro i hi h
  have := hsep i hi
  rw [h] at this
  linarith

/-! ### The rescaled pencil at a spectral point -/

section Wmat

variable {P : Matrix (Fin M) (Fin M) ℂ} (hP : P.IsHermitian)

/-- The weights `(p - τ)/(λ_i - τ)`, with the value `1` on the eigenvalue `p`. -/
noncomputable def wgtP (p τ : ℝ) : Fin M → ℂ :=
  fun i => if hP.eigenvalues i = p then 1 else (((p - τ) / (hP.eigenvalues i - τ) : ℝ) : ℂ)

/-- The rescaled pencil `W_p(τ, c) = (p - τ)(P - τ)⁻¹(B + c)` (continuous up to `τ = p`). -/
noncomputable def WmatP (p : ℝ) (B : Matrix (Fin M) (Fin M) ℂ) (q : ℝ × ℂ) :
    Matrix (Fin M) (Fin M) ℂ :=
  fcalc hP (wgtP hP p q.1) * (B + q.2 • 1)

lemma WmatP_eq (p : ℝ) (B : Matrix (Fin M) (Fin M) ℂ) {τ : ℝ} (hτ : τ ∉ spec hP) (c : ℂ) :
    WmatP hP p B (τ, c)
      = (((p - τ : ℝ)) : ℂ) • ((P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ))⁻¹ * (B + c • 1)) := by
  rw [inv_sub_eq_fcalc hP hτ, ← Matrix.smul_mul, ← fcalc_smul]
  unfold WmatP
  congr 2
  funext i
  unfold wgtP
  simp only [Pi.smul_apply, smul_eq_mul]
  have hne : hP.eigenvalues i - τ ≠ 0 := by
    rw [sub_ne_zero]; intro h; exact hτ (h ▸ eigenvalues_mem_spec hP i)
  split_ifs with h
  · rw [h] at hne
    have hne' : ((p - τ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hne
    rw [h, mul_inv_cancel₀ hne']
  · push_cast
    rw [div_eq_mul_inv]

lemma roots_WmatP (p : ℝ) (B : Matrix (Fin M) (Fin M) ℂ) {τ : ℝ} (hτ : τ ∉ spec hP)
    (hpτ : p ≠ τ) (c : ℂ) :
    (Matrix.charpoly (WmatP hP p B (τ, c))).roots = (Rt P B τ c).map ((((p - τ : ℝ)) : ℂ) * ·) := by
  rw [WmatP_eq hP p B hτ c, OQP27.StripL3b.roots_charpoly_smul _
    (by exact_mod_cast sub_ne_zero.mpr hpτ)]
  rfl

lemma wgtP_self (p : ℝ) : wgtP hP p p = ind hP p := by
  funext i
  unfold wgtP ind
  split_ifs <;> simp

lemma WmatP_self (p : ℝ) (B : Matrix (Fin M) (Fin M) ℂ) (c : ℂ) :
    WmatP hP p B (p, c) = sproj hP p * (B + c • 1) := by
  unfold WmatP sproj
  rw [wgtP_self]

lemma continuousOn_WmatP (p : ℝ) (B : Matrix (Fin M) (Fin M) ℂ) :
    ContinuousOn (WmatP hP p B)
      {q : ℝ × ℂ | ∀ i, hP.eigenvalues i ≠ p → hP.eigenvalues i ≠ q.1} := by
  have hw : ContinuousOn (fun q : ℝ × ℂ => wgtP hP p q.1)
      {q : ℝ × ℂ | ∀ i, hP.eigenvalues i ≠ p → hP.eigenvalues i ≠ q.1} := by
    refine continuousOn_pi.mpr fun i => ?_
    by_cases h : hP.eigenvalues i = p
    · have e : (fun q : ℝ × ℂ => wgtP hP p q.1 i) = fun _ => (1 : ℂ) := by
        funext q; simp [wgtP, h]
      rw [e]
      exact continuousOn_const
    · have e : (fun q : ℝ × ℂ => wgtP hP p q.1 i)
          = fun q => (((p - q.1) / (hP.eigenvalues i - q.1) : ℝ) : ℂ) := by
        funext q; simp [wgtP, h]
      rw [e]
      refine Complex.continuous_ofReal.comp_continuousOn ?_
      refine ContinuousOn.div (by fun_prop) (by fun_prop) fun q hq => ?_
      exact sub_ne_zero.mpr (hq i h)
  have h1 := (continuous_fcalc hP).comp_continuousOn hw
  have h2 : Continuous (fun q : ℝ × ℂ => B + q.2 • (1 : Matrix (Fin M) (Fin M) ℂ)) := by fun_prop
  exact h1.mul h2.continuousOn

/-- At `τ = p` the rescaled pencils of `A` and `A_d` have the same characteristic polynomial. -/
lemma charpoly_WmatP_self_pinch {p : ℝ} (hp : p ∈ spec hP) (A : Matrix (Fin M) (Fin M) ℂ)
    (c : ℂ) :
    Matrix.charpoly (WmatP hP p (pinchH hP A) (p, c)) = Matrix.charpoly (WmatP hP p A (p, c)) := by
  have hQ : sproj hP p * sproj hP p = sproj hP p := sproj_mul_self hP p
  rw [WmatP_self, WmatP_self, OQP27.StripL3b.charpoly_proj_mul hQ,
    OQP27.StripL3b.charpoly_proj_mul hQ]
  congr 1
  rw [Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul, sproj_mul_pinchH hP A hp,
    Matrix.mul_assoc (sproj hP p * A) (sproj hP p) (sproj hP p), hQ]

/-- At `τ = p` the roots of the rescaled pencil are `0` or lie on the line `Im w = Im c`. -/
lemma roots_WmatP_self (p : ℝ) {B : Matrix (Fin M) (Fin M) ℂ} (hB : B.IsHermitian) (c : ℂ)
    {w : ℂ} (hw : w ∈ (Matrix.charpoly (WmatP hP p B (p, c))).roots) :
    w = 0 ∨ (w.im = c.im ∧ ‖w‖ ^ 2 ≤ frob (B + c • 1)) := by
  have hQ : sproj hP p * sproj hP p = sproj hP p := sproj_mul_self hP p
  rw [WmatP_self, OQP27.StripL3b.charpoly_proj_mul hQ] at hw
  have hw' : w ∈ (Matrix.charpoly (((1 : ℝ) : ℂ) • (sproj hP p * (B + c • 1) * sproj hP p))).roots := by
    simpa using hw
  rcases OQP27.StripL3b.root_compression ⟨isHermitian_sproj hP p, hQ⟩ hB (s := 1) (by norm_num) c
    hw' with h | ⟨h1, h2⟩
  · exact Or.inl h
  · exact Or.inr ⟨by rw [h1, one_mul], h2⟩

end Wmat

/-! ### Generic helpers -/

/-- Splitting a filter into two disjoint filters. -/
lemma filter_eq_add_filter {S : Multiset ℂ} {p q r : ℂ → Prop} [DecidablePred p]
    [DecidablePred q] [DecidablePred r] (h : ∀ y ∈ S, (p y ↔ q y ∨ r y))
    (hd : ∀ y ∈ S, ¬ (q y ∧ r y)) :
    S.filter p = S.filter q + S.filter r := by
  rw [Multiset.filter_add_filter, Multiset.filter_congr h,
    Multiset.filter_eq_nil.mpr (fun y hy => hd y hy), add_zero]

/-- The sum of `φ` over the roots inside a circle as a contour integral. -/
lemma sum_filter_eq_circleIntegral (p : ℂ[X]) (hp : p ≠ 0) {z₀ : ℂ} {R : ℝ} (hR : 0 < R)
    (hroot : ∀ a ∈ p.roots, dist a z₀ ≠ R) {φ : ℂ → ℂ} (hφ : DiffContOnCl ℂ φ (ball z₀ R)) :
    ((p.roots.filter fun a => dist a z₀ < R).map φ).sum
      = (2 * π * I)⁻¹ * ∮ z in C(z₀, R), φ z * (p.derivative.eval z / p.eval z) := by
  rw [OQP27.StripL3b.circleIntegral_mul_logDeriv p hp hR hroot hφ, ← mul_assoc,
    inv_mul_cancel₀ (by simp [Real.pi_ne_zero, I_ne_zero]), one_mul]

/-- Uniform continuity of a parametric circle integral on a compact parameter set. -/
lemma uniform_circleIntegral {S : Set (ℝ × ℂ)} (hS : IsCompact S) {G : ℝ × ℂ → ℂ → ℂ} {z₀ : ℂ}
    {R : ℝ} (hR : 0 ≤ R) (hG : ContinuousOn (fun x : (ℝ × ℂ) × ℂ => G x.1 x.2) (S ×ˢ sphere z₀ R))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ q ∈ S, ∀ q' ∈ S, dist q q' < δ →
      ‖(∮ z in C(z₀, R), G q z) - ∮ z in C(z₀, R), G q' z‖ < ε := by
  have hc := OQP27.StripL3b.continuousOn_circleIntegral (F := G) hR hG
  have hU := hS.uniformContinuousOn_of_continuous hc
  rw [Metric.uniformContinuousOn_iff] at hU
  obtain ⟨δ, hδ, h⟩ := hU ε hε
  refine ⟨δ, hδ, fun q hq q' hq' hd => ?_⟩
  have := h q hq q' hq' hd
  rwa [dist_eq_norm] at this

end HarmonicMajorization
