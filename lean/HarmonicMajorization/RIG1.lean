import HarmonicMajorization.PencilGen
import OQP27.StripRIMain

/-!
# The shifted pencil for a Hermitian `P`: root location and bounds (proof of the multi-line RI, I)

Authors: Ansh Mishra, Aryan Senthilkumar.  License: MIT.

`P` Hermitian (`hP`), eigenvalues `λ_i ∈ [L, U]`, `A` Hermitian, `c ∈ ℂ₊`, `τ ∉ spec P`.  The roots
`Rt P A τ c` of `y ↦ det(A + c - y(P - τ))` and the half-plane sums `Sup`, `Slo`, `Lup`, `Llo` are those
of `OQP27/StripRISums.lean` (defined for any `P`); the pinched matrix is `pinchH hP A`.

Main results (generalising Lemmas A, B of [27, Appendix RI] from a projection to a Hermitian `P`):
* `pencilRoot_im_bounds_gen`: no real roots; `Im c ≤ (U - τ) Im y` in `ℂ₊`, `Im c ≤ (L - τ) Im y` in `ℂ₋`;
* `pencilRoot_norm_bound_dist`: `|y|² d² ≤ ‖A + c‖_F²` if `d ≤ |λ_i - τ|` for all `i` (Lemma B(i));
* `pencilRoot_norm_bound_gap`: on a gap `α < τ < β` of `spec P`, `|y|² (τ - α)(β - τ) ≤ ‖A + c‖_F²` for
  roots in `ℂ₊` if `τ ≤ (α + β)/2` and for roots in `ℂ₋` if `τ ≥ (α + β)/2` (Lemma B(ii));
* `roots_penPoly_gen`, `penPoly_ne_zero_gen`, `penPoly_leadingCoeff_gen`, `penPoly_natDegree_gen`;
* `sum_Rt_pinchH`, `Sup_sub_eq_gen`, `norm_Sup_sub_le_gap` (Lemma B(iii) on a gap);
* `Sup_sub_eq_zero_of_lt`, `Sup_sub_eq_zero_of_gt`: `S_+(A) = S_+(A_d)` outside `[L, U]`.

No hypotheses.
-/

set_option autoImplicit false

namespace HarmonicMajorization

open Matrix Polynomial Complex Metric Filter Topology Set Real
open OQP27.StripL3b (pencilRoots imAbsSum frob Rt Sup Slo Lup Llo penPoly upperRoots lowerRoots)

variable {M : ℕ}

section Quad

variable {P : Matrix (Fin M) (Fin M) ℂ} (hP : P.IsHermitian)
include hP

/-- `Re ⟨v, v⟩ = Σ_i |(U* v)_i|²`. -/
lemma re_dot_self_eq_sum (v : Fin M → ℂ) :
    (star v ⬝ᵥ v).re = ∑ i, ‖(star (eU hP) *ᵥ v) i‖ ^ 2 := by
  have h := re_dot_fcalc hP (fun _ => (1 : ℝ)) v
  have e : fcalc hP (fun _ => (((1 : ℝ)) : ℂ)) = 1 := by
    rw [show (fun _ : Fin M => (((1 : ℝ)) : ℂ)) = 1 by funext; simp, fcalc_one]
  rw [e, Matrix.one_mulVec] at h
  simpa using h

/-- `Re ⟨v, (P - τ) v⟩ = Σ_i (λ_i - τ) |(U* v)_i|²`. -/
lemma re_dot_sub_eq_sum (τ : ℝ) (v : Fin M → ℂ) :
    (star v ⬝ᵥ ((P - (τ : ℂ) • 1) *ᵥ v)).re
      = ∑ i, (hP.eigenvalues i - τ) * ‖(star (eU hP) *ᵥ v) i‖ ^ 2 := by
  rw [sub_smul_eq_fcalc hP τ]
  exact re_dot_fcalc hP (fun i => hP.eigenvalues i - τ) v

/-- `|(P - τ) v|² = Σ_i (λ_i - τ)² |(U* v)_i|²`. -/
lemma re_norm_sub_sq_eq_sum (τ : ℝ) (v : Fin M → ℂ) :
    (star ((P - (τ : ℂ) • 1) *ᵥ v) ⬝ᵥ ((P - (τ : ℂ) • 1) *ᵥ v)).re
      = ∑ i, (hP.eigenvalues i - τ) ^ 2 * ‖(star (eU hP) *ᵥ v) i‖ ^ 2 := by
  have hQ := OQP27.StripL3b.isHermitian_P_sub hP τ
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hQ.eq, Matrix.mulVec_mulVec,
    sub_smul_eq_fcalc hP τ, fcalc_mul]
  have e : (fun i => ((hP.eigenvalues i - τ : ℝ) : ℂ)) * (fun i => ((hP.eigenvalues i - τ : ℝ) : ℂ))
      = fun i => (((hP.eigenvalues i - τ) ^ 2 : ℝ) : ℂ) := by
    funext i; simp only [Pi.mul_apply]; push_cast; ring
  rw [e]
  exact re_dot_fcalc hP (fun i => (hP.eigenvalues i - τ) ^ 2) v

end Quad

/-! ### Faithfulness of the pencil polynomial off the spectrum -/

section PenPoly

variable {P : Matrix (Fin M) (Fin M) ℂ} (hP : P.IsHermitian)
include hP

theorem pencilRoots_eq_roots_det_gen (H : Matrix (Fin M) (Fin M) ℂ) {τ : ℝ} (hτ : τ ∉ spec hP) :
    pencilRoots P H τ
      = ((H.map Polynomial.C) - (Polynomial.X : ℂ[X])
          • ((P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ)).map Polynomial.C)).det.roots := by
  set Q := P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ) with hQ_def
  have hQ : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_det_sub hP hτ)
  have key : (H.map Polynomial.C) - (Polynomial.X : ℂ[X]) • (Q.map Polynomial.C)
      = ((-Q).map Polynomial.C) * Matrix.charmatrix (Q⁻¹ * H) := by
    have hm : (Q.map Polynomial.C) * ((Q⁻¹ * H).map Polynomial.C) = H.map Polynomial.C := by
      rw [← Matrix.map_mul, ← Matrix.mul_assoc, hQ, Matrix.one_mul]
    have hneg : (-Q).map Polynomial.C = -(Q.map Polynomial.C) := by
      ext i j; simp
    rw [Matrix.charmatrix, hneg, Matrix.neg_mul, Matrix.mul_sub, RingHom.mapMatrix_apply, hm,
      Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]
    abel
  have hdet : (-Q).det ≠ 0 := by
    rw [Matrix.det_neg]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (isUnit_det_sub hP hτ).ne_zero
  have hC : ((-Q).map Polynomial.C).det = Polynomial.C (-Q).det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
  rw [key, Matrix.det_mul, hC, Polynomial.roots_C_mul _ hdet]
  rfl

lemma roots_penPoly_gen (A : Matrix (Fin M) (Fin M) ℂ) {τ : ℝ} (hτ : τ ∉ spec hP) (c : ℂ) :
    (penPoly P A τ c).roots = Rt P A τ c := by
  rw [OQP27.StripL3b.penPoly_eq_det_form, ← pencilRoots_eq_roots_det_gen hP _ hτ]
  rfl

lemma det_pencil_gen (H : Matrix (Fin M) (Fin M) ℂ) {τ : ℝ} (hτ : τ ∉ spec hP) (y : ℂ) :
    (H - y • (P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ))).det
      = (-(P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ))).det
        * (((P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ))⁻¹ * H).charpoly).eval y := by
  set Q := P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ) with hQ_def
  have hQ : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_det_sub hP hτ)
  have e : H - y • Q = -Q * (Matrix.scalar (Fin M) y - Q⁻¹ * H) := by
    rw [Matrix.neg_mul, Matrix.mul_sub, ← Matrix.mul_assoc, hQ, Matrix.one_mul,
      Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]
    abel
  rw [e, Matrix.det_mul, Matrix.eval_charpoly]

lemma penPoly_eq_C_mul_charpoly_gen (A : Matrix (Fin M) (Fin M) ℂ) {τ : ℝ} (hτ : τ ∉ spec hP)
    (c : ℂ) :
    penPoly P A τ c = Polynomial.C (-(P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ))).det
      * ((P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ))⁻¹ * (A + c • 1)).charpoly := by
  apply Polynomial.funext
  intro z
  rw [OQP27.StripL3b.eval_penPoly, Polynomial.eval_mul, Polynomial.eval_C]
  exact det_pencil_gen hP (A + c • 1) hτ z

lemma det_neg_sub_ne_zero {τ : ℝ} (hτ : τ ∉ spec hP) :
    (-(P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ))).det ≠ 0 := by
  rw [Matrix.det_neg]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (isUnit_det_sub hP hτ).ne_zero

lemma penPoly_ne_zero_gen (A : Matrix (Fin M) (Fin M) ℂ) {τ : ℝ} (hτ : τ ∉ spec hP) (c : ℂ) :
    penPoly P A τ c ≠ 0 := by
  rw [penPoly_eq_C_mul_charpoly_gen hP A hτ c]
  exact mul_ne_zero (Polynomial.C_ne_zero.mpr (det_neg_sub_ne_zero hP hτ))
    (Matrix.charpoly_monic _).ne_zero

lemma penPoly_leadingCoeff_gen (A : Matrix (Fin M) (Fin M) ℂ) {τ : ℝ} (hτ : τ ∉ spec hP)
    (c : ℂ) :
    (penPoly P A τ c).leadingCoeff = (-(P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ))).det := by
  rw [penPoly_eq_C_mul_charpoly_gen hP A hτ c, Polynomial.leadingCoeff_C_mul_of_isUnit
    (isUnit_iff_ne_zero.mpr (det_neg_sub_ne_zero hP hτ)), (Matrix.charpoly_monic _).leadingCoeff,
    mul_one]

lemma penPoly_natDegree_gen (A : Matrix (Fin M) (Fin M) ℂ) {τ : ℝ} (hτ : τ ∉ spec hP) (c : ℂ) :
    (penPoly P A τ c).natDegree = M := by
  rw [penPoly_eq_C_mul_charpoly_gen hP A hτ c,
    Polynomial.natDegree_C_mul (det_neg_sub_ne_zero hP hτ),
    Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]

end PenPoly

/-! ### Lemma A: location of the roots -/

section Location

variable {P A : Matrix (Fin M) (Fin M) ℂ} (hP : P.IsHermitian) (hA : A.IsHermitian)
include hP hA

/-- `Im c |v|² = Im y ⟨v, (P - τ) v⟩` for a root `y` with eigenvector `v`. -/
lemma root_im_identity_gen (τ : ℝ) (c : ℂ) {y : ℂ} {v : Fin M → ℂ}
    (hv : (A + c • 1) *ᵥ v = y • ((P - (τ : ℂ) • 1) *ᵥ v)) :
    c.im * (star v ⬝ᵥ v).re = y.im * (star v ⬝ᵥ ((P - (τ : ℂ) • 1) *ᵥ v)).re := by
  have hQim : (star v ⬝ᵥ ((P - (τ : ℂ) • 1) *ᵥ v)).im = 0 := by
    simpa using (OQP27.StripL3b.isHermitian_P_sub hP τ).im_star_dotProduct_mulVec_self v
  have hAim : (star v ⬝ᵥ (A *ᵥ v)).im = 0 := by
    simpa using hA.im_star_dotProduct_mulVec_self v
  have hvv : (star v ⬝ᵥ v).im = 0 := by
    simpa using (isHermitian_one (n := Fin M) (α := ℂ)).im_star_dotProduct_mulVec_self v
  have hlhs : star v ⬝ᵥ ((A + c • 1) *ᵥ v) = star v ⬝ᵥ (A *ᵥ v) + c * (star v ⬝ᵥ v) := by
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_add, dotProduct_smul,
      smul_eq_mul]
  have hrhs : star v ⬝ᵥ (y • ((P - (τ : ℂ) • 1) *ᵥ v))
      = y * (star v ⬝ᵥ ((P - (τ : ℂ) • 1) *ᵥ v)) := by
    rw [dotProduct_smul, smul_eq_mul]
  have heq := congrArg Complex.im (hlhs.symm.trans ((congrArg (star v ⬝ᵥ ·) hv).trans hrhs))
  simp only [Complex.add_im, Complex.mul_im, hAim, hvv, hQim, mul_zero, zero_add] at heq
  linarith

/-- **Lemma A** (general `P`).  For `τ ∉ spec P` and `Im c > 0` no root is real; roots in `ℂ₊`
satisfy `Im c ≤ (U - τ) Im y`, roots in `ℂ₋` satisfy `Im c ≤ (L - τ) Im y`. -/
lemma pencilRoot_im_bounds_gen {L U : ℝ} (hL : ∀ i, L ≤ hP.eigenvalues i)
    (hU : ∀ i, hP.eigenvalues i ≤ U) {τ : ℝ} (hτ : τ ∉ spec hP) {c : ℂ} (hc : 0 < c.im) {y : ℂ}
    (hy : y ∈ Rt P A τ c) :
    y.im ≠ 0 ∧ (0 < y.im → c.im ≤ (U - τ) * y.im) ∧ (y.im < 0 → c.im ≤ (L - τ) * y.im) := by
  obtain ⟨v, hv0, hv⟩ := exists_pencil_eigvec_gen hP hτ hy
  have hkey := root_im_identity_gen hP hA τ c hv
  set w := star (eU hP) *ᵥ v
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

omit hA in
/-- **Lemma B(i)** (general `P`).  If `d ≤ |λ_i - τ|` for all `i`, every root satisfies
`|y|² d² ≤ ‖A + c‖_F²`. -/
lemma pencilRoot_norm_bound_dist {τ : ℝ} (hτ : τ ∉ spec hP) {d : ℝ}
    (hd : ∀ i, d ≤ |hP.eigenvalues i - τ|) (hd0 : 0 ≤ d) (c : ℂ) {y : ℂ} (hy : y ∈ Rt P A τ c) :
    ‖y‖ ^ 2 * d ^ 2 ≤ frob (A + c • 1) := by
  obtain ⟨v, hv0, hv⟩ := exists_pencil_eigvec_gen hP hτ hy
  have hnpos := OQP27.StripL3b.re_star_dotProduct_self_pos hv0
  have hn := re_dot_self_eq_sum hP v
  have hq := re_norm_sub_sq_eq_sum hP τ v
  set n := (star v ⬝ᵥ v).re
  have hlow : d ^ 2 * n
      ≤ (star ((P - (τ : ℂ) • 1) *ᵥ v) ⬝ᵥ ((P - (τ : ℂ) • 1) *ᵥ v)).re := by
    rw [hq, hn, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right ?_ (by positivity)
    have h1 := hd i
    have h2 : d ^ 2 ≤ |hP.eigenvalues i - τ| ^ 2 := pow_le_pow_left₀ hd0 h1 2
    rwa [sq_abs] at h2
  have hAv : star ((A + c • 1) *ᵥ v) ⬝ᵥ ((A + c • 1) *ᵥ v)
      = ((‖y‖ : ℂ) ^ 2) * (star ((P - (τ : ℂ) • 1) *ᵥ v) ⬝ᵥ ((P - (τ : ℂ) • 1) *ᵥ v)) := by
    rw [hv, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
      Complex.star_def, Complex.conj_mul']
  have hle := OQP27.StripL3b.re_dot_mulVec_le_frob (A + c • 1) v
  rw [hAv] at hle
  have hre : (((‖y‖ : ℂ) ^ 2) * (star ((P - (τ : ℂ) • 1) *ᵥ v) ⬝ᵥ ((P - (τ : ℂ) • 1) *ᵥ v))).re
      = ‖y‖ ^ 2 * (star ((P - (τ : ℂ) • 1) *ᵥ v) ⬝ᵥ ((P - (τ : ℂ) • 1) *ᵥ v)).re := by
    have e : ((‖y‖ : ℂ) ^ 2) = ((‖y‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.re_ofReal_mul]
  rw [hre] at hle
  have h3 : ‖y‖ ^ 2 * (d ^ 2 * n) ≤ frob (A + c • 1) * n :=
    le_trans (mul_le_mul_of_nonneg_left hlow (by positivity)) hle
  have h4 : ‖y‖ ^ 2 * d ^ 2 * n ≤ frob (A + c • 1) * n := by linarith
  exact le_of_mul_le_mul_right h4 hnpos

/-- **Lemma B(ii)** (general `P`, on a gap).  For `α < τ < β` with no eigenvalue strictly between `α`
and `β`, a root in `ℂ₊` with `τ ≤ (α + β)/2`, or a root in `ℂ₋` with `τ ≥ (α + β)/2`, satisfies
`|y|² (τ - α)(β - τ) ≤ ‖A + c‖_F²`. -/
lemma pencilRoot_norm_bound_gap {α β τ : ℝ} (hατ : α < τ) (hτβ : τ < β)
    (hgap : ∀ p ∈ spec hP, p ≤ α ∨ β ≤ p) (hτ : τ ∉ spec hP) {c : ℂ} (hc : 0 < c.im) {y : ℂ}
    (hy : y ∈ Rt P A τ c)
    (hside : (0 < y.im ∧ τ ≤ (α + β) / 2) ∨ (y.im < 0 ∧ (α + β) / 2 ≤ τ)) :
    ‖y‖ ^ 2 * ((τ - α) * (β - τ)) ≤ frob (A + c • 1) := by
  obtain ⟨v, hv0, hv⟩ := exists_pencil_eigvec_gen hP hτ hy
  have hkey := root_im_identity_gen hP hA τ c hv
  have hnpos := OQP27.StripL3b.re_star_dotProduct_self_pos hv0
  have hn := re_dot_self_eq_sum hP v
  have ha := re_dot_sub_eq_sum hP τ v
  have hq := re_norm_sub_sq_eq_sum hP τ v
  set n := (star v ⬝ᵥ v).re
  set a := (star v ⬝ᵥ ((P - (τ : ℂ) • 1) *ᵥ v)).re
  have hcn : 0 < c.im * n := mul_pos hc hnpos
  -- `(α + β - 2τ) a ≥ 0`
  have hsign : 0 ≤ (α + β - 2 * τ) * a := by
    rcases hside with ⟨hy0, hτm⟩ | ⟨hy0, hτm⟩
    · have ha0 : 0 < a := by
        by_contra h
        push Not at h
        nlinarith
      nlinarith
    · have ha0 : a < 0 := by
        by_contra h
        push Not at h
        nlinarith
      nlinarith
  -- `|(P - τ) v|² ≥ (α + β - 2τ) a + (τ - α)(β - τ) n`
  have hlow : (α + β - 2 * τ) * a + (τ - α) * (β - τ) * n
      ≤ (star ((P - (τ : ℂ) • 1) *ᵥ v) ⬝ᵥ ((P - (τ : ℂ) • 1) *ᵥ v)).re := by
    rw [hq, ha, hn, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    have hpos : 0 ≤ (hP.eigenvalues i - α) * (hP.eigenvalues i - β) := by
      rcases hgap _ (eigenvalues_mem_spec hP i) with h | h
      · exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
      · exact mul_nonneg (by linarith) (by linarith)
    have hw : 0 ≤ ‖(star (eU hP) *ᵥ v) i‖ ^ 2 := by positivity
    nlinarith
  have hAv : star ((A + c • 1) *ᵥ v) ⬝ᵥ ((A + c • 1) *ᵥ v)
      = ((‖y‖ : ℂ) ^ 2) * (star ((P - (τ : ℂ) • 1) *ᵥ v) ⬝ᵥ ((P - (τ : ℂ) • 1) *ᵥ v)) := by
    rw [hv, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
      Complex.star_def, Complex.conj_mul']
  have hle := OQP27.StripL3b.re_dot_mulVec_le_frob (A + c • 1) v
  rw [hAv] at hle
  have hre : (((‖y‖ : ℂ) ^ 2) * (star ((P - (τ : ℂ) • 1) *ᵥ v) ⬝ᵥ ((P - (τ : ℂ) • 1) *ᵥ v))).re
      = ‖y‖ ^ 2 * (star ((P - (τ : ℂ) • 1) *ᵥ v) ⬝ᵥ ((P - (τ : ℂ) • 1) *ᵥ v)).re := by
    have e : ((‖y‖ : ℂ) ^ 2) = ((‖y‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.re_ofReal_mul]
  rw [hre] at hle
  have hlow' : (τ - α) * (β - τ) * n
      ≤ (star ((P - (τ : ℂ) • 1) *ᵥ v) ⬝ᵥ ((P - (τ : ℂ) • 1) *ᵥ v)).re := by linarith
  have h3 : ‖y‖ ^ 2 * ((τ - α) * (β - τ) * n) ≤ frob (A + c • 1) * n :=
    le_trans (mul_le_mul_of_nonneg_left hlow' (by positivity)) hle
  have h4 : ‖y‖ ^ 2 * ((τ - α) * (β - τ)) * n ≤ frob (A + c • 1) * n := by linarith
  exact le_of_mul_le_mul_right h4 hnpos

end Location

/-! ### Root sums -/

section Sums

variable {P A : Matrix (Fin M) (Fin M) ℂ} (hP : P.IsHermitian) (hA : A.IsHermitian)
include hP

lemma pinchH_add_smul_one (A : Matrix (Fin M) (Fin M) ℂ) (c : ℂ) :
    pinchH hP (A + c • 1) = pinchH hP A + c • 1 := by
  rw [pinchH_add, pinchH_smul, pinchH_one]

/-- The trace identity: the pencils of `A + c` and `A_d + c` have the same root sum. -/
lemma sum_Rt_pinchH (A : Matrix (Fin M) (Fin M) ℂ) {τ : ℝ} (hτ : τ ∉ spec hP) (c : ℂ) :
    (Rt P (pinchH hP A) τ c).sum = (Rt P A τ c).sum := by
  unfold Rt pencilRoots
  rw [← Matrix.trace_eq_sum_roots_charpoly, ← Matrix.trace_eq_sum_roots_charpoly,
    ← pinchH_add_smul_one hP A c]
  exact trace_inv_mul_pinchH hP _ hτ

include hA

lemma Rt_im_ne_zero_gen {L U : ℝ} (hL : ∀ i, L ≤ hP.eigenvalues i)
    (hU : ∀ i, hP.eigenvalues i ≤ U) {τ : ℝ} (hτ : τ ∉ spec hP) {c : ℂ} (hc : 0 < c.im) :
    ∀ y ∈ Rt P A τ c, y.im ≠ 0 :=
  fun _ hy => (pencilRoot_im_bounds_gen hP hA hL hU hτ hc hy).1

lemma Sup_add_Slo_gen {L U : ℝ} (hL : ∀ i, L ≤ hP.eigenvalues i) (hU : ∀ i, hP.eigenvalues i ≤ U)
    {τ : ℝ} (hτ : τ ∉ spec hP) {c : ℂ} (hc : 0 < c.im) :
    Sup P A τ c + Slo P A τ c = (Rt P A τ c).sum := by
  unfold Sup Slo
  rw [← Multiset.sum_add, OQP27.StripL3b.upper_add_lower (Rt_im_ne_zero_gen hP hA hL hU hτ hc)]

/-- `S_+(A) - S_+(A_d) = S_-(A_d) - S_-(A)`. -/
lemma Sup_sub_eq_gen {L U : ℝ} (hL : ∀ i, L ≤ hP.eigenvalues i) (hU : ∀ i, hP.eigenvalues i ≤ U)
    {τ : ℝ} (hτ : τ ∉ spec hP) {c : ℂ} (hc : 0 < c.im) :
    Sup P A τ c - Sup P (pinchH hP A) τ c = Slo P (pinchH hP A) τ c - Slo P A τ c := by
  have h1' := Sup_add_Slo_gen hP hA hL hU hτ hc
  have h2' := Sup_add_Slo_gen hP (isHermitian_pinchH hP hA) hL hU hτ hc
  have h3 := sum_Rt_pinchH hP A hτ c
  rw [← h1', ← h2'] at h3
  linear_combination -h3

/-- Left of the spectrum all roots are in `ℂ₊`, so `S_+(A) = S_+(A_d)`. -/
lemma Sup_sub_eq_zero_of_lt {L U : ℝ} (hL : ∀ i, L ≤ hP.eigenvalues i)
    (hU : ∀ i, hP.eigenvalues i ≤ U) {τ : ℝ} (hτL : τ < L) {c : ℂ} (hc : 0 < c.im) :
    Sup P A τ c - Sup P (pinchH hP A) τ c = 0 := by
  have hτ : τ ∉ spec hP := by
    intro h
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp h
    linarith [hL i]
  have hlow : ∀ B : Matrix (Fin M) (Fin M) ℂ, B.IsHermitian → Slo P B τ c = 0 := by
    intro B hB
    unfold Slo
    have : lowerRoots (Rt P B τ c) = 0 := by
      unfold lowerRoots
      rw [Multiset.filter_eq_nil]
      intro y hy hneg
      have h := (pencilRoot_im_bounds_gen hP hB hL hU hτ hc hy).2.2 hneg
      nlinarith
    rw [this, Multiset.sum_zero]
  rw [Sup_sub_eq_gen hP hA hL hU hτ hc, hlow _ (isHermitian_pinchH hP hA), hlow A hA, sub_zero]

/-- Right of the spectrum no root is in `ℂ₊`, so `S_+(A) = S_+(A_d) = 0`. -/
lemma Sup_sub_eq_zero_of_gt {L U : ℝ} (hL : ∀ i, L ≤ hP.eigenvalues i)
    (hU : ∀ i, hP.eigenvalues i ≤ U) {τ : ℝ} (hτU : U < τ) {c : ℂ} (hc : 0 < c.im) :
    Sup P A τ c - Sup P (pinchH hP A) τ c = 0 := by
  have hτ : τ ∉ spec hP := by
    intro h
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp h
    linarith [hU i]
  have hup : ∀ B : Matrix (Fin M) (Fin M) ℂ, B.IsHermitian → Sup P B τ c = 0 := by
    intro B hB
    unfold Sup
    have : upperRoots (Rt P B τ c) = 0 := by
      unfold upperRoots
      rw [Multiset.filter_eq_nil]
      intro y hy hpos
      have h := (pencilRoot_im_bounds_gen hP hB hL hU hτ hc hy).2.1 hpos
      nlinarith
    rw [this, Multiset.sum_zero]
  rw [hup A hA, hup _ (isHermitian_pinchH hP hA), sub_zero]

omit hP hA in
lemma norm_le_of_sq_bound_gap {y : ℂ} {K x : ℝ} (hx : 0 < x) (h : ‖y‖ ^ 2 * x ≤ K) :
    ‖y‖ ≤ √K / √x := by
  rw [le_div_iff₀ (Real.sqrt_pos.mpr hx), ← Real.sqrt_sq (norm_nonneg y),
    ← Real.sqrt_mul (sq_nonneg _)]
  exact Real.sqrt_le_sqrt h

omit hP hA in
lemma card_upperRoots_le (B : Matrix (Fin M) (Fin M) ℂ) (τ : ℝ) (c : ℂ) :
    ((upperRoots (Rt P B τ c)).card : ℝ) ≤ M := by
  have := OQP27.StripL3b.card_filter_le (Rt P B τ c) (fun z => 0 < z.im)
  unfold Rt at this ⊢
  rw [OQP27.StripL3b.card_pencilRoots] at this
  exact_mod_cast this

omit hP hA in
lemma card_lowerRoots_le (B : Matrix (Fin M) (Fin M) ℂ) (τ : ℝ) (c : ℂ) :
    ((lowerRoots (Rt P B τ c)).card : ℝ) ≤ M := by
  have := OQP27.StripL3b.card_filter_le (Rt P B τ c) (fun z => z.im < 0)
  unfold Rt at this ⊢
  rw [OQP27.StripL3b.card_pencilRoots] at this
  exact_mod_cast this

/-- **Lemma B(iii)** on a gap: with `K ≥ ‖A + c‖_F², ‖A_d + c‖_F²`,
`|S_+(A) - S_+(A_d)| ≤ 2 M √K / √((τ - α)(β - τ))`. -/
theorem norm_Sup_sub_le_gap {α β τ : ℝ} (hατ : α < τ) (hτβ : τ < β)
    (hgap : ∀ p ∈ spec hP, p ≤ α ∨ β ≤ p) (hτ : τ ∉ spec hP) {L U : ℝ}
    (hL : ∀ i, L ≤ hP.eigenvalues i) (hU : ∀ i, hP.eigenvalues i ≤ U) {c : ℂ} (hc : 0 < c.im)
    {K : ℝ} (hK1 : frob (A + c • 1) ≤ K) (hK2 : frob (pinchH hP A + c • 1) ≤ K) :
    ‖Sup P A τ c - Sup P (pinchH hP A) τ c‖ ≤ 2 * M * (√K / √((τ - α) * (β - τ))) := by
  have hAd := isHermitian_pinchH hP hA
  have hx : 0 < (τ - α) * (β - τ) := mul_pos (by linarith) (by linarith)
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hbd : ∀ B : Matrix (Fin M) (Fin M) ℂ, B.IsHermitian → frob (B + c • 1) ≤ K →
      (τ ≤ (α + β) / 2 → ‖Sup P B τ c‖ ≤ M * (√K / √((τ - α) * (β - τ)))) ∧
      ((α + β) / 2 ≤ τ → ‖Slo P B τ c‖ ≤ M * (√K / √((τ - α) * (β - τ)))) := by
    intro B hB hKB
    constructor
    · intro hτm
      unfold Sup
      have hb : ∀ y ∈ upperRoots (Rt P B τ c), ‖y‖ ≤ √K / √((τ - α) * (β - τ)) := by
        intro y hy
        have hy' : y ∈ Rt P B τ c := Multiset.mem_of_mem_filter hy
        have hpos : 0 < y.im := (Multiset.mem_filter.mp hy).2
        exact norm_le_of_sq_bound_gap hx
          ((pencilRoot_norm_bound_gap hP hB hατ hτβ hgap hτ hc hy' (Or.inl ⟨hpos, hτm⟩)).trans hKB)
      refine (OQP27.StripL3b.norm_multiset_sum_le_card_mul hb).trans ?_
      exact mul_le_mul_of_nonneg_right (card_upperRoots_le (P := P) B τ c) (by positivity)
    · intro hτm
      unfold Slo
      have hb : ∀ y ∈ lowerRoots (Rt P B τ c), ‖y‖ ≤ √K / √((τ - α) * (β - τ)) := by
        intro y hy
        have hy' : y ∈ Rt P B τ c := Multiset.mem_of_mem_filter hy
        have hneg : y.im < 0 := (Multiset.mem_filter.mp hy).2
        exact norm_le_of_sq_bound_gap hx
          ((pencilRoot_norm_bound_gap hP hB hατ hτβ hgap hτ hc hy' (Or.inr ⟨hneg, hτm⟩)).trans hKB)
      refine (OQP27.StripL3b.norm_multiset_sum_le_card_mul hb).trans ?_
      exact mul_le_mul_of_nonneg_right (card_lowerRoots_le (P := P) B τ c) (by positivity)
  rcases le_or_gt τ ((α + β) / 2) with hτm | hτm
  · calc ‖Sup P A τ c - Sup P (pinchH hP A) τ c‖
        ≤ ‖Sup P A τ c‖ + ‖Sup P (pinchH hP A) τ c‖ := norm_sub_le _ _
      _ ≤ M * (√K / √((τ - α) * (β - τ))) + M * (√K / √((τ - α) * (β - τ))) :=
          add_le_add ((hbd A hA hK1).1 hτm) ((hbd _ hAd hK2).1 hτm)
      _ = 2 * M * (√K / √((τ - α) * (β - τ))) := by ring
  · rw [Sup_sub_eq_gen hP hA hL hU hτ hc]
    calc ‖Slo P (pinchH hP A) τ c - Slo P A τ c‖
        ≤ ‖Slo P (pinchH hP A) τ c‖ + ‖Slo P A τ c‖ := norm_sub_le _ _
      _ ≤ M * (√K / √((τ - α) * (β - τ))) + M * (√K / √((τ - α) * (β - τ))) :=
          add_le_add ((hbd _ hAd hK2).2 hτm.le) ((hbd A hA hK1).2 hτm.le)
      _ = 2 * M * (√K / √((τ - α) * (β - τ))) := by ring

end Sums

end HarmonicMajorization
