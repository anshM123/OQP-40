import HarmonicMajorization.SpecDecomp
import OQP27.StripBMV
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-!
# The pencil `det(H - y(P - τ))` for a Hermitian `P` (THEOREMS.md, Lemma 2.2)

Authors: Ansh Mishra, Aryan Senthilkumar.  License: MIT.

`P` Hermitian with distinct eigenvalues `spec hP`; the pencil roots at `τ` are
`OQP27.StripL3b.pencilRoots P H τ`, the eigenvalues of `(P - τ)⁻¹ H` (for `τ ∉ spec P` the roots of
`y ↦ det(H - y(P - τ))`; for `τ ∈ spec P` Lean's inverse is `0` and all roots are `0`).

Main results:
* `imAbsSum_pencilRoots_of_mem_spec`: no contribution on the lines `τ ∈ spec P`;
* `imAbsSum_pencilRoots_add_smul`: invariance under `H ↦ H + ξ(P - τ)`;
* `imAbsSum_pencilRoots_eq_zero_of_posSemidef` (Lemma 2.2(3), `g - s` semidefinite) and
  `imAbsSum_pencilRoots_eq_zero_of_definite` (Lemma 2.2(3), `P - τ` definite);
* `normSq_nonreal_root_le_gap`, `imAbsSum_pencilRoots_le_gap` (**Lemma 2.2(6)**): on a gap
  `α < τ < β` of the spectrum, every non-real root satisfies `|y|² (τ - α)(β - τ) ≤ ‖H‖_F²`;
* the density `rhoG P g s τ = (1/2π) Σ_i |Im x_i(s,τ)|`, its measurability (`measurable_rhoG`), its
  support (`rhoG_eq_zero_of_semidef`, `rhoG_eq_zero_of_not_mem_Ioo`) and the integrable bound
  `rhoG_le_domG` with `domG` integrable (`integrable_domG`).

No hypotheses.
-/

set_option autoImplicit false

namespace HarmonicMajorization

open Matrix Complex MeasureTheory Filter Topology Set
open scoped Real ComplexOrder
open OQP27.StripL3b (pencilRoots imAbsSum frob)

variable {M : ℕ}

/-! ### Determinant of the functional calculus -/

section Det

variable {P : Matrix (Fin M) (Fin M) ℂ} (hP : P.IsHermitian)

lemma det_fcalc (f : Fin M → ℂ) : (fcalc hP f).det = ∏ i, f i := by
  unfold fcalc
  rw [Matrix.det_mul, Matrix.det_mul, det_diagonal, mul_comm ((eU hP).det), mul_assoc,
    ← Matrix.det_mul, eU_mul_star, Matrix.det_one, mul_one]

lemma det_sub_smul (τ : ℝ) :
    (P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ)).det = ∏ i, ((hP.eigenvalues i - τ : ℝ) : ℂ) := by
  rw [sub_smul_eq_fcalc hP τ, det_fcalc]

lemma det_sub_smul_eq_zero {τ : ℝ} (hτ : τ ∈ spec hP) :
    (P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ)).det = 0 := by
  rw [det_sub_smul hP τ]
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hτ
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hi, sub_self, Complex.ofReal_zero])

end Det

/-! ### Pencil roots -/

section Roots

variable {P : Matrix (Fin M) (Fin M) ℂ} (hP : P.IsHermitian)
include hP

/-- On the lines `τ ∈ spec P` all pencil roots are `0`. -/
lemma imAbsSum_pencilRoots_of_mem_spec {τ : ℝ} (hτ : τ ∈ spec hP)
    (H : Matrix (Fin M) (Fin M) ℂ) : imAbsSum (pencilRoots P H τ) = 0 := by
  have hinv : (P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ))⁻¹ = 0 := by
    apply Matrix.nonsing_inv_apply_not_isUnit
    rw [isUnit_iff_ne_zero, not_not]
    exact det_sub_smul_eq_zero hP hτ
  unfold pencilRoots imAbsSum
  rw [hinv, Matrix.zero_mul, Matrix.charpoly_zero, Fintype.card_fin]
  apply Multiset.sum_eq_zero
  intro x hx
  obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hx
  have hX : ((Polynomial.X : Polynomial ℂ) ^ M) ≠ 0 := pow_ne_zero _ Polynomial.X_ne_zero
  have h1 := (Polynomial.mem_roots hX).mp hz
  rw [Polynomial.IsRoot.def, Polynomial.eval_pow, Polynomial.eval_X] at h1
  rw [eq_zero_of_pow_eq_zero h1, Complex.zero_im, abs_zero]

/-- Every pencil root comes with an eigenvector, for `τ ∉ spec P`. -/
lemma exists_pencil_eigvec_gen {H : Matrix (Fin M) (Fin M) ℂ} {τ : ℝ} (hτ : τ ∉ spec hP) {x : ℂ}
    (hx : x ∈ pencilRoots P H τ) :
    ∃ v : Fin M → ℂ, v ≠ 0 ∧ H *ᵥ v = x • ((P - (τ : ℂ) • 1) *ᵥ v) := by
  unfold pencilRoots at hx
  set Q := P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ) with hQ
  have hmon := Matrix.charpoly_monic (Q⁻¹ * H)
  have hroot : (Q⁻¹ * H).charpoly.IsRoot x := (Polynomial.mem_roots hmon.ne_zero).mp hx
  rw [Polynomial.IsRoot.def, Matrix.eval_charpoly] at hroot
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hroot
  refine ⟨v, hv0, ?_⟩
  have h2 : (Q⁻¹ * H) *ᵥ v = x • v := by
    rw [Matrix.sub_mulVec, sub_eq_zero] at hv
    rw [← hv, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mulVec,
      Matrix.one_mulVec]
  have hQinv : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_det_sub hP hτ)
  calc H *ᵥ v = (Q * (Q⁻¹ * H)) *ᵥ v := by rw [← Matrix.mul_assoc, hQinv, Matrix.one_mul]
    _ = Q *ᵥ ((Q⁻¹ * H) *ᵥ v) := (Matrix.mulVec_mulVec _ _ _).symm
    _ = Q *ᵥ (x • v) := by rw [h2]
    _ = x • (Q *ᵥ v) := Matrix.mulVec_smul _ _ _

/-- Adding `ξ(P - τ)` to `H` does not change `Σ |Im y_i|`. -/
lemma imAbsSum_pencilRoots_add_smul (H : Matrix (Fin M) (Fin M) ℂ) (ξ τ : ℝ) :
    imAbsSum (pencilRoots P (H + (ξ : ℂ) • (P - (τ : ℂ) • 1)) τ)
      = imAbsSum (pencilRoots P H τ) := by
  by_cases hτ : τ ∈ spec hP
  · rw [imAbsSum_pencilRoots_of_mem_spec hP hτ, imAbsSum_pencilRoots_of_mem_spec hP hτ]
  · unfold pencilRoots
    rw [Matrix.mul_add, Matrix.mul_smul, inv_sub_mul_self hP hτ]
    have h2 : (P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ))⁻¹ * H + (ξ : ℂ) • 1
        = (P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ))⁻¹ * H
          - Matrix.scalar (Fin M) (-(ξ : ℂ)) := by
      rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, neg_smul, sub_neg_eq_add]
    rw [h2, Matrix.charpoly_sub_scalar]
    have h3 : (Polynomial.X + Polynomial.C (-(ξ : ℂ)) : Polynomial ℂ)
        = Polynomial.C 1 * Polynomial.X + Polynomial.C (-(ξ : ℂ)) := by simp
    rw [h3, Polynomial.roots_comp_C_mul_X_add_C _ 1 (-(ξ : ℂ)) isUnit_one]
    have e : (fun x : ℂ => Ring.inverse (1 : ℂ) * (x - -(ξ : ℂ))) = fun x => x + (ξ : ℂ) := by
      funext x; simp
    rw [e]
    exact OQP27.StripL3b.imAbsSum_map_add_ofReal _ ξ

/-- **Lemma 2.2(3)** (`H` semidefinite): all pencil roots are real. -/
lemma imAbsSum_pencilRoots_eq_zero_of_posSemidef {H : Matrix (Fin M) (Fin M) ℂ}
    (hH : H.PosSemidef ∨ (-H).PosSemidef) (τ : ℝ) : imAbsSum (pencilRoots P H τ) = 0 := by
  by_cases hτ : τ ∈ spec hP
  · exact imAbsSum_pencilRoots_of_mem_spec hP hτ H
  have hHerm : H.IsHermitian := by
    rcases hH with h | h
    · exact h.isHermitian
    · simpa using h.isHermitian.neg
  have hreal : ∀ x ∈ pencilRoots P H τ, x.im = 0 := by
    intro x hx
    by_contra hxim
    obtain ⟨v, hv0, hv⟩ := exists_pencil_eigvec_gen hP hτ hx
    have horth := (OQP27.StripL3b.nonreal_root_orth hP hHerm τ hv hxim).2
    have hHv : H *ᵥ v = 0 := by
      rcases hH with h | h
      · exact (h.dotProduct_mulVec_zero_iff v).mp horth
      · have : star v ⬝ᵥ ((-H) *ᵥ v) = 0 := by
          rw [Matrix.neg_mulVec, dotProduct_neg, horth, neg_zero]
        have h2 := (h.dotProduct_mulVec_zero_iff v).mp this
        rw [Matrix.neg_mulVec, neg_eq_zero] at h2
        exact h2
    rw [hHv] at hv
    have hx0 : x ≠ 0 := fun h => hxim (by rw [h, Complex.zero_im])
    have hQv : (P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ)) *ᵥ v = 0 :=
      (smul_eq_zero.mp hv.symm).resolve_left hx0
    apply hv0
    calc v = ((P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ))⁻¹ * (P - (τ : ℂ) • 1)) *ᵥ v := by
          rw [inv_sub_mul_self hP hτ, Matrix.one_mulVec]
      _ = 0 := by rw [← Matrix.mulVec_mulVec, hQv, Matrix.mulVec_zero]
  unfold imAbsSum
  rw [Multiset.map_congr rfl (fun z hz => by rw [hreal z hz, abs_zero])]
  simp

/-- `Re ⟨v, φ(f) v⟩ = Σ_i f_i |(U* v)_i|²` for real `f`. -/
lemma re_dot_fcalc (f : Fin M → ℝ) (v : Fin M → ℂ) :
    (star v ⬝ᵥ (fcalc hP (fun i => (f i : ℂ)) *ᵥ v)).re
      = ∑ i, f i * ‖(star (eU hP) *ᵥ v) i‖ ^ 2 := by
  set w := star (eU hP) *ᵥ v with hw
  have h1 : fcalc hP (fun i => (f i : ℂ)) *ᵥ v
      = eU hP *ᵥ (diagonal (fun i => (f i : ℂ)) *ᵥ w) := by
    unfold fcalc
    rw [hw, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have h2 : star v ᵥ* eU hP = star w := by
    rw [hw, Matrix.star_mulVec, Matrix.star_eq_conjTranspose, conjTranspose_conjTranspose]
  rw [h1, Matrix.dotProduct_mulVec, h2]
  simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show star (w i) * ((f i : ℂ) * w i) = (f i : ℂ) * (star (w i) * w i) by ring,
    Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul,
    Complex.ofReal_re]

/-- `Re ⟨v, φ(f) v⟩ ≥ 0` for `f ≥ 0`. -/
lemma re_dot_fcalc_nonneg {f : Fin M → ℝ} (hf : ∀ i, 0 ≤ f i) (v : Fin M → ℂ) :
    0 ≤ (star v ⬝ᵥ (fcalc hP (fun i => (f i : ℂ)) *ᵥ v)).re := by
  rw [re_dot_fcalc]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hf i) (by positivity)

lemma star_eU_mulVec_ne_zero {v : Fin M → ℂ} (hv : v ≠ 0) : star (eU hP) *ᵥ v ≠ 0 := by
  intro h
  apply hv
  calc v = (eU hP * star (eU hP)) *ᵥ v := by rw [eU_mul_star, Matrix.one_mulVec]
    _ = 0 := by rw [← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]

/-- `Re ⟨v, φ(f) v⟩ > 0` for `f > 0` and `v ≠ 0`. -/
lemma re_dot_fcalc_pos {f : Fin M → ℝ} (hf : ∀ i, 0 < f i) {v : Fin M → ℂ} (hv : v ≠ 0) :
    0 < (star v ⬝ᵥ (fcalc hP (fun i => (f i : ℂ)) *ᵥ v)).re := by
  rw [re_dot_fcalc]
  obtain ⟨j, hj⟩ := Function.ne_iff.mp (star_eU_mulVec_ne_zero hP hv)
  refine Finset.sum_pos' (fun i _ => mul_nonneg (hf i).le (by positivity))
    ⟨j, Finset.mem_univ j, mul_pos (hf j) ?_⟩
  have : ‖(star (eU hP) *ᵥ v) j‖ ≠ 0 := by simpa using hj
  positivity

/-- If `P - τ` is positive or negative definite (`τ` outside `[min spec, max spec]`), all pencil
roots are real (Lemma 2.2(3)). -/
lemma imAbsSum_pencilRoots_eq_zero_of_definite {H : Matrix (Fin M) (Fin M) ℂ} (hH : H.IsHermitian)
    {τ : ℝ} (hτ : (∀ p ∈ spec hP, τ < p) ∨ (∀ p ∈ spec hP, p < τ)) :
    imAbsSum (pencilRoots P H τ) = 0 := by
  have hτs : τ ∉ spec hP := by
    intro h
    rcases hτ with h' | h'
    · exact lt_irrefl _ (h' τ h)
    · exact lt_irrefl _ (h' τ h)
  have hreal : ∀ x ∈ pencilRoots P H τ, x.im = 0 := by
    intro x hx
    by_contra hxim
    obtain ⟨v, hv0, hv⟩ := exists_pencil_eigvec_gen hP hτs hx
    have horth := (OQP27.StripL3b.nonreal_root_orth hP hH τ hv hxim).1
    rw [sub_smul_eq_fcalc hP τ] at horth
    have h2 := congrArg Complex.re horth
    rw [Complex.zero_re] at h2
    rcases hτ with h' | h'
    · have hpos := re_dot_fcalc_pos hP (f := fun i => hP.eigenvalues i - τ)
        (fun i => by have := h' _ (eigenvalues_mem_spec hP i); linarith) hv0
      linarith
    · have hpos := re_dot_fcalc_pos hP (f := fun i => τ - hP.eigenvalues i)
        (fun i => by have := h' _ (eigenvalues_mem_spec hP i); linarith) hv0
      have hneg : fcalc hP (fun i => ((hP.eigenvalues i - τ : ℝ) : ℂ))
          = -fcalc hP (fun i => ((τ - hP.eigenvalues i : ℝ) : ℂ)) := by
        rw [show -fcalc hP (fun i => ((τ - hP.eigenvalues i : ℝ) : ℂ))
            = (-1 : ℂ) • fcalc hP (fun i => ((τ - hP.eigenvalues i : ℝ) : ℂ)) by
              rw [neg_one_smul], ← fcalc_smul]
        congr 1; funext i; simp
      rw [hneg, Matrix.neg_mulVec, dotProduct_neg, Complex.neg_re] at h2
      linarith
  unfold imAbsSum
  rw [Multiset.map_congr rfl (fun z hz => by rw [hreal z hz, abs_zero])]
  simp

/-! ### Lemma 2.2(6): the gap bound -/

/-- On a gap `α < τ < β` (no eigenvalue strictly between `α` and `β`), if `⟨v, (P - τ) v⟩ = 0`
then `|(P - τ) v|² ≥ (τ - α)(β - τ)|v|²`. -/
lemma gap_ineq {α β τ : ℝ} (hα : α < τ) (hβ : τ < β) (hgap : ∀ p ∈ spec hP, p ≤ α ∨ β ≤ p)
    (v : Fin M → ℂ)
    (hv : star v ⬝ᵥ ((P - (τ : ℂ) • 1) *ᵥ v) = 0) :
    (τ - α) * (β - τ) * (star v ⬝ᵥ v).re
      ≤ (star ((P - (τ : ℂ) • 1) *ᵥ v) ⬝ᵥ ((P - (τ : ℂ) • 1) *ᵥ v)).re := by
  set Q := P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ) with hQ
  have hQh : Q.IsHermitian := OQP27.StripL3b.isHermitian_P_sub hP τ
  -- `Q² = (P - α)(P - β) + (α + β - 2τ) Q + (τ - α)(β - τ)`
  have hsq : Q * Q = fcalc hP (fun i => (((hP.eigenvalues i - α) * (hP.eigenvalues i - β) : ℝ) : ℂ))
      + ((α + β - 2 * τ : ℝ) : ℂ) • Q + (((τ - α) * (β - τ) : ℝ) : ℂ) • 1 := by
    rw [hQ, sub_smul_eq_fcalc hP τ, fcalc_mul, ← fcalc_one hP, ← fcalc_smul, ← fcalc_smul,
      ← fcalc_add, ← fcalc_add]
    congr 1
    funext i
    simp only [Pi.mul_apply, Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
    push_cast
    ring
  have h1 := re_dot_fcalc_nonneg hP (f := fun i => (hP.eigenvalues i - α) * (hP.eigenvalues i - β))
    (fun i => by
      rcases hgap _ (eigenvalues_mem_spec hP i) with h | h
      · exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith [h])
      · exact mul_nonneg (by linarith) (by linarith)) v
  have hstar : star (Q *ᵥ v) ⬝ᵥ (Q *ᵥ v) = star v ⬝ᵥ ((Q * Q) *ᵥ v) := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hQh.eq, Matrix.mulVec_mulVec]
  rw [hstar, hsq, Matrix.add_mulVec, Matrix.add_mulVec, dotProduct_add, dotProduct_add,
    Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, dotProduct_smul,
    hv, smul_zero, add_zero, Complex.add_re, smul_eq_mul, Complex.re_ofReal_mul]
  linarith

/-- **Lemma 2.2(6).**  On a gap `α < τ < β`, every non-real root satisfies
`|y|² (τ - α)(β - τ) ≤ ‖H‖_F²`. -/
lemma normSq_nonreal_root_le_gap {H : Matrix (Fin M) (Fin M) ℂ} (hH : H.IsHermitian) {α β τ : ℝ}
    (hα : α < τ) (hβ : τ < β) (hτ : τ ∉ spec hP) (hgap : ∀ p ∈ spec hP, p ≤ α ∨ β ≤ p) {x : ℂ}
    (hx : x ∈ pencilRoots P H τ) (hxim : x.im ≠ 0) :
    ‖x‖ ^ 2 * ((τ - α) * (β - τ)) ≤ frob H := by
  obtain ⟨v, hv0, hv⟩ := exists_pencil_eigvec_gen hP hτ hx
  have horth := (OQP27.StripL3b.nonreal_root_orth hP hH τ hv hxim).1
  have hg := gap_ineq hP hα hβ hgap v horth
  have hHv : (star (H *ᵥ v) ⬝ᵥ (H *ᵥ v)).re
      = ‖x‖ ^ 2 * (star ((P - (τ : ℂ) • 1) *ᵥ v) ⬝ᵥ ((P - (τ : ℂ) • 1) *ᵥ v)).re := by
    rw [hv, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
      Complex.star_def, Complex.conj_mul']
    rw [show ((‖x‖ : ℂ) ^ 2) = ((‖x‖ ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul]
  have hle := OQP27.StripL3b.re_dot_mulVec_le_frob H v
  have hpos := OQP27.StripL3b.re_star_dotProduct_self_pos hv0
  rw [hHv] at hle
  have h2 : ‖x‖ ^ 2 * ((τ - α) * (β - τ) * (star v ⬝ᵥ v).re) ≤ frob H * (star v ⬝ᵥ v).re :=
    le_trans (mul_le_mul_of_nonneg_left hg (by positivity)) hle
  have h3 : ‖x‖ ^ 2 * ((τ - α) * (β - τ)) * (star v ⬝ᵥ v).re ≤ frob H * (star v ⬝ᵥ v).re := by
    linarith
  exact le_of_mul_le_mul_right h3 hpos

/-- `Σ |Im y_i| ≤ M ‖H‖_F / √((τ - α)(β - τ))` on a gap. -/
lemma imAbsSum_pencilRoots_le_gap {H : Matrix (Fin M) (Fin M) ℂ} (hH : H.IsHermitian)
    {α β τ : ℝ} (hα : α < τ) (hβ : τ < β) (hτ : τ ∉ spec hP)
    (hgap : ∀ p ∈ spec hP, p ≤ α ∨ β ≤ p) :
    imAbsSum (pencilRoots P H τ) ≤ M * (√(frob H) / √((τ - α) * (β - τ))) := by
  have hτ' : 0 < (τ - α) * (β - τ) := mul_pos (by linarith) (by linarith)
  have hterm : ∀ x ∈ pencilRoots P H τ, |x.im| ≤ √(frob H) / √((τ - α) * (β - τ)) := by
    intro x hx
    by_cases hxim : x.im = 0
    · rw [hxim, abs_zero]; positivity
    · have hb := normSq_nonreal_root_le_gap hP hH hα hβ hτ hgap hx hxim
      have h2 : ‖x‖ ≤ √(frob H) / √((τ - α) * (β - τ)) := by
        rw [le_div_iff₀ (Real.sqrt_pos.mpr hτ'), ← Real.sqrt_sq (norm_nonneg x),
          ← Real.sqrt_mul (sq_nonneg _)]
        exact Real.sqrt_le_sqrt hb
      exact (Complex.abs_im_le_norm x).trans h2
  have hcard : (pencilRoots P H τ).card = M := by
    unfold pencilRoots
    rw [IsAlgClosed.card_roots_eq_natDegree, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  unfold imAbsSum
  calc ((pencilRoots P H τ).map fun z => |z.im|).sum
      ≤ ((pencilRoots P H τ).map fun _ => √(frob H) / √((τ - α) * (β - τ))).sum :=
        Multiset.sum_map_le_sum_map _ _ hterm
    _ = M * (√(frob H) / √((τ - α) * (β - τ))) := by
        rw [Multiset.map_const', Multiset.sum_replicate, hcard, nsmul_eq_mul]

/-- For `τ ∉ spec P` strictly inside `[min spec, max spec]`, the enclosing gap. -/
lemma exists_gap {τ : ℝ} (hτ : τ ∉ spec hP) {p₀ q₀ : ℝ} (hp₀ : p₀ ∈ spec hP) (hq₀ : q₀ ∈ spec hP)
    (h₀ : p₀ < τ) (h₁ : τ < q₀) :
    ∃ α ∈ spec hP, ∃ β ∈ spec hP, α < τ ∧ τ < β ∧ ∀ p ∈ spec hP, p ≤ α ∨ β ≤ p := by
  classical
  set L := (spec hP).filter (· < τ) with hL
  set U := (spec hP).filter (τ < ·) with hU
  have hLne : L.Nonempty := ⟨p₀, Finset.mem_filter.mpr ⟨hp₀, h₀⟩⟩
  have hUne : U.Nonempty := ⟨q₀, Finset.mem_filter.mpr ⟨hq₀, h₁⟩⟩
  have hαL := L.max'_mem hLne
  have hβU := U.min'_mem hUne
  refine ⟨L.max' hLne, (Finset.mem_filter.mp hαL).1, U.min' hUne, (Finset.mem_filter.mp hβU).1,
    (Finset.mem_filter.mp hαL).2, (Finset.mem_filter.mp hβU).2, fun p hp => ?_⟩
  rcases lt_trichotomy p τ with h | h | h
  · exact Or.inl (L.le_max' p (Finset.mem_filter.mpr ⟨hp, h⟩))
  · exact absurd (h ▸ hp) hτ
  · exact Or.inr (U.min'_le p (Finset.mem_filter.mpr ⟨hp, h⟩))

end Roots

/-! ### The dominating function -/

/-- `1/√((τ - p)(q - τ))` on `(p, q)`, `0` elsewhere. -/
noncomputable def arcW (p q τ : ℝ) : ℝ := Set.indicator (Ioo p q) (fun τ => 1 / √((τ - p) * (q - τ))) τ

lemma arcW_nonneg (p q τ : ℝ) : 0 ≤ arcW p q τ := by
  unfold arcW
  by_cases h : τ ∈ Ioo p q
  · rw [Set.indicator_of_mem h]; positivity
  · rw [Set.indicator_of_notMem h]

lemma integrableOn_arcW {p q : ℝ} (hpq : p < q) :
    IntegrableOn (fun τ : ℝ => 1 / √((τ - p) * (q - τ))) (Ioo p q) := by
  have h := intervalIntegral.integrableOn_deriv_of_nonneg (a := p) (b := q)
    (g := fun τ : ℝ => Real.arcsin ((2 * τ - p - q) / (q - p)))
    (g' := fun τ : ℝ => 1 / √((τ - p) * (q - τ)))
    (Real.continuous_arcsin.comp (by fun_prop)).continuousOn ?_ ?_
  · exact h.mono_set Ioo_subset_Ioc_self
  · intro τ hτ
    have hqp : 0 < q - p := by linarith
    have h1 : (2 * τ - p - q) / (q - p) ≠ -1 := by
      rw [ne_eq, div_eq_iff hqp.ne']; intro h; linarith [hτ.1]
    have h2 : (2 * τ - p - q) / (q - p) ≠ 1 := by
      rw [ne_eq, div_eq_iff hqp.ne']; intro h; linarith [hτ.2]
    have hd := (Real.hasDerivAt_arcsin h1 h2).comp τ
      ((((hasDerivAt_id τ).const_mul 2).sub_const p |>.sub_const q).div_const (q - p))
    refine hd.congr_deriv ?_
    have hpos : 0 < (τ - p) * (q - τ) := mul_pos (by linarith [hτ.1]) (by linarith [hτ.2])
    have e : 1 - ((2 * τ - p - q) / (q - p)) ^ 2 = 4 * ((τ - p) * (q - τ)) / (q - p) ^ 2 := by
      field_simp; ring
    rw [e, Real.sqrt_div' _ (by positivity), Real.sqrt_mul (by norm_num),
      show √(4:ℝ) = 2 by rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)],
      Real.sqrt_sq hqp.le]
    have hs : 0 < √((τ - p) * (q - τ)) := Real.sqrt_pos.mpr hpos
    field_simp
  · intro τ _
    positivity

lemma integrable_arcW (p q : ℝ) : Integrable (arcW p q) := by
  unfold arcW
  rw [integrable_indicator_iff measurableSet_Ioo]
  rcases lt_or_ge p q with h | h
  · exact integrableOn_arcW h
  · rw [Ioo_eq_empty (not_lt.mpr h)]
    exact integrableOn_empty

section Dom

variable {P : Matrix (Fin M) (Fin M) ℂ} (hP : P.IsHermitian)

/-- The dominating function `Ψ(τ) = Σ_{p < q in spec P} 1_{(p,q)}(τ)/√((τ - p)(q - τ))`. -/
noncomputable def domG (τ : ℝ) : ℝ :=
  ∑ p ∈ spec hP, ∑ q ∈ spec hP, if p < q then arcW p q τ else 0

lemma domG_nonneg (τ : ℝ) : 0 ≤ domG hP τ :=
  Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun q _ => by
    split_ifs
    · exact arcW_nonneg _ _ _
    · exact le_rfl

lemma integrable_domG : Integrable (domG hP) := by
  unfold domG
  refine integrable_finsetSum _ fun p _ => integrable_finsetSum _ fun q _ => ?_
  by_cases h : p < q
  · simp only [h, if_true]; exact integrable_arcW p q
  · simp only [h, if_false]; exact integrable_zero _ _ _

lemma arcW_le_domG {α β τ : ℝ} (hα : α ∈ spec hP) (hβ : β ∈ spec hP) (h : α < β) :
    arcW α β τ ≤ domG hP τ := by
  unfold domG
  have h1 : arcW α β τ = if α < β then arcW α β τ else 0 := by rw [if_pos h]
  rw [h1]
  refine le_trans ?_ (Finset.single_le_sum (f := fun p => ∑ q ∈ spec hP,
    if p < q then arcW p q τ else 0) (fun p _ => Finset.sum_nonneg fun q _ => by
      split_ifs
      · exact arcW_nonneg _ _ _
      · exact le_rfl) hα)
  exact Finset.single_le_sum (f := fun q => if α < q then arcW α q τ else 0)
    (fun q _ => by
      split_ifs
      · exact arcW_nonneg _ _ _
      · exact le_rfl) hβ

/-- The pointwise bound: for `τ ∉ spec P`, `Σ|Im y_i| ≤ M ‖H‖_F Ψ(τ)`. -/
theorem imAbsSum_pencilRoots_le_domG {H : Matrix (Fin M) (Fin M) ℂ} (hH : H.IsHermitian) (τ : ℝ) :
    imAbsSum (pencilRoots P H τ) ≤ M * √(frob H) * domG hP τ := by
  by_cases hτ : τ ∈ spec hP
  · rw [imAbsSum_pencilRoots_of_mem_spec hP hτ]
    exact mul_nonneg (by positivity) (domG_nonneg hP τ)
  by_cases hdef : (∀ p ∈ spec hP, τ < p) ∨ (∀ p ∈ spec hP, p < τ)
  · rw [imAbsSum_pencilRoots_eq_zero_of_definite hP hH hdef]
    exact mul_nonneg (by positivity) (domG_nonneg hP τ)
  push Not at hdef
  obtain ⟨⟨p₀, hp₀, hp₀τ⟩, ⟨q₀, hq₀, hq₀τ⟩⟩ := hdef
  have hp₀τ' : p₀ < τ := lt_of_le_of_ne hp₀τ (fun h => hτ (h ▸ hp₀))
  have hq₀τ' : τ < q₀ := lt_of_le_of_ne hq₀τ (fun h => hτ (h ▸ hq₀))
  obtain ⟨α, hα, β, hβ, hατ, hτβ, hgap⟩ := exists_gap hP hτ hp₀ hq₀ hp₀τ' hq₀τ'
  have hb := imAbsSum_pencilRoots_le_gap hP hH hατ hτβ hτ hgap
  have hw : 1 / √((τ - α) * (β - τ)) = arcW α β τ := by
    unfold arcW; rw [Set.indicator_of_mem (Set.mem_Ioo.mpr ⟨hατ, hτβ⟩ : τ ∈ Ioo α β)]
  have hd := arcW_le_domG hP (τ := τ) hα hβ (hατ.trans hτβ)
  calc imAbsSum (pencilRoots P H τ) ≤ M * (√(frob H) / √((τ - α) * (β - τ))) := hb
    _ = M * √(frob H) * arcW α β τ := by rw [← hw]; ring
    _ ≤ M * √(frob H) * domG hP τ := mul_le_mul_of_nonneg_left hd (by positivity)

end Dom

/-! ### The density -/

/-- The density of Theorem A: `ρ(s,τ) = (1/2π) Σ_i |Im x_i(s,τ)|`, `x_i` the roots of
`det(g - s - x(P - τ))` (`0` on the lines `τ ∈ spec P`). -/
noncomputable def rhoG (P g : Matrix (Fin M) (Fin M) ℂ) (s τ : ℝ) : ℝ :=
  imAbsSum (pencilRoots P (g - (s : ℂ) • 1) τ) / (2 * π)

lemma rhoG_nonneg (P g : Matrix (Fin M) (Fin M) ℂ) (s τ : ℝ) : 0 ≤ rhoG P g s τ :=
  div_nonneg (OQP27.StripL3b.imAbsSum_nonneg _) (by positivity)

lemma isHermitian_g_sub {g : Matrix (Fin M) (Fin M) ℂ} (hg : g.IsHermitian) (s : ℝ) :
    (g - (s : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ)).IsHermitian :=
  hg.sub (isHermitian_one.smul (OQP27.StripL3b.isSelfAdjoint_ofReal s))

section Density

variable {P g : Matrix (Fin M) (Fin M) ℂ} (hP : P.IsHermitian) (hg : g.IsHermitian)
include hP hg

/-- **Support in `s`** (Lemma 2.2(3)): `ρ(s,τ) = 0` unless `λ_min(g) < s < λ_max(g)`. -/
theorem rhoG_eq_zero_of_semidef {s : ℝ}
    (hs : (∀ i, s ≤ hg.eigenvalues i) ∨ (∀ i, hg.eigenvalues i ≤ s)) (τ : ℝ) :
    rhoG P g s τ = 0 := by
  have hpsd : (g - (s : ℂ) • 1).PosSemidef ∨ (-(g - (s : ℂ) • 1)).PosSemidef := by
    rcases hs with h | h
    · exact Or.inl (OQP27.StripL3b.posSemidef_sub_smul_one hg h)
    · exact Or.inr (OQP27.StripL3b.posSemidef_neg_sub_smul_one hg h)
  unfold rhoG
  rw [imAbsSum_pencilRoots_eq_zero_of_posSemidef hP hpsd τ, zero_div]

/-- **Support in `τ`**: if `spec P ⊆ [0,1]`, then `ρ(s,τ) = 0` for `τ ∉ (0,1)`. -/
theorem rhoG_eq_zero_of_not_mem_Ioo (hspec : ∀ p ∈ spec hP, 0 ≤ p ∧ p ≤ 1) {τ : ℝ}
    (hτ : ¬ (0 < τ ∧ τ < 1)) (s : ℝ) : rhoG P g s τ = 0 := by
  unfold rhoG
  by_cases hτs : τ ∈ spec hP
  · rw [imAbsSum_pencilRoots_of_mem_spec hP hτs, zero_div]
  have hdef : (∀ p ∈ spec hP, τ < p) ∨ (∀ p ∈ spec hP, p < τ) := by
    rcases not_and_or.mp hτ with h | h
    · left
      intro p hp
      rcases (hspec p hp).1.lt_or_eq with h' | h'
      · linarith
      · rcases (not_lt.mp h).lt_or_eq with h'' | h''
        · linarith
        · exact absurd (h''.symm ▸ h' ▸ hp) hτs
    · right
      intro p hp
      rcases (hspec p hp).2.lt_or_eq with h' | h'
      · linarith
      · rcases (not_lt.mp h).lt_or_eq with h'' | h''
        · linarith
        · exact absurd (h'' ▸ h' ▸ hp) hτs
  rw [imAbsSum_pencilRoots_eq_zero_of_definite hP (isHermitian_g_sub hg s) hdef, zero_div]

/-- Compact support in `s`. -/
theorem rhoG_support : ∃ R : ℝ, 0 < R ∧ ∀ s τ : ℝ, R ≤ |s| → rhoG P g s τ = 0 := by
  refine ⟨1 + ∑ i, |hg.eigenvalues i|, by positivity, fun s τ hs => ?_⟩
  have hle : ∀ i, |hg.eigenvalues i| ≤ ∑ i, |hg.eigenvalues i| := fun i =>
    Finset.single_le_sum (f := fun i => |hg.eigenvalues i|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ i)
  apply rhoG_eq_zero_of_semidef hP hg _ τ
  rcases le_or_gt 0 s with h | h
  · rw [abs_of_nonneg h] at hs
    exact Or.inr fun i => by linarith [le_abs_self (hg.eigenvalues i), hle i]
  · rw [abs_of_neg h] at hs
    exact Or.inl fun i => by linarith [neg_abs_le (hg.eigenvalues i), hle i]

/-- **Uniform integrable bound** (from Lemma 2.2(6)): `ρ(s,τ) ≤ C Ψ(τ)`. -/
theorem rhoG_le_domG : ∃ C : ℝ, 0 ≤ C ∧ ∀ s τ : ℝ, rhoG P g s τ ≤ C * domG hP τ := by
  obtain ⟨R, hR, hsupp⟩ := rhoG_support hP hg
  have hcont : Continuous fun s : ℝ => √(frob (g - (s : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ))) := by
    unfold frob
    fun_prop
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨M * max K 0 / (2 * π), by positivity, fun s τ => ?_⟩
  by_cases hs : R ≤ |s|
  · rw [hsupp s τ hs]
    exact mul_nonneg (by positivity) (domG_nonneg hP τ)
  · have hs : |s| < R := not_le.mp hs
    have hsI : s ∈ Set.Icc (-R) R := ⟨by linarith [neg_abs_le s], by linarith [le_abs_self s]⟩
    have hKs : √(frob (g - (s : ℂ) • 1)) ≤ max K 0 := by
      have := hK s hsI
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] at this
      exact this.trans (le_max_left _ _)
    have hb := imAbsSum_pencilRoots_le_domG hP (isHermitian_g_sub hg s) τ
    unfold rhoG
    rw [div_le_iff₀ (by positivity)]
    calc imAbsSum (pencilRoots P (g - (s : ℂ) • 1) τ)
        ≤ M * √(frob (g - (s : ℂ) • 1)) * domG hP τ := hb
      _ ≤ M * max K 0 * domG hP τ := by
          gcongr
          exact domG_nonneg hP τ
      _ = M * max K 0 / (2 * π) * domG hP τ * (2 * π) := by
          field_simp

end Density

/-! ### Measurability of the density -/

section Measurability

variable {P : Matrix (Fin M) (Fin M) ℂ} (hP : P.IsHermitian) (g : Matrix (Fin M) (Fin M) ℂ)
include hP

/-- The explicit form of `(P - τ)⁻¹ (g - s)` off the spectrum. -/
noncomputable def pencilMatG (s τ : ℝ) : Matrix (Fin M) (Fin M) ℂ :=
  fcalc hP (fun i => ((hP.eigenvalues i - τ : ℝ) : ℂ)⁻¹) * (g - (s : ℂ) • 1)

lemma continuous_fcalc : Continuous (fun f : Fin M → ℂ => fcalc hP f) := by
  unfold fcalc
  exact (continuous_const.matrix_mul (continuous_id.matrix_diagonal)).matrix_mul continuous_const

lemma measurable_log_det_gen :
    Measurable (fun q : (ℝ × ℝ) × ℝ =>
      Real.log ‖((q.2 : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ) - pencilMatG hP g q.1.1 q.1.2).det‖) := by
  have hΦ : Continuous (fun v : ℝ × ℝ × (Fin M → ℂ) =>
      ((v.1 : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ)
        - fcalc hP v.2.2 * (g - (v.2.1 : ℂ) • 1)).det) := by
    have h1 : Continuous (fun v : ℝ × ℝ × (Fin M → ℂ) => fcalc hP v.2.2) :=
      (continuous_fcalc hP).comp continuous_snd.snd
    exact (((Complex.continuous_ofReal.comp continuous_fst).smul continuous_const).sub
      (h1.matrix_mul (continuous_const.sub
        ((Complex.continuous_ofReal.comp continuous_snd.fst).smul continuous_const)))).matrix_det
  have hin : Measurable (fun q : (ℝ × ℝ) × ℝ =>
      (q.2, q.1.1, fun i => ((hP.eigenvalues i - q.1.2 : ℝ) : ℂ)⁻¹)) := by
    refine measurable_snd.prodMk (measurable_fst.fst.prodMk ?_)
    exact measurable_pi_lambda _ fun i =>
      (Complex.measurable_ofReal.comp (measurable_const.sub measurable_fst.snd)).inv
  exact (hΦ.measurable.comp hin).norm.log

lemma measurable_integral_log_det_gen (n : ℕ) :
    Measurable (fun q : ℝ × ℝ =>
      ∫ x in (-(n : ℝ))..n, Real.log ‖((x : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ)
        - pencilMatG hP g q.1 q.2).det‖) := by
  have h := (measurable_log_det_gen hP g).stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Set.Ioc (-(n : ℝ)) n))
  have hle : -(n : ℝ) ≤ n := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have heq : (fun q : ℝ × ℝ => ∫ x in (-(n : ℝ))..n, Real.log ‖((x : ℂ) •
      (1 : Matrix (Fin M) (Fin M) ℂ) - pencilMatG hP g q.1 q.2).det‖)
      = fun q => ∫ x, Real.log ‖((x : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ)
          - pencilMatG hP g q.1 q.2).det‖ ∂(volume.restrict (Set.Ioc (-(n : ℝ)) n)) := by
    funext q
    rw [intervalIntegral.integral_of_le hle]
  rw [heq]
  exact h.measurable

/-- **The density is jointly measurable.** -/
theorem measurable_rhoG : Measurable (Function.uncurry (rhoG P g)) := by
  classical
  let f : ℕ → ℝ × ℝ → ℝ := fun n q => if q.2 ∈ spec hP then 0 else
      ((∫ x in (-(n : ℝ))..n, Real.log ‖((x : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ)
        - pencilMatG hP g q.1 q.2).det‖) - M * (2 * n * Real.log n - 2 * n)) / (2 * π ^ 2)
  apply measurable_of_tendsto_metrizable (f := f)
  · intro n
    apply Measurable.ite
    · exact measurable_snd (Finset.measurableSet _)
    · exact measurable_const
    · exact ((measurable_integral_log_det_gen hP g n).sub measurable_const).div_const _
  · rw [tendsto_pi_nhds]
    rintro ⟨s, τ⟩
    simp only [f, Function.uncurry_apply_pair]
    split_ifs with h
    · unfold rhoG
      rw [imAbsSum_pencilRoots_of_mem_spec hP h, zero_div]
      exact tendsto_const_nhds
    · set A := (P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ))⁻¹ * (g - (s : ℂ) • 1) with hA_def
      have hA : pencilMatG hP g s τ = A := by
        rw [pencilMatG, hA_def, inv_sub_eq_fcalc hP h]
      have hmon : A.charpoly.Monic := Matrix.charpoly_monic A
      have key := (OQP27.StripL3b.tendsto_integral_log_norm_eval A.charpoly hmon.ne_zero).comp
        tendsto_natCast_atTop_atTop
      have key2 := key.div_const (2 * π ^ 2)
      have hlim : π * (A.charpoly.roots.map (fun z => |z.im|)).sum / (2 * π ^ 2)
          = rhoG P g s τ := by
        unfold rhoG pencilRoots imAbsSum
        rw [← hA_def]
        field_simp
      rw [hlim] at key2
      refine key2.congr (fun n => ?_)
      simp only [Function.comp_apply, hmon.leadingCoeff, norm_one, Real.log_one, mul_zero,
        sub_zero, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin, hA, Matrix.eval_charpoly,
        Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

end Measurability

end HarmonicMajorization
