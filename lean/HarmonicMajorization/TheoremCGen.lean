import HarmonicMajorization.TheoremBGen
import HarmonicMajorization.TheoremCProj

/-!
# Theorem C (quantitative form) for general `0 ≤ B ≤ 1`

Authors: Ansh Mishra, Aryan Senthilkumar.  License: MIT.

Setting as in `HarmonicMajorization/TheoremBGen.lean`: `0 ≤ B ≤ 1`, `P = 1 - B` with distinct
eigenvalues `p ∈ spec P` and spectral projections `Q_p = sproj hP p`, `g` Hermitian, `ρ = rhoG (1 - B) g`,
`V(λ) = ∫_0^1 ∫ K_{1-τ}(s - λ) ρ(s,τ) ds dτ`; `frobNorm`, `opNorm` are Mathlib's Frobenius and Euclidean
operator norms (`HarmonicMajorization/TheoremCProj.lean`).

Main results (from `Hyp_RI_gen M`):
* `stripBalayage_ge_gen`: for every real `λ`, with `R = |λ| + ‖g‖`,
  `V(λ) ≥ 1/(2(1 + cosh(πR))) · Σ_{p<q} ‖Q_p g Q_q‖_F² · (1/(q - p)) ∫_p^q sin(πτ) dτ`;
* **`theoremC_gen`**: the same lower bound for
  `Σ_{ν ∈ spec(B+ig)} h_λ(ν) - Σ_{ν ∈ spec(B+ig_d)} h_λ(ν)` (THEOREMS.md, Theorem C).

Hypothesis used: `Hyp_RI_gen M` (the multi-line Radon identity), through Theorems A and B.
-/

set_option autoImplicit false

namespace HarmonicMajorization

open Matrix Complex MeasureTheory Filter Set
open scoped Real ComplexOrder
open OQP27.StripL3a (stripKernel stripBalayage hLam)

variable {M : ℕ}

/-- `∫_p^q sin(πτ) dτ = (cos πp - cos πq)/π`. -/
lemma integral_sin_pi (p q : ℝ) :
    ∫ τ in p..q, Real.sin (π * τ) = (Real.cos (π * p) - Real.cos (π * q)) / π := by
  have hpi : π ≠ 0 := Real.pi_ne_zero
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.sin x) hpi, integral_sin, smul_eq_mul,
    div_eq_inv_mul]

section Sandwich

variable {P g : Matrix (Fin M) (Fin M) ℂ} (hP : P.IsHermitian) (hg : g.IsHermitian)
include hP hg

/-- `‖Q_p g Q_q‖_F² = Σ_{ij} |(Q_q g Q_p)_{ij}|²` (the adjoint has the same Frobenius norm). -/
lemma frobNorm_sandwich_sq (p q : ℝ) :
    frobNorm (sproj hP p * g * sproj hP q) ^ 2
      = ∑ i, ∑ j, ‖(sproj hP q * g * sproj hP p) i j‖ ^ 2 := by
  have h : (sproj hP p * g * sproj hP q)ᴴ = sproj hP q * g * sproj hP p := by
    rw [conjTranspose_mul, conjTranspose_mul, (isHermitian_sproj hP p).eq, hg.eq,
      (isHermitian_sproj hP q).eq, ← Matrix.mul_assoc]
  rw [← h, ← frobNorm_sq]
  unfold frobNorm
  rw [@Matrix.frobenius_norm_conjTranspose]

end Sandwich

section TheoremC

variable {B g : Matrix (Fin M) (Fin M) ℂ} (hB0 : B.PosSemidef) (hB1 : (1 - B).PosSemidef)
  (hg : g.IsHermitian)
include hB0 hB1 hg

omit hB0 in
/-- Support of the density: `ρ(s,τ) ≠ 0` forces `|s| ≤ ‖g‖`. -/
lemma abs_le_opNorm_of_rhoG_ne_zero {s τ : ℝ} (h : rhoG (1 - B) g s τ ≠ 0) : |s| ≤ opNorm g := by
  have hP := hB1.isHermitian
  have h1 : ¬ (∀ i, s ≤ hg.eigenvalues i) := fun h' =>
    h (rhoG_eq_zero_of_semidef hP hg (Or.inl h') τ)
  have h2 : ¬ (∀ i, hg.eigenvalues i ≤ s) := fun h' =>
    h (rhoG_eq_zero_of_semidef hP hg (Or.inr h') τ)
  simp only [not_forall, not_le] at h1 h2
  obtain ⟨i, hi⟩ := h1
  obtain ⟨j, hj⟩ := h2
  have hi' := abs_eigenvalues_le_opNorm hg i
  have hj' := abs_eigenvalues_le_opNorm hg j
  rw [abs_le]
  constructor
  · linarith [neg_abs_le (hg.eigenvalues i)]
  · linarith [le_abs_self (hg.eigenvalues j)]

/-- **The quantitative lower bound on the defect** (THEOREMS.md, Theorem C):
`V(λ) ≥ 1/(2(1 + cosh(π(|λ| + ‖g‖)))) · Σ_{p<q} ‖Q_p g Q_q‖_F² (1/(q - p)) ∫_p^q sin(πτ) dτ`. -/
theorem stripBalayage_ge_gen (hRI : Hyp_RI_gen M) (lam : ℝ) :
    1 / (2 * (1 + Real.cosh (π * (|lam| + opNorm g))))
        * (∑ p ∈ spec hB1.isHermitian, ∑ q ∈ spec hB1.isHermitian, if p < q then
            frobNorm (sproj hB1.isHermitian p * g * sproj hB1.isHermitian q) ^ 2
              * (1 / (q - p) * ∫ τ in p..q, Real.sin (π * τ)) else 0)
      ≤ stripBalayage (rhoG (1 - B) g) lam := by
  set hP := hB1.isHermitian
  have hspec := spec_one_sub_subset hB0 hB1
  set F := rhoG (1 - B) g with hFdef
  have hF : DensityRegG F := densityRegG_rhoG hP hg hspec
  set R := |lam| + opNorm g with hR
  set c := 1 / (2 * (1 + Real.cosh (π * R))) with hc
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hsum : (∑ p ∈ spec hP, ∑ q ∈ spec hP, if p < q then
      frobNorm (sproj hP p * g * sproj hP q) ^ 2
        * (1 / (q - p) * ∫ τ in p..q, Real.sin (π * τ)) else 0)
      = ∫ q : ℝ × ℝ, Real.sin (π * q.2) * F q.1 q.2 := by
    rw [hFdef, integral_sin_mul_rhoG hP hg hspec hRI]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    split_ifs with hpq
    · rw [frobNorm_sandwich_sq hP hg, integral_sin_pi]
      have hqp : q - p ≠ 0 := sub_ne_zero.mpr hpq.ne'
      field_simp
    · rfl
  rw [hsum, ← integral_const_mul, hF.stripBalayage_eq]
  unfold OQP27.StripL3a.balayageProd
  have hFm : Measurable (fun q : ℝ × ℝ => F q.1 q.2) := hF.measurable
  have hm : Measurable (fun q : ℝ × ℝ => c * (Real.sin (π * q.2) * F q.1 q.2)) :=
    ((by fun_prop : Measurable fun q : ℝ × ℝ => Real.sin (π * q.2)).mul hFm).const_mul c
  have hint1 : Integrable (fun q : ℝ × ℝ => c * (Real.sin (π * q.2) * F q.1 q.2)) := by
    refine (hF.integrable.const_mul c).mono' hm.aestronglyMeasurable
      (Eventually.of_forall fun q => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hc0, abs_of_nonneg (hF.nonneg _ _)]
    exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (hF.nonneg _ _)
      (Real.abs_sin_le_one _)) hc0
  refine integral_mono hint1 (hF.integrable_section lam) (fun q => ?_)
  show c * (Real.sin (π * q.2) * F q.1 q.2)
    ≤ stripKernel (1 - q.2) (q.1 - lam) * F q.1 q.2
  by_cases hq : F q.1 q.2 = 0
  · rw [hq, mul_zero, mul_zero, mul_zero]
  · have hτ : 0 < q.2 ∧ q.2 < 1 := by
      by_contra hτ
      exact hq (hF.zero_of_not_mem _ _ hτ)
    have hs : |q.1| ≤ opNorm g := abs_le_opNorm_of_rhoG_ne_zero hB1 hg hq
    have hu : |q.1 - lam| ≤ R := by
      rw [hR]
      calc |q.1 - lam| ≤ |q.1| + |lam| := abs_sub _ _
        _ ≤ opNorm g + |lam| := by linarith
        _ = |lam| + opNorm g := by ring
    have hK := kernel_lower_bound hτ.1 hτ.2 hu
    have hFn := hF.nonneg q.1 q.2
    calc c * (Real.sin (π * q.2) * F q.1 q.2)
        = Real.sin (π * q.2) / (2 * (1 + Real.cosh (π * R))) * F q.1 q.2 := by
          rw [hc]; ring
      _ ≤ stripKernel (1 - q.2) (q.1 - lam) * F q.1 q.2 := mul_le_mul_of_nonneg_right hK hFn

/-- **Theorem C** (THEOREMS.md, Section 1): for every real `λ`, with `R = |λ| + ‖g‖`,
`Σ_{ν ∈ spec(B+ig)} h_λ(ν) - Σ_{ν ∈ spec(B+ig_d)} h_λ(ν)
  ≥ 1/(2(1 + cosh(πR))) · Σ_{p<q} ‖Q_p g Q_q‖_F² (1/(q - p)) ∫_p^q sin(πτ) dτ`. -/
theorem theoremC_gen (hRI : Hyp_RI_gen M) (lam : ℝ) :
    1 / (2 * (1 + Real.cosh (π * (|lam| + opNorm g))))
        * (∑ p ∈ spec hB1.isHermitian, ∑ q ∈ spec hB1.isHermitian, if p < q then
            frobNorm (sproj hB1.isHermitian p * g * sproj hB1.isHermitian q) ^ 2
              * (1 / (q - p) * ∫ τ in p..q, Real.sin (π * τ)) else 0)
      ≤ ((B + I • g).charpoly.roots.map (hLam lam)).sum
        - ((B + I • pinchH hB1.isHermitian g).charpoly.roots.map (hLam lam)).sum := by
  rw [theoremB_gen hB0 hB1 hg hRI lam]
  exact stripBalayage_ge_gen hB0 hB1 hg hRI lam

end TheoremC

end HarmonicMajorization
