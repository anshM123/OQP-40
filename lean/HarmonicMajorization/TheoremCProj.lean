import HarmonicMajorization.MarginalProj
import OQP27.StripRIChain
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Theorem C (quantitative strip inequality), projection case

Authors: Ansh Mishra, Aryan Senthilkumar.  License: MIT.

Setting (as in `OQP27.StripL3a`): `B` an orthogonal projection on `ℂ^M`, `P = 1 - B`, `g` Hermitian,
`λ` real; `h_λ` is `OQP27.StripL3a.hLam`, the eigenvalues of `B + ig` are
`(B + I • g).charpoly.roots`, `Tr[(P(g-λ)P)_+]` is `OQP27.StripL3a.posPartTrace`, and the defect is
`V(λ) = ∫_0^1 ∫ K_{1-τ}(s - λ) ρ(s,τ) ds dτ` (`OQP27.StripL3a.stripBalayage`) with the density
`ρ = OQP27.StripL3b.stripF (1 - B) g` of Theorem A.

Norms: `frobNorm` is Mathlib's Frobenius norm and `opNorm` Mathlib's operator norm for the Euclidean
norm on `ℂ^M` (`Matrix.frobeniusNormedAddCommGroup`, `Matrix.instL2OpNormedAddCommGroup`).

Main results (THEOREMS.md, Theorem C, the case `spec B ⊆ {0, 1}`):
* `kernel_lower_bound`: `K_{1-τ}(u) ≥ sin(πτ)/(2(1 + cosh(πR)))` for `0 < τ < 1`, `|u| ≤ R`;
* `stripBalayage_ge_proj`: `V(λ) ≥ (1/(2(1 + cosh(πR)))) · (2/π) ‖BgP‖_F²`, `R = |λ| + ‖g‖`;
* `frobNorm_comm_sq`: `‖[B,g]‖_F² = 2 ‖BgP‖_F²`;
* **`theoremC_proj`**: `Σ_{ν ∈ spec(B+ig)} h_λ(ν) - Tr[(P(g-λ)P)_+] ≥ ‖[B,g]‖_F² / (2π(1 + cosh(π(|λ| + ‖g‖))))`.

No hypotheses: the inputs are `OQP27.StripL3b.strip_defect_formula_noHyp` (the exact defect) and
`HarmonicMajorization.integral_sin_mul_stripF` (the sine moment of the density).
-/

set_option autoImplicit false

namespace HarmonicMajorization

open Matrix Complex MeasureTheory Filter
open scoped Real

variable {M : ℕ}

/-! ### Norms -/

/-- The Frobenius norm `‖A‖_F` (Mathlib's `Matrix.frobeniusNormedAddCommGroup`). -/
noncomputable def frobNorm (A : Matrix (Fin M) (Fin M) ℂ) : ℝ :=
  @Norm.norm _ Matrix.frobeniusNormedAddCommGroup.toNorm A

/-- The operator norm `‖A‖` for the Euclidean norm on `ℂ^M`
(Mathlib's `Matrix.instL2OpNormedAddCommGroup`). -/
noncomputable def opNorm (A : Matrix (Fin M) (Fin M) ℂ) : ℝ :=
  @Norm.norm _ Matrix.instL2OpNormedAddCommGroup.toNorm A

lemma frobNorm_sq (A : Matrix (Fin M) (Fin M) ℂ) : frobNorm A ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  unfold frobNorm
  rw [@Matrix.frobenius_norm_def]
  have h0 : 0 ≤ ∑ i, ∑ j, ‖A i j‖ ^ (2 : ℝ) := by positivity
  rw [← Real.sqrt_eq_rpow, Real.sq_sqrt h0]
  simp only [Real.rpow_two]

/-- Eigenvalues of a Hermitian matrix are bounded by its operator norm. -/
lemma abs_eigenvalues_le_opNorm {g : Matrix (Fin M) (Fin M) ℂ} (hg : g.IsHermitian) (i : Fin M) :
    |hg.eigenvalues i| ≤ opNorm g := by
  set v := hg.eigenvectorBasis i with hvdef
  have hv : ‖v‖ = 1 := hg.eigenvectorBasis.orthonormal.1 i
  have h1 := @Matrix.l2_opNorm_mulVec ℂ (Fin M) (Fin M) _ _ _ _ g v
  have h2 : (EuclideanSpace.equiv (Fin M) ℂ).symm (g *ᵥ v.ofLp) = (hg.eigenvalues i : ℂ) • v := by
    have := hg.mulVec_eigenvectorBasis i
    rw [← hvdef] at this
    rw [this]
    rfl
  rw [h2, norm_smul, hv, mul_one] at h1
  unfold opNorm
  simpa using h1

/-- `Re Tr(A Aᴴ) = ‖A‖_F²`. -/
lemma re_trace_mul_conjTranspose (A : Matrix (Fin M) (Fin M) ℂ) :
    (A * Aᴴ).trace.re = frobNorm A ^ 2 := by
  rw [trace_mul_conjTranspose_eq_sum, Complex.ofReal_re, frobNorm_sq]

section Proj

variable {B g : Matrix (Fin M) (Fin M) ℂ}

/-- `Tr([B,g][B,g]ᴴ) = 2 Tr(BgPg)` for a projection `B`, `P = 1 - B`. -/
lemma trace_comm_mul_conjTranspose (hB : B.IsHermitian ∧ B * B = B) (hg : g.IsHermitian) :
    ((B * g - g * B) * (B * g - g * B)ᴴ).trace = 2 * (B * g * (1 - B) * g).trace := by
  have hc : (B * g - g * B)ᴴ = g * B - B * g := by
    rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, hB.1.eq, hg.eq]
  rw [hc]
  have e : (B * g - g * B) * (g * B - B * g)
      = B * g * g * B - B * g * B * g - g * B * g * B + g * B * B * g := by noncomm_ring
  have t1 : (B * g * g * B).trace = (B * g * g).trace := by
    rw [Matrix.trace_mul_comm (B * g * g) B, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hB.2]
  have t2 : (g * B * B * g).trace = (B * g * g).trace := by
    rw [Matrix.mul_assoc g B B, hB.2, Matrix.trace_mul_comm (g * B) g, ← Matrix.mul_assoc,
      Matrix.trace_mul_comm (g * g) B, Matrix.mul_assoc]
  have t3 : (g * B * g * B).trace = (B * g * B * g).trace := by
    rw [Matrix.trace_mul_comm (g * B * g) B]; simp only [Matrix.mul_assoc]
  have t4 : (B * g * (1 - B) * g).trace = (B * g * g).trace - (B * g * B * g).trace := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.trace_sub]
  rw [e, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub, t1, t2, t3, t4]
  ring

/-- `‖[B,g]‖_F² = 2 ‖BgP‖_F²`. -/
theorem frobNorm_comm_sq (hB : B.IsHermitian ∧ B * B = B) (hg : g.IsHermitian) :
    frobNorm (B * g - g * B) ^ 2 = 2 * ∑ i, ∑ j, ‖(B * g * (1 - B)) i j‖ ^ 2 := by
  have hP : OQP27.StripL3b.IsProj (1 - B) := OQP27.StripL3a.isProj_one_sub hB
  have h1 := trace_BgPg_eq hP hg
  rw [sub_sub_cancel] at h1
  rw [← re_trace_mul_conjTranspose, trace_comm_mul_conjTranspose hB hg, h1,
    trace_mul_conjTranspose_eq_sum]
  rw [show (2 : ℂ) * ((∑ i, ∑ j, ‖(B * g * (1 - B)) i j‖ ^ 2 : ℝ) : ℂ)
      = ((2 * ∑ i, ∑ j, ‖(B * g * (1 - B)) i j‖ ^ 2 : ℝ) : ℂ) by push_cast; ring,
    Complex.ofReal_re]

end Proj

/-! ### The kernel bound -/

/-- `K_{1-τ}(u) ≥ sin(πτ)/(2(1 + cosh(πR)))` for `0 < τ < 1` and `|u| ≤ R`. -/
theorem kernel_lower_bound {τ R u : ℝ} (h0 : 0 < τ) (h1 : τ < 1) (hu : |u| ≤ R) :
    Real.sin (π * τ) / (2 * (1 + Real.cosh (π * R))) ≤ OQP27.StripL3a.stripKernel (1 - τ) u := by
  unfold OQP27.StripL3a.stripKernel
  have hs : Real.sin (π * (1 - τ)) = Real.sin (π * τ) := by
    rw [show π * (1 - τ) = π - π * τ by ring, Real.sin_pi_sub]
  have hc : Real.cos (π * (1 - τ)) = -Real.cos (π * τ) := by
    rw [show π * (1 - τ) = π - π * τ by ring, Real.cos_pi_sub]
  rw [hs, hc, sub_neg_eq_add]
  have hsin : 0 < Real.sin (π * τ) := OQP27.StripL3a.sin_pi_mul_pos h0 h1
  have hpos : 0 < Real.cosh (π * u) + Real.cos (π * τ) := by
    have := OQP27.StripL3a.stripKernel_denom_pos (X := 1 - τ) (by linarith) (by linarith) u
    rw [hc] at this
    linarith
  have hcosh : Real.cosh (π * u) ≤ Real.cosh (π * R) := by
    rw [Real.cosh_le_cosh, abs_mul, abs_mul, abs_of_pos Real.pi_pos]
    exact mul_le_mul_of_nonneg_left (hu.trans (le_abs_self R)) Real.pi_pos.le
  have hcos : Real.cos (π * τ) ≤ 1 := Real.cos_le_one _
  apply div_le_div_of_nonneg_left hsin.le (by positivity)
  linarith

/-! ### Theorem C for a projection -/

section TheoremC

variable {B g : Matrix (Fin M) (Fin M) ℂ}

/-- Support of the density: `ρ(s,τ) ≠ 0` forces `|s| ≤ ‖g‖`. -/
lemma abs_le_opNorm_of_stripF_ne_zero (hB : B.IsHermitian ∧ B * B = B) (hg : g.IsHermitian)
    {s τ : ℝ} (h : OQP27.StripL3b.stripF (1 - B) g s τ ≠ 0) : |s| ≤ opNorm g := by
  have hP : OQP27.StripL3b.IsProj (1 - B) := OQP27.StripL3a.isProj_one_sub hB
  have h1 : ¬ (∀ i, s ≤ hg.eigenvalues i) := fun h' =>
    h (OQP27.StripL3b.stripF_eq_zero_of_semidef hP hg (Or.inl h'))
  have h2 : ¬ (∀ i, hg.eigenvalues i ≤ s) := fun h' =>
    h (OQP27.StripL3b.stripF_eq_zero_of_semidef hP hg (Or.inr h'))
  simp only [not_forall, not_le] at h1 h2
  obtain ⟨i, hi⟩ := h1
  obtain ⟨j, hj⟩ := h2
  have hi' := abs_eigenvalues_le_opNorm hg i
  have hj' := abs_eigenvalues_le_opNorm hg j
  rw [abs_le]
  constructor
  · linarith [neg_abs_le (hg.eigenvalues i)]
  · linarith [le_abs_self (hg.eigenvalues j)]

/-- **The quantitative lower bound on the defect** (THEOREMS.md, Theorem C, `spec B ⊆ {0,1}`):
`V(λ) ≥ (1/(2(1 + cosh(π(|λ| + ‖g‖))))) · (2/π) · ‖BgP‖_F²`. -/
theorem stripBalayage_ge_proj (hB : B.IsHermitian ∧ B * B = B) (hg : g.IsHermitian) (lam : ℝ) :
    1 / (2 * (1 + Real.cosh (π * (|lam| + opNorm g))))
        * (2 / π * ∑ i, ∑ j, ‖(B * g * (1 - B)) i j‖ ^ 2)
      ≤ OQP27.StripL3a.stripBalayage (OQP27.StripL3b.stripF (1 - B) g) lam := by
  have hP : OQP27.StripL3b.IsProj (1 - B) := OQP27.StripL3a.isProj_one_sub hB
  set F := OQP27.StripL3b.stripF (1 - B) g with hFdef
  have hF : OQP27.StripL3a.DensityReg F :=
    OQP27.StripL3a.densityReg_stripF (OQP27.StripL3b.hyp_RI M) hB hg
  set R := |lam| + opNorm g with hR
  set c := 1 / (2 * (1 + Real.cosh (π * R))) with hc
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hsin := integral_sin_mul_stripF hP hg
  rw [sub_sub_cancel] at hsin
  rw [← hsin, ← integral_const_mul, hF.stripBalayage_eq]
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
    ≤ OQP27.StripL3a.stripKernel (1 - q.2) (q.1 - lam) * F q.1 q.2
  by_cases hq : F q.1 q.2 = 0
  · rw [hq, mul_zero, mul_zero, mul_zero]
  · have hτ : 0 < q.2 ∧ q.2 < 1 := by
      by_contra hτ
      exact hq (hF.zero_of_not_mem _ _ hτ)
    have hs : |q.1| ≤ opNorm g := abs_le_opNorm_of_stripF_ne_zero hB hg hq
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
      _ ≤ OQP27.StripL3a.stripKernel (1 - q.2) (q.1 - lam) * F q.1 q.2 :=
          mul_le_mul_of_nonneg_right hK hFn

/-- **Theorem C, projection case** (THEOREMS.md, Section 1, Theorem C, the display for a
projection `B`): for every real `λ`,
`Σ_{ν ∈ spec(B+ig)} h_λ(ν) - Tr[(P(g-λ)P)_+] ≥ ‖[B,g]‖_F² / (2π(1 + cosh(π(|λ| + ‖g‖))))`. -/
theorem theoremC_proj (hB : B.IsHermitian ∧ B * B = B) (hg : g.IsHermitian) (lam : ℝ) :
    frobNorm (B * g - g * B) ^ 2 / (2 * π * (1 + Real.cosh (π * (|lam| + opNorm g))))
      ≤ ((B + I • g).charpoly.roots.map (OQP27.StripL3a.hLam lam)).sum
        - OQP27.StripL3a.posPartTrace ((1 - B) * (g - (lam : ℂ) • 1) * (1 - B)) := by
  rw [OQP27.StripL3b.strip_defect_formula_noHyp hB hg lam]
  refine le_trans (le_of_eq ?_) (stripBalayage_ge_proj hB hg lam)
  rw [frobNorm_comm_sq hB hg]
  have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have hd : (1 + Real.cosh (π * (|lam| + opNorm g))) ≠ 0 := by
    have := Real.one_le_cosh (π * (|lam| + opNorm g)); linarith
  field_simp

end TheoremC

end HarmonicMajorization
