import HarmonicMajorization.MarginalGen
import HarmonicMajorization.PoissonGen

/-!
# Theorem B (harmonic pinching theorem) for general `0 ≤ B ≤ 1`

Authors: Ansh Mishra, Aryan Senthilkumar.  License: MIT.

Setting (THEOREMS.md, Section 0): `B` with `0 ≤ B ≤ 1` (`B.PosSemidef`, `(1 - B).PosSemidef`),
`P = 1 - B`, `g` Hermitian, `g_d = pinchH hP g` the pinching onto the eigenspaces of `P` (the same as
those of `B`), `ρ = rhoG (1 - B) g`, and the defect `V(λ) = ∫_0^1 ∫ K_{1-τ}(s - λ) ρ(s,τ) ds dτ`
(`OQP27.StripL3a.stripBalayage`).  The left sweep of a multiset `Z` in the closed strip, evaluated
against `(w - λ)_+`, is `Σ_{ν ∈ Z} h_λ(ν)` (`OQP27.StripL3a.hLam`).

Main results:
* `mass_moment_gen` (no hypothesis): both sweeps have mass `M - Tr B` and first moment `Tr(Pg)`;
* **`theoremB_gen`** (from `Hyp_RI_gen M`, through Theorem A):
  `Σ_{ν ∈ spec(B+ig)} h_λ(ν) - Σ_{ν ∈ spec(B+ig_d)} h_λ(ν) = V(λ)`;
* `theoremB_gen_ineq`: the difference is `≥ 0`;
* `theoremB_gen_eq_iff`: equality at one `λ` iff `[B, g] = 0`.
The right edge is in `HarmonicMajorization/RightEdge.lean` (`theoremB_right`), and the versions without
hypothesis are in `HarmonicMajorization/MainGen.lean`.

Unconditional ingredients proved here: the strip location of the spectra
(`re_mem_Icc_of_mem_roots_gen`), the masses and moments, the matrix side of step (a)
(`bmvDG_sub_eq`), and the regularity `DensityRegG ρ` (`densityRegG_rhoG`).

Hypothesis used: `Hyp_RI_gen M` (the multi-line Radon identity), for Theorem A.
-/

set_option autoImplicit false

namespace HarmonicMajorization

open Matrix Complex MeasureTheory Filter Topology Set
open scoped Real ComplexOrder
open OQP27.StripL3b (pencilRoots imAbsSum)
open OQP27.StripL3a (stripKernel stripBalayage hLam sinhRatio)

variable {M : ℕ}

/-! ### The strip and the spectrum of `P` -/

/-- **The eigenvalues of `B + ig'` lie in the closed strip** for `0 ≤ B ≤ 1` and Hermitian `g'`. -/
theorem re_mem_Icc_of_mem_roots_gen {B g' : Matrix (Fin M) (Fin M) ℂ} (hB0 : B.PosSemidef)
    (hB1 : (1 - B).PosSemidef) (hg : g'.IsHermitian) {ν : ℂ}
    (hν : ν ∈ (B + I • g').charpoly.roots) : 0 ≤ ν.re ∧ ν.re ≤ 1 := by
  obtain ⟨v, hv0, hXv⟩ := OQP27.StripL3a.exists_mulVec_eq_smul_of_mem_roots hν
  have hBpos : 0 ≤ star v ⬝ᵥ (B *ᵥ v) := hB0.dotProduct_mulVec_nonneg v
  have hPpos : 0 ≤ star v ⬝ᵥ ((1 - B) *ᵥ v) := hB1.dotProduct_mulVec_nonneg v
  have hsum : star v ⬝ᵥ (B *ᵥ v) + star v ⬝ᵥ ((1 - B) *ᵥ v) = star v ⬝ᵥ v := by
    rw [← dotProduct_add, ← Matrix.add_mulVec, add_sub_cancel, Matrix.one_mulVec]
  have hgre : (star v ⬝ᵥ (g' *ᵥ v)).im = 0 := hg.im_star_dotProduct_mulVec_self v
  have hq : 0 < (star v ⬝ᵥ v).re := by
    have := (Matrix.dotProduct_star_self_pos_iff (v := v)).mpr hv0
    exact (Complex.pos_iff.mp this).1
  have hqim : (star v ⬝ᵥ v).im = 0 := by
    have := (Matrix.dotProduct_star_self_pos_iff (v := v)).mpr hv0
    exact ((Complex.pos_iff.mp this).2).symm
  have hmain : ν * (star v ⬝ᵥ v) = star v ⬝ᵥ (B *ᵥ v) + I * (star v ⬝ᵥ (g' *ᵥ v)) := by
    have h1 : star v ⬝ᵥ ((B + I • g') *ᵥ v) = ν * (star v ⬝ᵥ v) := by
      rw [hXv, dotProduct_smul, smul_eq_mul]
    rw [← h1, Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  have hre := congrArg Complex.re hmain
  simp only [Complex.mul_re, hqim, mul_zero, sub_zero, Complex.add_re, Complex.I_re, zero_mul,
    Complex.I_im, hgre, add_zero] at hre
  have hB0' := (Complex.nonneg_iff.mp hBpos).1
  have hP0 := (Complex.nonneg_iff.mp hPpos).1
  have hs := congrArg Complex.re hsum
  rw [Complex.add_re] at hs
  constructor
  · by_contra hneg
    push Not at hneg
    have : ν.re * (star v ⬝ᵥ v).re < 0 := mul_neg_of_neg_of_pos hneg hq
    linarith
  · by_contra hgt
    push Not at hgt
    have : (star v ⬝ᵥ v).re < ν.re * (star v ⬝ᵥ v).re := by nlinarith
    linarith

/-- For `0 ≤ B ≤ 1`, the spectrum of `P = 1 - B` lies in `[0, 1]`. -/
theorem spec_one_sub_subset {B : Matrix (Fin M) (Fin M) ℂ} (hB0 : B.PosSemidef)
    (hB1 : (1 - B).PosSemidef) : ∀ p ∈ spec hB1.isHermitian, 0 ≤ p ∧ p ≤ 1 := by
  intro p hp
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
  set hP := hB1.isHermitian
  set v := hP.eigenvectorBasis i with hv_def
  have hv1 : ‖v‖ = 1 := hP.eigenvectorBasis.orthonormal.1 i
  have hPv : (1 - B) *ᵥ v.ofLp = (hP.eigenvalues i : ℂ) • v.ofLp := by
    have := hP.mulVec_eigenvectorBasis i
    rw [← hv_def] at this
    rw [this]; rfl
  have hnorm : (star v.ofLp ⬝ᵥ v.ofLp).re = 1 := by
    rw [OQP27.StripL3b.re_star_dotProduct_self]
    have := EuclideanSpace.norm_eq v
    rw [hv1] at this
    have h2 : ∑ x, ‖v x‖ ^ 2 = 1 := by
      have h3 := congrArg (· ^ 2) this
      simp only [one_pow] at h3
      rw [h3, Real.sq_sqrt (by positivity)]
    exact h2
  have hBv : B *ᵥ v.ofLp = v.ofLp - (hP.eigenvalues i : ℂ) • v.ofLp := by
    have e : B *ᵥ v.ofLp = v.ofLp - (1 - B) *ᵥ v.ofLp := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_sub_cancel]
    rw [e, hPv]
  have h1 : 0 ≤ (star v.ofLp ⬝ᵥ ((1 - B) *ᵥ v.ofLp)).re :=
    (Complex.nonneg_iff.mp (hB1.dotProduct_mulVec_nonneg v.ofLp)).1
  have h2 : 0 ≤ (star v.ofLp ⬝ᵥ (B *ᵥ v.ofLp)).re :=
    (Complex.nonneg_iff.mp (hB0.dotProduct_mulVec_nonneg v.ofLp)).1
  rw [hPv, dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul, hnorm, mul_one] at h1
  rw [hBv, dotProduct_sub, dotProduct_smul, smul_eq_mul, Complex.sub_re, Complex.re_ofReal_mul,
    hnorm, mul_one] at h2
  exact ⟨h1, by linarith⟩

/-! ### Mass and first moment -/

/-- Mass and first moment of the left sweep of `spec(B + ig')`, for Hermitian `B`, `g'`:
`Σ_ν (1 - Re ν) = M - Re Tr B` and `Σ_ν (1 - Re ν) Im ν = Re (Tr g' - Tr(Bg'))`. -/
lemma mass_moment_one {B g' : Matrix (Fin M) (Fin M) ℂ} (hB : B.IsHermitian) (hg : g'.IsHermitian) :
    ((B + I • g').charpoly.roots.map (fun ν => 1 - ν.re)).sum = M - B.trace.re ∧
    ((B + I • g').charpoly.roots.map (fun ν => (1 - ν.re) * ν.im)).sum
      = (g'.trace - (B * g').trace).re := by
  set X := B + I • g' with hX
  set S := X.charpoly.roots with hS
  have h1 : S.sum = X.trace := (Matrix.trace_eq_sum_roots_charpoly X).symm
  have h2 : (S.map (fun ν => ν ^ 2)).sum = (X ^ 2).trace :=
    (OQP27.StripL3a.trace_pow_eq_sum_roots X 2).symm
  have hcard : S.card = M := OQP27.StripL3a.card_roots_charpoly X
  have hBim : B.trace.im = 0 := OQP27.StripL3a.trace_im_eq_zero hB
  have hgim : g'.trace.im = 0 := OQP27.StripL3a.trace_im_eq_zero hg
  have hggim : (g' * g').trace.im = 0 := by
    refine OQP27.StripL3a.trace_im_eq_zero ?_
    unfold IsHermitian; rw [conjTranspose_mul, hg.eq]
  have hBBim : (B * B).trace.im = 0 := by
    refine OQP27.StripL3a.trace_im_eq_zero ?_
    unfold IsHermitian; rw [conjTranspose_mul, hB.eq]
  have hBgre : (B * g').trace.im = 0 := by
    have h := Matrix.trace_conjTranspose (B * g')
    rw [conjTranspose_mul, hB.eq, hg.eq, Matrix.trace_mul_comm] at h
    exact Complex.conj_eq_iff_im.mp h.symm
  have htrX : X.trace = B.trace + I * g'.trace := by rw [hX, trace_add, trace_smul, smul_eq_mul]
  have hX2 : X ^ 2 = B * B + I • (B * g' + g' * B) - g' * g' := by
    rw [hX, pow_two, add_mul, mul_add, mul_add, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, I_mul_I, neg_one_smul, smul_add]
    abel
  have htrX2 : (X ^ 2).trace = (B * B).trace + 2 * I * (B * g').trace - (g' * g').trace := by
    rw [hX2, trace_sub, trace_add, trace_smul, trace_add, Matrix.trace_mul_comm g' B, smul_eq_mul]
    ring
  constructor
  · have e : (S.map (fun ν => 1 - ν.re)).sum = S.card - (S.map Complex.re).sum := by
      rw [Multiset.sum_map_sub]; simp
    rw [e, hcard, OQP27.StripL3a.multiset_map_re_sum, h1, htrX]
    simp [hgim]
  · have e : (S.map (fun ν => (1 - ν.re) * ν.im)).sum
        = (S.map Complex.im).sum - (S.map (fun ν => ν.re * ν.im)).sum := by
      rw [← Multiset.sum_map_sub]; congr 1; apply Multiset.map_congr rfl; intro ν _; ring
    rw [e, OQP27.StripL3a.multiset_map_im_sum, OQP27.StripL3a.multiset_map_re_mul_im, h1, h2, htrX,
      htrX2]
    simp [hBim, hgim, hggim, hBBim, hBgre]

section Pinch

variable {B g : Matrix (Fin M) (Fin M) ℂ} (hP : (1 - B).IsHermitian) (hg : g.IsHermitian)
include hP hg

omit hg in
lemma isHermitian_of_one_sub : B.IsHermitian := by
  have : B = 1 - (1 - B) := by abel
  rw [this]; exact isHermitian_one.sub hP

/-- **Equal masses and first moments** of the two sweeps: both equal `M - Tr B` and `Tr(Pg)`. -/
theorem mass_moment_gen :
    ((B + I • g).charpoly.roots.map (fun ν => 1 - ν.re)).sum
        = ((B + I • pinchH hP g).charpoly.roots.map (fun ν => 1 - ν.re)).sum ∧
    ((B + I • g).charpoly.roots.map (fun ν => (1 - ν.re) * ν.im)).sum
        = ((B + I • pinchH hP g).charpoly.roots.map (fun ν => (1 - ν.re) * ν.im)).sum := by
  have hB := isHermitian_of_one_sub hP
  have hgd := isHermitian_pinchH hP hg
  obtain ⟨m1, f1⟩ := mass_moment_one hB hg
  obtain ⟨m2, f2⟩ := mass_moment_one hB hgd
  refine ⟨by rw [m1, m2], ?_⟩
  rw [f1, f2]
  have htr : (pinchH hP g).trace = g.trace := trace_pinchH hP g
  have hBtr : (B * pinchH hP g).trace = (B * g).trace := by
    have hBf : fcalc hP (fun i => (fun x : ℝ => ((1 - x : ℝ) : ℂ)) (hP.eigenvalues i)) = B := by
      have h1 : fcalc hP (fun i => (fun x : ℝ => ((1 - x : ℝ) : ℂ)) (hP.eigenvalues i))
          = 1 - (1 - B) := by
        rw [show (fun i => (fun x : ℝ => ((1 - x : ℝ) : ℂ)) (hP.eigenvalues i))
            = (fun _ => (1 : ℂ)) - (fun i => (hP.eigenvalues i : ℂ)) by funext i; simp,
          fcalc_sub, fcalc_const, one_smul, fcalc_eigenvalues]
      rw [h1]; abel
    have h := trace_pinchH_mul_fcalc hP g (fun x : ℝ => ((1 - x : ℝ) : ℂ))
    rw [hBf] at h
    rw [Matrix.trace_mul_comm B, Matrix.trace_mul_comm B]
    exact h
  rw [htr, hBtr]

end Pinch

/-! ### The matrix side of step (a) -/

lemma exp_sub_exp_eq_sinh (κ : ℝ) (ν : ℂ) :
    cexp (κ * (1 - star ν)) - cexp (κ * (ν - 1))
      = cexp (I * κ * ν.im) * (2 * (Real.sinh (κ * (1 - ν.re)) : ℂ)) := by
  have hsinh : ∀ x : ℝ, (2 * (Real.sinh x : ℂ)) = cexp x - cexp (-x) := by
    intro x
    rw [Complex.ofReal_sinh, Complex.sinh]
    ring
  rw [hsinh, mul_sub (cexp (I * κ * ν.im)), ← Complex.exp_add, ← Complex.exp_add]
  have e1 : (κ : ℂ) * (1 - star ν) = I * κ * ν.im + ((κ * (1 - ν.re) : ℝ) : ℂ) := by
    rw [OQP27.StripL3a.star_eq_re_sub_im]; push_cast; ring
  have e2 : (κ : ℂ) * (ν - 1) = I * κ * ν.im + -((κ * (1 - ν.re) : ℝ) : ℂ) := by
    conv_lhs => rw [← Complex.re_add_im ν]
    push_cast; ring
  rw [e1, e2]

/-- `D(iκ,-κ) - D(iκ,κ) = Σ_{ν ∈ spec(B+ig)} e^{iκ Im ν} 2 sinh(κ(1 - Re ν))
- Σ_{ν ∈ spec(B+ig_d)} e^{iκ Im ν} 2 sinh(κ(1 - Re ν))`. -/
theorem bmvDG_sub_eq {B g : Matrix (Fin M) (Fin M) ℂ} (hP : (1 - B).IsHermitian)
    (hg : g.IsHermitian) (κ : ℝ) :
    bmvDG hP g (I * κ) (-(κ : ℂ)) - bmvDG hP g (I * κ) κ
      = ((B + I • g).charpoly.roots.map
          (fun ν => cexp (I * κ * ν.im) * (2 * (Real.sinh (κ * (1 - ν.re)) : ℂ)))).sum
        - ((B + I • pinchH hP g).charpoly.roots.map
          (fun ν => cexp (I * κ * ν.im) * (2 * (Real.sinh (κ * (1 - ν.re)) : ℂ)))).sum := by
  have hB := isHermitian_of_one_sub hP
  have hgd := isHermitian_pinchH hP hg
  unfold bmvDG
  rw [OQP27.StripL3a.trace_exp_left hB hg κ, OQP27.StripL3a.trace_exp_right B g κ,
    OQP27.StripL3a.trace_exp_left hB hgd κ, OQP27.StripL3a.trace_exp_right B (pinchH hP g) κ]
  have hmap : ∀ T : Multiset ℂ, (T.map (fun ν => cexp (κ * (1 - star ν)))).sum
      - (T.map (fun ν => cexp (κ * (ν - 1)))).sum
      = (T.map (fun ν => cexp (I * κ * ν.im) * (2 * (Real.sinh (κ * (1 - ν.re)) : ℂ)))).sum := by
    intro T
    rw [← Multiset.sum_map_sub]
    congr 1
    exact Multiset.map_congr rfl (fun ν _ => exp_sub_exp_eq_sinh κ ν)
  rw [← hmap, ← hmap]
  ring

/-! ### Regularity of the density -/

/-- The density of Theorem A satisfies `DensityRegG` (for `spec P ⊆ [0,1]`). -/
theorem densityRegG_rhoG {P g : Matrix (Fin M) (Fin M) ℂ} (hP : P.IsHermitian) (hg : g.IsHermitian)
    (hspec : ∀ p ∈ spec hP, 0 ≤ p ∧ p ≤ 1) : DensityRegG (rhoG P g) := by
  obtain ⟨C, hC0, hC⟩ := rhoG_le_domG hP hg
  exact ⟨measurable_rhoG hP g, rhoG_nonneg P g,
    fun s τ hτ => rhoG_eq_zero_of_not_mem_Ioo hP hg hspec hτ s, rhoG_support hP hg,
    ⟨fun τ => C * domG hP τ, (integrable_domG hP).const_mul C,
      fun τ => mul_nonneg hC0 (domG_nonneg hP τ), hC⟩⟩

/-! ### Theorem B -/

section TheoremB

variable {B g : Matrix (Fin M) (Fin M) ℂ} (hB0 : B.PosSemidef) (hB1 : (1 - B).PosSemidef)
  (hg : g.IsHermitian)
include hB0 hB1 hg

/-- Step (a): `ρ̂ - σ̂ = -κ² ∫∫ e^{iκs} sinh(κτ)/sinh κ ρ(s,τ)` (from Theorem A at `(iκ, ∓κ)`). -/
lemma rhohat_sub_sigmahat_gen (hRI : Hyp_RI_gen M) {κ : ℝ} (hκ : κ ≠ 0) :
    ((B + I • g).charpoly.roots.map (fun ν => cexp (I * κ * ν.im) * (sinhRatio ν.re κ : ℂ))).sum
        - ((B + I • pinchH hB1.isHermitian g).charpoly.roots.map
          (fun ν => cexp (I * κ * ν.im) * (sinhRatio ν.re κ : ℂ))).sum
      = -(κ : ℂ) ^ 2 * ∫ q : ℝ × ℝ,
          cexp (I * κ * q.1) * (sinhRatio (1 - q.2) κ : ℂ) * (rhoG (1 - B) g q.1 q.2 : ℂ) := by
  set hP := hB1.isHermitian
  have hspec := spec_one_sub_subset hB0 hB1
  have hs : (Real.sinh κ : ℂ) ≠ 0 := by
    have : Real.sinh κ ≠ 0 := by simpa using hκ
    exact_mod_cast this
  have hint := integrable_laplaceG_integrand hP hg hspec hRI
  have h1 := theoremA_gen hP hg hspec hRI (I * κ) (-(κ : ℂ))
  have h2 := theoremA_gen hP hg hspec hRI (I * κ) κ
  have hD := bmvDG_sub_eq hP hg κ
  rw [h1, h2] at hD
  unfold laplaceG at hD
  rw [← mul_sub, ← integral_sub (hint _ _) (hint _ _)] at hD
  have hint2 : ∀ q : ℝ × ℝ, cexp (I * κ * q.1 - -(κ : ℂ) * q.2) * (rhoG (1 - B) g q.1 q.2 : ℂ)
      - cexp (I * κ * q.1 - (κ : ℂ) * q.2) * (rhoG (1 - B) g q.1 q.2 : ℂ)
      = (2 * (Real.sinh κ : ℂ)) * (cexp (I * κ * q.1) * (sinhRatio (1 - q.2) κ : ℂ)
          * (rhoG (1 - B) g q.1 q.2 : ℂ)) := by
    intro q
    have e1 : (2 * (Real.sinh κ : ℂ)) * (sinhRatio (1 - q.2) κ : ℂ)
        = 2 * (Real.sinh (κ * q.2) : ℂ) := by
      have := OQP27.StripL3a.sinh_mul_one_sub_eq hκ (1 - q.2)
      rw [show κ * (1 - (1 - q.2)) = κ * q.2 by ring] at this
      rw [this]; push_cast; ring
    have e2 : 2 * (Real.sinh (κ * q.2) : ℂ) = cexp (κ * q.2) - cexp (-(κ * q.2)) := by
      rw [Complex.ofReal_sinh, Complex.sinh]; push_cast; ring
    have e3 : cexp (I * κ * q.1 - -(κ : ℂ) * q.2) = cexp (I * κ * q.1) * cexp (κ * q.2) := by
      rw [← Complex.exp_add]; ring_nf
    have e4 : cexp (I * κ * q.1 - (κ : ℂ) * q.2) = cexp (I * κ * q.1) * cexp (-(κ * q.2)) := by
      rw [← Complex.exp_add]; ring_nf
    calc cexp (I * κ * q.1 - -(κ : ℂ) * q.2) * (rhoG (1 - B) g q.1 q.2 : ℂ)
          - cexp (I * κ * q.1 - (κ : ℂ) * q.2) * (rhoG (1 - B) g q.1 q.2 : ℂ)
        = cexp (I * κ * q.1) * (cexp (κ * q.2) - cexp (-(κ * q.2)))
            * (rhoG (1 - B) g q.1 q.2 : ℂ) := by rw [e3, e4]; ring
      _ = cexp (I * κ * q.1) * ((2 * (Real.sinh κ : ℂ)) * (sinhRatio (1 - q.2) κ : ℂ))
            * (rhoG (1 - B) g q.1 q.2 : ℂ) := by rw [e1, e2]
      _ = _ := by ring
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hint2),
    integral_const_mul] at hD
  have hmat : ∀ T : Multiset ℂ, (T.map
      (fun ν => cexp (I * κ * ν.im) * (2 * (Real.sinh (κ * (1 - ν.re)) : ℂ)))).sum
      = (2 * (Real.sinh κ : ℂ)) * (T.map
          (fun ν => cexp (I * κ * ν.im) * (sinhRatio ν.re κ : ℂ))).sum := by
    intro T
    rw [← Multiset.sum_map_mul_left]
    congr 1
    refine Multiset.map_congr rfl (fun ν _ => ?_)
    rw [OQP27.StripL3a.sinh_mul_one_sub_eq hκ]; push_cast; ring
  rw [hmat, hmat] at hD
  have h2s : (2 * (Real.sinh κ : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero hs
  apply mul_left_cancel₀ h2s
  rw [mul_sub, ← hD, mul_pow, Complex.I_sq]
  push_cast
  ring

/-- **Theorem B (left edge), the exact defect**: for every real `λ`,
`Σ_{ν ∈ spec(B+ig)} h_λ(ν) - Σ_{ν ∈ spec(B+ig_d)} h_λ(ν) = V(λ)`. -/
theorem theoremB_gen (hRI : Hyp_RI_gen M) (lam : ℝ) :
    ((B + I • g).charpoly.roots.map (hLam lam)).sum
      - ((B + I • pinchH hB1.isHermitian g).charpoly.roots.map (hLam lam)).sum
      = stripBalayage (rhoG (1 - B) g) lam := by
  set hP := hB1.isHermitian
  have hspec := spec_one_sub_subset hB0 hB1
  have hF := densityRegG_rhoG hP hg hspec
  set S := (B + I • g).charpoly.roots with hSdef
  set S₀ := (B + I • pinchH hP g).charpoly.roots with hS₀def
  have hS : ∀ ν ∈ S, 0 ≤ ν.re ∧ ν.re ≤ 1 := fun ν hν => re_mem_Icc_of_mem_roots_gen hB0 hB1 hg hν
  have hS₀ : ∀ ν ∈ S₀, 0 ≤ ν.re ∧ ν.re ≤ 1 := fun ν hν =>
    re_mem_Icc_of_mem_roots_gen hB0 hB1 (isHermitian_pinchH hP hg) hν
  obtain ⟨hmass, hmom⟩ := mass_moment_gen hP hg
  have hL : ∀ lam' : ℝ, (S.map (hLam lam')).sum - (S₀.map (hLam lam')).sum
      = poissonDefect2 S S₀ lam' := fun lam' => rfl
  rw [hL]
  have hΨ : poissonDefect2 S S₀ = rampDefect2 S S₀ :=
    funext (poissonDefect2_eq_rampDefect2 S S₀ hS hS₀ hmass hmom)
  have hV : stripBalayage (rhoG (1 - B) g) = OQP27.StripL3a.balayageProd (rhoG (1 - B) g) :=
    funext hF.stripBalayage_eq
  have key : (fun w : ℝ => ((poissonDefect2 S S₀ w - stripBalayage (rhoG (1 - B) g) w : ℝ) : ℂ))
      = 0 := by
    apply OQP27.StripL3a.eq_zero_of_fourier_eq_zero
    · exact Complex.continuous_ofReal.comp
        ((continuous_poissonDefect2 S S₀).sub hF.continuous_stripBalayage)
    · rw [hΨ, hV]
      exact ((integrable_rampDefect2 S S₀).sub hF.integrable_balayageProd).ofReal
    · intro κ hκ
      have hbdd : ∀ G : ℝ → ℂ, Integrable G →
          Integrable (fun w : ℝ => cexp (I * κ * w) * G w) := by
        intro G hG
        refine hG.bdd_mul (c := 1)
          ((by fun_prop : Continuous fun w : ℝ => cexp (I * κ * w)).aestronglyMeasurable)
          (Eventually.of_forall fun w => ?_)
        rw [Complex.norm_exp]; simp
      have e : (fun w : ℝ => cexp (I * κ * w)
          * (((poissonDefect2 S S₀ w - stripBalayage (rhoG (1 - B) g) w : ℝ)) : ℂ))
          = fun w : ℝ => cexp (I * κ * w) * (rampDefect2 S S₀ w : ℂ)
              - cexp (I * κ * w) * (OQP27.StripL3a.balayageProd (rhoG (1 - B) g) w : ℂ) := by
        funext w; rw [hΨ, hV]; push_cast; ring
      have i1 : Integrable (fun w : ℝ => cexp (I * κ * w) * (rampDefect2 S S₀ w : ℂ)) :=
        hbdd _ (integrable_rampDefect2 S S₀).ofReal
      have i2 : Integrable (fun w : ℝ => cexp (I * κ * w)
          * (OQP27.StripL3a.balayageProd (rhoG (1 - B) g) w : ℂ)) :=
        hbdd _ hF.integrable_balayageProd.ofReal
      rw [e, integral_sub i1 i2, fourier_rampDefect2 S S₀ hS hS₀ hmass hmom hκ,
        hF.fourier_balayageProd hκ, rhohat_sub_sigmahat_gen hB0 hB1 hg hRI hκ]
      have hκ' : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ
      field_simp
      ring
  have h := congrFun key lam
  simp only [Pi.zero_apply, Complex.ofReal_eq_zero, sub_eq_zero] at h
  exact h

/-- **Theorem B (left edge), the inequality**: `Σ_{spec(B+ig_d)} h_λ ≤ Σ_{spec(B+ig)} h_λ`. -/
theorem theoremB_gen_ineq (hRI : Hyp_RI_gen M) (lam : ℝ) :
    ((B + I • pinchH hB1.isHermitian g).charpoly.roots.map (hLam lam)).sum
      ≤ ((B + I • g).charpoly.roots.map (hLam lam)).sum := by
  have h := theoremB_gen hB0 hB1 hg hRI lam
  have h0 := (densityRegG_rhoG hB1.isHermitian hg (spec_one_sub_subset hB0 hB1)).stripBalayage_nonneg
    lam
  linarith

end TheoremB

/-! ### The equality case -/

section Equality

variable {P g : Matrix (Fin M) (Fin M) ℂ} (hP : P.IsHermitian) (hg : g.IsHermitian)
include hP hg

omit hg in
/-- `g = Σ_{p,q} Q_p g Q_q`. -/
lemma eq_sum_sandwich :
    g = ∑ p ∈ spec hP, ∑ q ∈ spec hP, sproj hP p * g * sproj hP q := by
  conv_lhs => rw [← Matrix.one_mul g, ← Matrix.mul_one (1 * g), ← sum_sproj hP]
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Matrix.mul_sum]

omit hg in
/-- If all off-diagonal blocks vanish, `g` commutes with `P`. -/
lemma commute_of_offdiag_zero (h : ∀ p ∈ spec hP, ∀ q ∈ spec hP, p ≠ q → sproj hP p * g * sproj hP q = 0) :
    Commute P g := by
  have hg' : g = ∑ p ∈ spec hP, sproj hP p * g * sproj hP p := by
    calc g = ∑ p ∈ spec hP, ∑ q ∈ spec hP, sproj hP p * g * sproj hP q := eq_sum_sandwich hP
      _ = ∑ p ∈ spec hP, sproj hP p * g * sproj hP p := Finset.sum_congr rfl fun p hp => by
          rw [Finset.sum_eq_single p (fun q hq hqp => h p hp q hq (Ne.symm hqp))
            (fun hp' => absurd hp hp')]
  show P * g = g * P
  rw [hg', Matrix.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hL : P * (sproj hP p * g * sproj hP p) = (p : ℂ) • (sproj hP p * g * sproj hP p) := by
    rw [show P * (sproj hP p * g * sproj hP p) = (P * sproj hP p) * g * sproj hP p by
        simp only [Matrix.mul_assoc], P_mul_sproj, Matrix.smul_mul, Matrix.smul_mul]
  have hR : (sproj hP p * g * sproj hP p) * P = (p : ℂ) • (sproj hP p * g * sproj hP p) := by
    rw [show (sproj hP p * g * sproj hP p) * P = (sproj hP p * g) * (sproj hP p * P) by
        simp only [Matrix.mul_assoc], sproj_mul_P, Matrix.mul_smul]
  rw [hL, hR]

omit hg in
/-- If `g` commutes with `P`, all off-diagonal blocks vanish. -/
lemma offdiag_zero_of_commute (hc : Commute P g) {p q : ℝ} (hpq : p ≠ q) :
    sproj hP p * g * sproj hP q = 0 := by
  have h1 : sproj hP p * (P * g) * sproj hP q = (p : ℂ) • (sproj hP p * g * sproj hP q) := by
    rw [show sproj hP p * (P * g) * sproj hP q = (sproj hP p * P) * g * sproj hP q by
        simp only [Matrix.mul_assoc], sproj_mul_P, Matrix.smul_mul, Matrix.smul_mul]
  have h2 : sproj hP p * (g * P) * sproj hP q = (q : ℂ) • (sproj hP p * g * sproj hP q) := by
    rw [show sproj hP p * (g * P) * sproj hP q = sproj hP p * g * (P * sproj hP q) by
        simp only [Matrix.mul_assoc], P_mul_sproj, Matrix.mul_smul]
  have h3 : ((p : ℂ) - q) • (sproj hP p * g * sproj hP q) = 0 := by
    rw [sub_smul, ← h1, ← h2, hc.eq, sub_self]
  have hne : ((p : ℂ) - q) ≠ 0 := by
    rw [sub_ne_zero, Ne, Complex.ofReal_inj]; exact hpq
  exact (smul_eq_zero.mp h3).resolve_left hne

omit hg in
/-- If `g` commutes with `P`, then `g` equals its pinching. -/
lemma pinchH_eq_self_of_commute (hc : Commute P g) : pinchH hP g = g := by
  have e : g = ∑ p ∈ spec hP, ∑ q ∈ spec hP, sproj hP p * g * sproj hP q := by
    conv_lhs => rw [← Matrix.one_mul g, ← Matrix.mul_one (1 * g), ← sum_sproj hP]
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Matrix.mul_sum]
  conv_rhs => rw [e]
  unfold pinchH
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.sum_eq_single p]
  · intro q _ hqp; exact offdiag_zero_of_commute hP hc (Ne.symm hqp)
  · intro hp'; exact absurd hp hp'

/-- If `g` commutes with `P`, the density vanishes. -/
lemma rhoG_eq_zero_of_commute (hc : Commute P g) (s τ : ℝ) : rhoG P g s τ = 0 := by
  unfold rhoG
  by_cases hτ : τ ∈ spec hP
  · rw [imAbsSum_pencilRoots_of_mem_spec hP hτ, zero_div]
  · have hH := isHermitian_g_sub hg s
    have hpin : pinchH hP (g - (s : ℂ) • 1) = g - (s : ℂ) • 1 := by
      rw [pinchH_sub, pinchH_smul, pinchH_one, pinchH_eq_self_of_commute hP hc]
    have hherm := isHermitian_inv_mul_pinchH hP hH hτ
    rw [hpin] at hherm
    unfold pencilRoots imAbsSum
    rw [hherm.roots_charpoly_eq_eigenvalues, Multiset.map_map]
    simp

end Equality

section TheoremBEq

variable {B g : Matrix (Fin M) (Fin M) ℂ} (hB0 : B.PosSemidef) (hB1 : (1 - B).PosSemidef)
  (hg : g.IsHermitian)
include hB0 hB1 hg

/-- **Theorem B, equality case**: equality at one `λ` iff `[B, g] = 0`. -/
theorem theoremB_gen_eq_iff (hRI : Hyp_RI_gen M) (lam : ℝ) :
    ((B + I • g).charpoly.roots.map (hLam lam)).sum
        = ((B + I • pinchH hB1.isHermitian g).charpoly.roots.map (hLam lam)).sum
      ↔ Commute B g := by
  set hP := hB1.isHermitian
  have hspec := spec_one_sub_subset hB0 hB1
  have hF := densityRegG_rhoG hP hg hspec
  have hdef := theoremB_gen hB0 hB1 hg hRI lam
  have hcommP : Commute B g ↔ Commute (1 - B) g := by
    constructor
    · intro h; exact (Commute.one_left g).sub_left h
    · intro h
      have : B = 1 - (1 - B) := by abel
      rw [this]; exact (Commute.one_left g).sub_left h
  rw [hcommP]
  constructor
  · intro heq
    have hV : stripBalayage (rhoG (1 - B) g) lam = 0 := by linarith
    have hae := hF.ae_zero_of_stripBalayage_eq_zero hV
    -- `∫∫ e^{-τ} ρ = 0`, hence all off-diagonal blocks vanish
    have hL : laplaceG (1 - B) g 0 1 = 0 := by
      unfold laplaceG
      apply integral_eq_zero_of_ae
      filter_upwards [hae] with q hq
      simp only [Pi.zero_apply] at hq ⊢
      rw [hq, Complex.ofReal_zero, mul_zero]
    rw [laplaceG_zero hP hg hspec hRI 1 one_ne_zero] at hL
    apply commute_of_offdiag_zero hP
    -- each term of the sum is a nonnegative real number
    have hterm : ∀ p ∈ spec hP, ∀ q ∈ spec hP,
        (if p < q then (g * sproj hP p * g * sproj hP q).trace
          * ((cexp (-1 * p) - cexp (-1 * q)) / (1 * ((q : ℂ) - p))) else 0)
        = (((if p < q then (∑ i, ∑ j, ‖(sproj hP q * g * sproj hP p) i j‖ ^ 2)
            * ((Real.exp (-p) - Real.exp (-q)) / (q - p)) else 0) : ℝ) : ℂ) := by
      intro p _ q _
      split_ifs
      · rw [trace_sandwich_eq_frob hP hg]
        push_cast
        ring_nf
      · simp
    rw [Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun q hq => hterm p hp q hq] at hL
    simp only [← Complex.ofReal_sum, Complex.ofReal_eq_zero] at hL
    have hnn : ∀ p ∈ spec hP, ∀ q ∈ spec hP, 0 ≤ (if p < q then
        (∑ i, ∑ j, ‖(sproj hP q * g * sproj hP p) i j‖ ^ 2)
          * ((Real.exp (-p) - Real.exp (-q)) / (q - p)) else 0) := by
      intro p _ q _
      split_ifs with hpq
      · refine mul_nonneg (by positivity) (div_nonneg ?_ (by linarith))
        rw [sub_nonneg]; exact Real.exp_le_exp.mpr (by linarith)
      · exact le_rfl
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun p hp =>
      Finset.sum_nonneg (fun q hq => hnn p hp q hq))).mp hL
    have hblock : ∀ p ∈ spec hP, ∀ q ∈ spec hP, p < q → sproj hP q * g * sproj hP p = 0 := by
      intro p hp q hq hpq
      have h1 := (Finset.sum_eq_zero_iff_of_nonneg (hnn p hp)).mp (hzero p hp) q hq
      rw [if_pos hpq] at h1
      have hpos : 0 < (Real.exp (-p) - Real.exp (-q)) / (q - p) := by
        refine div_pos ?_ (by linarith)
        rw [sub_pos]; exact Real.exp_lt_exp.mpr (by linarith)
      have h2 : ∑ i, ∑ j, ‖(sproj hP q * g * sproj hP p) i j‖ ^ 2 = 0 := by
        rcases mul_eq_zero.mp h1 with h | h
        · exact h
        · exact absurd h hpos.ne'
      ext i j
      have h3 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg
        (fun j _ => by positivity))).mp h2 i (Finset.mem_univ i)
      have h4 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by positivity)).mp h3 j
        (Finset.mem_univ j)
      simpa using h4
    intro p hp q hq hpq
    rcases lt_or_gt_of_ne hpq with h | h
    · -- `p < q`: use the adjoint of the block `Q_q g Q_p`
      have hb := hblock p hp q hq h
      have := congrArg conjTranspose hb
      rw [conjTranspose_mul, conjTranspose_mul, (isHermitian_sproj hP p).eq, hg.eq,
        (isHermitian_sproj hP q).eq, conjTranspose_zero, ← Matrix.mul_assoc] at this
      exact this
    · exact hblock q hq p hp h
  · intro hc
    have hρ : (fun q : ℝ × ℝ => rhoG (1 - B) g q.1 q.2) =ᵐ[volume] 0 :=
      Eventually.of_forall fun q => rhoG_eq_zero_of_commute hP hg hc q.1 q.2
    have hV := hF.stripBalayage_eq_zero_of_ae hρ lam
    linarith

end TheoremBEq

end HarmonicMajorization
