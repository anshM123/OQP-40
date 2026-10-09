import HarmonicMajorization.Duhamel
import OQP27.StripRIMain

/-!
# The `τ`-marginal of the density, projection case

Authors: Ansh Mishra, Aryan Senthilkumar.  License: MIT.

Setting: `P` an orthogonal projection on `ℂ^M`, `B = 1 - P`, `g` Hermitian, and
`F = OQP27.StripL3b.stripF P g` the density of Theorem A (`ρ(s,τ) = (1/2π) Σ |Im x_i(s,τ)|`).

Main results:
* `laplaceF_zero`: for `t ≠ 0`, `∫∫ e^{-tτ} F(s,τ) ds dτ = Tr(BgPg) (1 - e^{-t})/t`, i.e. the
  `τ`-marginal of `F` is `‖BgP‖_F² 1_{(0,1)}(τ)` in Laplace form (THEOREMS.md, Theorem A, slice
  formula, for `spec P = {0, 1}`);
* `integral_sin_mul_stripF`: `∫∫ sin(πτ) F(s,τ) ds dτ = (2/π) ‖BgP‖_F²`;
* `trace_BgPg_eq`: `Tr(BgPg) = Tr((BgP)(BgP)ᴴ)`.

Route: Duhamel's formula (`HarmonicMajorization.trace_exp_add_smul`) gives
`D(a,t) = a² (Φ_{X,g}(a) - Φ_{X,g_d}(a))` with `X = -tP`; Theorem A (`OQP27.StripL3b.theorem1_bmv2`)
gives `D(a,t) = a² L(a,t)`; both `L(·,t)` and `Φ` are continuous, so `L(0,t) = Φ_{X,g}(0) - Φ_{X,g_d}(0)`,
which is computed explicitly.  No hypotheses.
-/

set_option autoImplicit false

namespace HarmonicMajorization

open Matrix Complex MeasureTheory intervalIntegral Filter Topology
open scoped Real
open OQP27.StripL3b (IsProj pinch stripF bmvD laplaceF)

variable {M : ℕ}

section Proj

variable {P : Matrix (Fin M) (Fin M) ℂ}

/-- `e^{cP} = (1 - P) + e^c P` for a projection `P`. -/
lemma exp_smul_proj (hP : P * P = P) (c : ℂ) :
    NormedSpace.exp (c • P) = (1 - P) + cexp c • P := by
  have h1 : NormedSpace.exp (c • P) * P = cexp c • P :=
    OQP27.StripL3b.exp_mul_of_mul_eq_smul (by rw [Matrix.smul_mul, hP])
  have h2 : NormedSpace.exp (c • P) * (1 - P) = 1 - P := by
    have h := OQP27.StripL3b.exp_mul_of_mul_eq_smul (X := c • P) (V := 1 - P) (c := 0)
      (by rw [Matrix.smul_mul, OQP27.StripL3b.proj_mul_compl hP, smul_zero, zero_smul])
    simpa using h
  calc NormedSpace.exp (c • P) = NormedSpace.exp (c • P) * ((1 - P) + P) := by
        rw [sub_add_cancel, Matrix.mul_one]
    _ = (1 - P) + cexp c • P := by rw [Matrix.mul_add, h1, h2]

lemma compl_mul_compl (hP : P * P = P) : (1 - P) * (1 - P) = 1 - P := by
  rw [Matrix.sub_mul, Matrix.one_mul, OQP27.StripL3b.proj_mul_compl hP, sub_zero]

/-- `((1 - P) + x P)((1 - P) + y P) = (1 - P) + xy P`. -/
lemma proj_affine_mul (hP : P * P = P) (x y : ℂ) :
    ((1 - P) + x • P) * ((1 - P) + y • P) = (1 - P) + (x * y) • P := by
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.smul_mul, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.mul_smul, compl_mul_compl hP, OQP27.StripL3b.compl_mul_proj hP,
    OQP27.StripL3b.proj_mul_compl hP, hP, smul_zero, smul_zero, add_zero, zero_add, smul_smul]

/-- The four trace identities behind the pinching difference. -/
lemma trace_pinch_diff (hP : P * P = P) (Y : Matrix (Fin M) (Fin M) ℂ) (x y : ℂ) :
    (Y * ((1 - P) + x • P) * Y * ((1 - P) + y • P)).trace
      - (pinch P Y * ((1 - P) + x • P) * pinch P Y * ((1 - P) + y • P)).trace
      = (x + y) * ((1 - P) * Y * P * Y).trace := by
  set B := 1 - P with hB
  have hBB : B * B = B := compl_mul_compl hP
  have hBP : B * P = 0 := OQP27.StripL3b.compl_mul_proj hP
  have hPB : P * B = 0 := OQP27.StripL3b.proj_mul_compl hP
  -- expansion of the first term
  have eY : Y * (B + x • P) * Y * (B + y • P)
      = Y * B * Y * B + y • (Y * B * Y * P) + x • (Y * P * Y * B) + (x * y) • (Y * P * Y * P) := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
      Matrix.mul_assoc, smul_add]
    rw [mul_comm y x]
    abel
  -- the pinched term
  have k1 : ∀ z : ℂ, pinch P Y * (B + z • P) = B * Y * B + z • (P * Y * P) := by
    intro z
    unfold pinch
    rw [← hB]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_assoc, hBB, hBP, hPB,
      hP, Matrix.mul_zero, add_zero, zero_add]
  have eYd : pinch P Y * (B + x • P) * pinch P Y * (B + y • P)
      = B * Y * B * Y * B + (x * y) • (P * Y * P * Y * P) := by
    rw [Matrix.mul_assoc (pinch P Y * (B + x • P)), k1, k1]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    have z1 : B * (Y * (B * (P * (Y * P)))) = 0 := by
      rw [← Matrix.mul_assoc B P, hBP, Matrix.zero_mul, Matrix.mul_zero, Matrix.mul_zero]
    have z2 : P * (Y * (P * (B * (Y * B)))) = 0 := by
      rw [← Matrix.mul_assoc P B, hPB, Matrix.zero_mul, Matrix.mul_zero, Matrix.mul_zero]
    have w1 : B * (Y * (B * (B * (Y * B)))) = B * (Y * (B * (Y * B))) := by
      rw [← Matrix.mul_assoc B B, hBB]
    have w2 : P * (Y * (P * (P * (Y * P)))) = P * (Y * (P * (Y * P))) := by
      rw [← Matrix.mul_assoc P P, hP]
    rw [z1, z2, w1, w2]
    simp only [add_zero, zero_add, smul_smul, smul_zero]
    rw [mul_comm y x]
  have t1 : (B * Y * B * Y * B).trace = (Y * B * Y * B).trace := by
    have e1 : B * (B * Y * B * Y) = B * Y * B * Y := by simp only [← Matrix.mul_assoc, hBB]
    calc (B * Y * B * Y * B).trace = (B * (B * Y * B * Y)).trace := Matrix.trace_mul_comm _ _
      _ = (B * Y * B * Y).trace := by rw [e1]
      _ = (Y * (B * Y * B)).trace := Matrix.trace_mul_comm _ _
      _ = (Y * B * Y * B).trace := by simp only [Matrix.mul_assoc]
  have t2 : (P * Y * P * Y * P).trace = (Y * P * Y * P).trace := by
    have e1 : P * (P * Y * P * Y) = P * Y * P * Y := by simp only [← Matrix.mul_assoc, hP]
    calc (P * Y * P * Y * P).trace = (P * (P * Y * P * Y)).trace := Matrix.trace_mul_comm _ _
      _ = (P * Y * P * Y).trace := by rw [e1]
      _ = (Y * (P * Y * P)).trace := Matrix.trace_mul_comm _ _
      _ = (Y * P * Y * P).trace := by simp only [Matrix.mul_assoc]
  have t3 : (Y * B * Y * P).trace = (B * Y * P * Y).trace := by
    calc (Y * B * Y * P).trace = (Y * (B * Y * P)).trace := by simp only [Matrix.mul_assoc]
      _ = (B * Y * P * Y).trace := Matrix.trace_mul_comm _ _
  have t4 : (Y * P * Y * B).trace = (B * Y * P * Y).trace := by
    calc (Y * P * Y * B).trace = (B * (Y * P * Y)).trace := Matrix.trace_mul_comm _ _
      _ = (B * Y * P * Y).trace := by simp only [Matrix.mul_assoc]
  rw [eY, eYd]
  simp only [Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
  rw [t1, t2, t3, t4]
  ring

/-- The second-order kernel at `a = 0` for `X = -tP`. -/
lemma kern2_proj_zero (hP : P * P = P) (Y : Matrix (Fin M) (Fin M) ℂ) (t : ℂ) (r r' : ℝ) :
    kern2 ((-t) • P) Y 0 r r'
      = (Y * ((1 - P) + cexp (-t * (1 - r + r' * r)) • P) * Y
          * ((1 - P) + cexp (-t * ((1 - r') * r)) • P)).trace := by
  unfold kern2
  simp only [zero_smul, add_zero, smul_smul]
  rw [exp_smul_proj hP, exp_smul_proj hP, exp_smul_proj hP, Matrix.mul_assoc Y,
    proj_affine_mul hP, ← Complex.exp_add]
  congr 5
  · ring
  · ring

/-- The pinching difference of the second-order kernels at `a = 0`. -/
lemma kern2_proj_diff (hP : P * P = P) (g : Matrix (Fin M) (Fin M) ℂ) (t : ℂ) (r r' : ℝ) :
    kern2 ((-t) • P) g 0 r r' - kern2 ((-t) • P) (pinch P g) 0 r r'
      = (cexp (-t * (1 - r + r' * r)) + cexp (-t * ((1 - r') * r)))
        * ((1 - P) * g * P * g).trace := by
  rw [kern2_proj_zero hP, kern2_proj_zero hP]
  exact trace_pinch_diff hP g _ _

/-- `Tr(g e^{-tP}) = Tr(g_d e^{-tP})`. -/
lemma trace_mul_exp_pinch (hP : P * P = P) (g : Matrix (Fin M) (Fin M) ℂ) (t : ℂ) :
    (g * NormedSpace.exp ((-t) • P)).trace = (pinch P g * NormedSpace.exp ((-t) • P)).trace := by
  rw [exp_smul_proj hP]
  set B := 1 - P with hB
  have hBB : B * B = B := compl_mul_compl hP
  have hBP : B * P = 0 := OQP27.StripL3b.compl_mul_proj hP
  have hPB : P * B = 0 := OQP27.StripL3b.proj_mul_compl hP
  have e : pinch P g * (B + cexp (-t) • P) = B * g * B + cexp (-t) • (P * g * P) := by
    unfold pinch
    rw [← hB]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_assoc, hBB, hBP, hPB,
      hP, Matrix.mul_zero, add_zero, zero_add]
  rw [e, Matrix.mul_add, Matrix.trace_add, Matrix.trace_add, Matrix.mul_smul, Matrix.trace_smul,
    Matrix.trace_smul]
  congr 1
  · rw [Matrix.trace_mul_comm (B * g) B, ← Matrix.mul_assoc, hBB, Matrix.trace_mul_comm]
  · congr 1
    rw [Matrix.trace_mul_comm (P * g) P, ← Matrix.mul_assoc, hP, Matrix.trace_mul_comm]

/-- `D(a, t) = a² (Φ_{X,g}(a) - Φ_{X,g_d}(a))`, `X = -tP`. -/
theorem bmvD_eq_phi2 (hP : P * P = P) (g : Matrix (Fin M) (Fin M) ℂ) (a t : ℂ) :
    bmvD P g a t = a ^ 2 * (phi2 ((-t) • P) g a - phi2 ((-t) • P) (pinch P g) a) := by
  unfold bmvD
  have e1 : a • g - t • P = (-t) • P + a • g := by rw [neg_smul]; abel
  have e2 : a • pinch P g - t • P = (-t) • P + a • pinch P g := by rw [neg_smul]; abel
  rw [e1, e2, trace_exp_add_smul, trace_exp_add_smul, trace_mul_exp_pinch hP]
  ring

end Proj

/-! ### The explicit double integral -/

lemma hasDerivAt_cexp_affine (c d : ℂ) (r : ℝ) :
    HasDerivAt (fun r : ℝ => cexp (c * r + d)) (c * cexp (c * r + d)) r := by
  have h : HasDerivAt (fun r : ℝ => c * (r : ℂ) + d) c r := by
    have := ((hasDerivAt_id r).ofReal_comp).const_mul c
    simpa using this.add_const d
  have h2 := h.cexp
  convert h2 using 1
  ring

/-- `∫_0^1 r e^{-t(1 - r + r' r)} + r e^{-t(1-r')r} dr' = (e^{-t(1-r)} - e^{-t} + 1 - e^{-tr})/t`. -/
lemma inner_integral (t : ℂ) (ht : t ≠ 0) (r : ℝ) :
    ∫ r' in (0:ℝ)..1, (r : ℂ) * (cexp (-t * (1 - r + r' * r)) + cexp (-t * ((1 - r') * r)))
      = (cexp (-t * (1 - r)) - cexp (-t) + 1 - cexp (-t * r)) / t := by
  have hd : ∀ r' : ℝ, HasDerivAt
      (fun r' : ℝ => (-cexp (-t * r * r' + (-t * (1 - r))) + cexp (t * r * r' + (-t * r))) / t)
      ((r : ℂ) * (cexp (-t * (1 - r + r' * r)) + cexp (-t * ((1 - r') * r)))) r' := by
    intro r'
    have h1 := hasDerivAt_cexp_affine (-t * r) (-t * (1 - r)) r'
    have h2 := hasDerivAt_cexp_affine (t * r) (-t * r) r'
    have h3 := (h1.neg.add h2).div_const t
    refine h3.congr_deriv ?_
    have e1 : -t * (1 - (r : ℂ) + r' * r) = -t * r * r' + -t * (1 - r) := by ring
    have e2 : -t * ((1 - (r' : ℂ)) * r) = t * r * r' + -t * r := by ring
    rw [e1, e2]
    field_simp
  have hc : Continuous (fun r' : ℝ =>
      (r : ℂ) * (cexp (-t * (1 - r + r' * r)) + cexp (-t * ((1 - r') * r)))) := by fun_prop
  rw [integral_eq_sub_of_hasDerivAt (fun r' _ => hd r') (hc.intervalIntegrable 0 1)]
  have e3 : -t * (r : ℂ) * ((1 : ℝ) : ℂ) + -t * (1 - r) = -t := by push_cast; ring
  have e4 : t * (r : ℂ) * ((1 : ℝ) : ℂ) + -t * r = 0 := by push_cast; ring
  have e5 : -t * (r : ℂ) * ((0 : ℝ) : ℂ) + -t * (1 - r) = -t * (1 - r) := by push_cast; ring
  have e6 : t * (r : ℂ) * ((0 : ℝ) : ℂ) + -t * r = -t * r := by push_cast; ring
  simp only [e3, e4, e5, e6, Complex.exp_zero]
  field_simp
  ring_nf

/-- `J(t) = ∫_0^1 r ∫_0^1 (e^{-t(1 - r + r'r)} + e^{-t(1-r')r}) dr' dr = (1 - e^{-t})/t`. -/
lemma double_integral_J (t : ℂ) (ht : t ≠ 0) :
    ∫ r in (0:ℝ)..1, ∫ r' in (0:ℝ)..1,
        (r : ℂ) * (cexp (-t * (1 - r + r' * r)) + cexp (-t * ((1 - r') * r)))
      = (1 - cexp (-t)) / t := by
  simp_rw [inner_integral t ht]
  have hd : ∀ r : ℝ, HasDerivAt
      (fun r : ℝ => (cexp (t * r + -t) / t - cexp (-t) * r + r + cexp (-t * r + 0) / t) / t)
      ((cexp (-t * (1 - r)) - cexp (-t) + 1 - cexp (-t * r)) / t) r := by
    intro r
    have h1 := (hasDerivAt_cexp_affine t (-t) r).div_const t
    have h2 := ((hasDerivAt_id r).ofReal_comp).const_mul (cexp (-t))
    have h3 := (hasDerivAt_id r).ofReal_comp
    have h4 := (hasDerivAt_cexp_affine (-t) 0 r).div_const t
    have h5 := (((h1.sub h2).add h3).add h4).div_const t
    refine h5.congr_deriv ?_
    have e1 : -t * (1 - (r : ℂ)) = t * r + -t := by ring
    have e2 : -t * (r : ℂ) = -t * r + 0 := by ring
    rw [e1, e2]
    simp only [Complex.ofReal_one]
    field_simp
    ring
  have hc : Continuous (fun r : ℝ => (cexp (-t * (1 - r)) - cexp (-t) + 1 - cexp (-t * r)) / t) := by
    fun_prop
  rw [integral_eq_sub_of_hasDerivAt (fun r _ => hd r) (hc.intervalIntegrable 0 1)]
  simp only [Complex.ofReal_one, Complex.ofReal_zero, mul_one, mul_zero, add_zero, zero_add,
    add_neg_cancel, Complex.exp_zero]
  field_simp
  ring

section Marginal

variable {P g : Matrix (Fin M) (Fin M) ℂ}

/-- `Φ_{X,g}(0) - Φ_{X,g_d}(0) = Tr(BgPg) (1 - e^{-t})/t`. -/
lemma phi2_diff_zero (hP : P * P = P) (t : ℂ) (ht : t ≠ 0) :
    phi2 ((-t) • P) g 0 - phi2 ((-t) • P) (pinch P g) 0
      = ((1 - P) * g * P * g).trace * ((1 - cexp (-t)) / t) := by
  unfold phi2
  have hi1 := (continuous_outer2_slice ((-t) • P) g 0).intervalIntegrable (μ := volume) 0 1
  have hi2 := (continuous_outer2_slice ((-t) • P) (pinch P g) 0).intervalIntegrable
    (μ := volume) 0 1
  rw [← intervalIntegral.integral_sub hi1 hi2]
  have hin : ∀ r : ℝ, (r : ℂ) * (∫ r' in (0:ℝ)..1, kern2 ((-t) • P) g 0 r r')
      - (r : ℂ) * (∫ r' in (0:ℝ)..1, kern2 ((-t) • P) (pinch P g) 0 r r')
      = ((1 - P) * g * P * g).trace * ∫ r' in (0:ℝ)..1,
          (r : ℂ) * (cexp (-t * (1 - r + r' * r)) + cexp (-t * ((1 - r') * r))) := by
    intro r
    have c1 := continuous_kern2_slice ((-t) • P) g 0 r
    have c2 := continuous_kern2_slice ((-t) • P) (pinch P g) 0 r
    rw [← mul_sub, ← intervalIntegral.integral_sub (c1.intervalIntegrable 0 1)
      (c2.intervalIntegrable 0 1), ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun r' _ => ?_)
    rw [kern2_proj_diff hP g t r r']
    ring
  rw [intervalIntegral.integral_congr (fun r _ => hin r), intervalIntegral.integral_const_mul,
    double_integral_J t ht]

/-- **The `τ`-marginal in Laplace form**: for `t ≠ 0`,
`∫∫ e^{-tτ} F(s,τ) ds dτ = Tr(BgPg) (1 - e^{-t})/t`. -/
theorem laplaceF_zero (hP : IsProj P) (hg : g.IsHermitian) (t : ℂ) (ht : t ≠ 0) :
    laplaceF P g 0 t = ((1 - P) * g * P * g).trace * ((1 - cexp (-t)) / t) := by
  rw [← phi2_diff_zero hP.2 t ht]
  have hL : Continuous (fun a : ℂ => laplaceF P g a t) :=
    (OQP27.StripL3b.differentiable_laplaceF_a (OQP27.StripL3b.hyp_RI M) hP hg t).continuous
  have hΦ : Continuous (fun a : ℂ => phi2 ((-t) • P) g a - phi2 ((-t) • P) (pinch P g) a) :=
    (continuous_phi2 _ _).sub (continuous_phi2 _ _)
  have heq : ∀ a : ℂ, a ≠ 0 →
      laplaceF P g a t = phi2 ((-t) • P) g a - phi2 ((-t) • P) (pinch P g) a := by
    intro a ha
    have h1 := OQP27.StripL3b.theorem1_bmv2 hP hg a t
    rw [bmvD_eq_phi2 hP.2] at h1
    exact (mul_left_cancel₀ (pow_ne_zero 2 ha) h1).symm
  have h1 : Tendsto (fun a : ℂ => laplaceF P g a t) (𝓝[≠] 0) (𝓝 (laplaceF P g 0 t)) :=
    hL.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun a : ℂ => laplaceF P g a t) (𝓝[≠] 0)
      (𝓝 (phi2 ((-t) • P) g 0 - phi2 ((-t) • P) (pinch P g) 0)) := by
    refine (hΦ.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with a ha
    exact (heq a ha).symm
  exact tendsto_nhds_unique h1 h2

/-- `Tr(BgPg) = Tr((BgP)(BgP)ᴴ)` for Hermitian `P`, `g`. -/
lemma trace_BgPg_eq (hP : IsProj P) (hg : g.IsHermitian) :
    ((1 - P) * g * P * g).trace = (((1 - P) * g * P) * ((1 - P) * g * P)ᴴ).trace := by
  have hB : (1 - P).IsHermitian := isHermitian_one.sub hP.1
  rw [conjTranspose_mul, conjTranspose_mul, hB.eq, hg.eq, hP.1.eq]
  have e : (1 - P) * g * P * (P * (g * (1 - P))) = ((1 - P) * g * P * g) * (1 - P) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc P P, hP.2]
  rw [e, Matrix.trace_mul_comm ((1 - P) * g * P * g) (1 - P)]
  rw [← Matrix.mul_assoc (1 - P) ((1 - P) * g * P) g, ← Matrix.mul_assoc (1 - P) ((1 - P) * g) P,
    ← Matrix.mul_assoc (1 - P) (1 - P) g, compl_mul_compl hP.2]

/-- The real number `‖BgP‖_F² = Re Tr((BgP)(BgP)ᴴ) = Σ_{ij} |(BgP)_{ij}|²`. -/
lemma trace_mul_conjTranspose_eq_sum (A : Matrix (Fin M) (Fin M) ℂ) :
    (A * Aᴴ).trace = ((∑ i, ∑ j, ‖A i j‖ ^ 2 : ℝ) : ℂ) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  push_cast
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.mul_conj']

/-- **The sine moment of the density**: `∫∫ sin(πτ) F(s,τ) ds dτ = (2/π) ‖BgP‖_F²`. -/
theorem integral_sin_mul_stripF (hP : IsProj P) (hg : g.IsHermitian) :
    ∫ q : ℝ × ℝ, Real.sin (π * q.2) * stripF P g q.1 q.2
      = 2 / π * ∑ i, ∑ j, ‖((1 - P) * g * P) i j‖ ^ 2 := by
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hI : (I * π : ℂ) ≠ 0 := mul_ne_zero I_ne_zero hpi
  have hI' : (-(I * π) : ℂ) ≠ 0 := neg_ne_zero.mpr hI
  obtain ⟨-, -, -, -, -, hint, -⟩ := OQP27.StripL3b.theorem1_package hP hg
  have hm := laplaceF_zero hP hg (-(I * π)) hI'
  have hp := laplaceF_zero hP hg (I * π) hI
  rw [trace_BgPg_eq hP hg, trace_mul_conjTranspose_eq_sum] at hm hp
  set n : ℝ := ∑ i, ∑ j, ‖((1 - P) * g * P) i j‖ ^ 2 with hn
  unfold laplaceF at hm hp
  have hexp1 : cexp (-(-(I * π))) = -1 := by
    rw [neg_neg, mul_comm, Complex.exp_pi_mul_I]
  have hexp2 : cexp (-(I * π)) = -1 := by
    rw [mul_comm, Complex.exp_neg_pi_mul_I]
  rw [hexp1] at hm
  rw [hexp2] at hp
  have hsub := congrArg₂ (· - ·) hm hp
  rw [← integral_sub (hint 0 (-(I * π))) (hint 0 (I * π))] at hsub
  have hfun : ∀ q : ℝ × ℝ, cexp (0 * q.1 - -(I * π) * q.2) * (stripF P g q.1 q.2 : ℂ)
      - cexp (0 * q.1 - I * π * q.2) * (stripF P g q.1 q.2 : ℂ)
      = (2 * I) * ((Real.sin (π * q.2) * stripF P g q.1 q.2 : ℝ) : ℂ) := by
    intro q
    have hs : ((Real.sin (π * q.2) : ℝ) : ℂ) * (2 * I)
        = cexp (I * π * q.2) - cexp (-(I * π * q.2)) := by
      rw [Complex.ofReal_sin, Complex.sin]
      push_cast
      have e1 : -((π : ℂ) * q.2) * I = -(I * π * q.2) := by ring
      have e2 : ((π : ℂ) * q.2) * I = I * π * q.2 := by ring
      rw [e1, e2]
      ring_nf
      rw [Complex.I_sq]
      ring
    have e1 : (0 : ℂ) * q.1 - -(I * π) * q.2 = I * π * q.2 := by ring
    have e2 : (0 : ℂ) * q.1 - I * π * q.2 = -(I * π * q.2) := by ring
    rw [e1, e2, Complex.ofReal_mul, ← sub_mul, ← hs]
    ring
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hfun),
    MeasureTheory.integral_const_mul, integral_complex_ofReal] at hsub
  have hval : (2 * I) * ((∫ q : ℝ × ℝ, Real.sin (π * q.2) * stripF P g q.1 q.2 : ℝ) : ℂ)
      = (2 * I) * ((2 / π * n : ℝ) : ℂ) := by
    rw [hsub]
    push_cast
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
  have h2I : (2 * I : ℂ) ≠ 0 := mul_ne_zero two_ne_zero I_ne_zero
  exact_mod_cast mul_left_cancel₀ h2I hval

end Marginal

end HarmonicMajorization
