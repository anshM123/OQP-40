import HarmonicMajorization.TheoremAGen
import HarmonicMajorization.Duhamel

/-!
# The `τ`-marginal of the density, general `B`

Authors: Ansh Mishra, Aryan Senthilkumar.  License: MIT.

Setting: `P` Hermitian with `spec P ⊆ [0,1]`, spectral projections `Q_p` (`sproj hP p`), `g`
Hermitian, `ρ = rhoG P g`.  With `w_{pq} = Tr(g Q_p g Q_q) = ‖Q_p g Q_q‖_F²`:

* `bmvDG_eq_phi2`: `D(a, t) = a² (Φ_{X,g}(a) - Φ_{X,g_d}(a))`, `X = -tP` (Duhamel);
* `phi2G_diff_zero`: `Φ_{X,g}(0) - Φ_{X,g_d}(0) = Σ_{p<q} w_{pq} (e^{-tp} - e^{-tq})/(t(q - p))`;
* `laplaceG_zero` (from `Hyp_RI_gen M`): `∫∫ e^{-tτ} ρ = Σ_{p<q} w_{pq} (e^{-tp} - e^{-tq})/(t(q-p))`,
  `t ≠ 0` — the Laplace form of the slice formula of Theorem A,
  `∫ ρ(s,τ) ds = Σ_{p<q} w_{pq}/(q - p) 1[p < τ < q]`;
* `integral_sin_mul_rhoG` (from `Hyp_RI_gen M`):
  `∫∫ sin(πτ) ρ = Σ_{p<q} w_{pq} (cos πp - cos πq)/(π(q - p))`.

Hypothesis used: `Hyp_RI_gen M` (through Theorem A).
-/

set_option autoImplicit false

namespace HarmonicMajorization

open Matrix Complex MeasureTheory intervalIntegral Filter Topology
open scoped Real
open OQP27.StripL3b (pencilRoots imAbsSum)

variable {M : ℕ}

section Kernel

variable {P : Matrix (Fin M) (Fin M) ℂ} (hP : P.IsHermitian)
include hP

/-- `Tr(Y φ(x∘λ) Y φ(y∘λ)) = Σ_{p,q} x(p) y(q) Tr(Y Q_p Y Q_q)`. -/
lemma trace_fcalc_sandwich (Y : Matrix (Fin M) (Fin M) ℂ) (x y : ℝ → ℂ) :
    (Y * fcalc hP (fun i => x (hP.eigenvalues i)) * Y * fcalc hP (fun i => y (hP.eigenvalues i))).trace
      = ∑ p ∈ spec hP, ∑ q ∈ spec hP, x p * y q * (Y * sproj hP p * Y * sproj hP q).trace := by
  rw [fcalc_comp, fcalc_comp]
  simp only [Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_sum,
    Matrix.trace_smul, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  ring

/-- For the pinching: `Tr(Y_d Q_p Y_d Q_q) = δ_{pq} Tr(Y Q_p Y Q_p)`. -/
lemma trace_pinchH_sandwich (Y : Matrix (Fin M) (Fin M) ℂ) {p q : ℝ} (hp : p ∈ spec hP)
    (hq : q ∈ spec hP) :
    (pinchH hP Y * sproj hP p * pinchH hP Y * sproj hP q).trace
      = if p = q then (Y * sproj hP p * Y * sproj hP p).trace else 0 := by
  have e : pinchH hP Y * sproj hP p * pinchH hP Y * sproj hP q
      = (sproj hP p * Y * sproj hP p) * (sproj hP q * Y * sproj hP q) := by
    rw [pinchH_mul_sproj hP Y hp, Matrix.mul_assoc _ (pinchH hP Y), pinchH_mul_sproj hP Y hq]
  rw [e]
  split_ifs with hpq
  · subst hpq
    have e2 : sproj hP p * Y * sproj hP p * (sproj hP p * Y * sproj hP p)
        = sproj hP p * (Y * sproj hP p * Y * sproj hP p) := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (sproj hP p) (sproj hP p), sproj_mul_self]
    rw [e2, Matrix.trace_mul_comm, Matrix.mul_assoc, sproj_mul_self]
  · have e2 : sproj hP p * Y * sproj hP p * (sproj hP q * Y * sproj hP q) = 0 := by
      rw [show sproj hP p * Y * sproj hP p * (sproj hP q * Y * sproj hP q)
          = sproj hP p * Y * (sproj hP p * sproj hP q) * Y * sproj hP q by simp only [Matrix.mul_assoc],
        sproj_mul_of_ne hP hpq]
      simp
    rw [e2, Matrix.trace_zero]

/-- The pinching difference of the sandwich traces. -/
lemma trace_sandwich_diff (Y : Matrix (Fin M) (Fin M) ℂ) (x y : ℝ → ℂ) :
    (Y * fcalc hP (fun i => x (hP.eigenvalues i)) * Y * fcalc hP (fun i => y (hP.eigenvalues i))).trace
      - (pinchH hP Y * fcalc hP (fun i => x (hP.eigenvalues i)) * pinchH hP Y
          * fcalc hP (fun i => y (hP.eigenvalues i))).trace
      = ∑ p ∈ spec hP, ∑ q ∈ spec hP,
          if p = q then 0 else x p * y q * (Y * sproj hP p * Y * sproj hP q).trace := by
  rw [trace_fcalc_sandwich, trace_fcalc_sandwich, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [trace_pinchH_sandwich hP Y hp hq]
  split_ifs with hpq
  · subst hpq; ring
  · ring

/-- `e^{c P} = φ(e^{cλ})`, in the form used for the Duhamel kernel. -/
lemma kern2G_zero (Y : Matrix (Fin M) (Fin M) ℂ) (t : ℂ) (r r' : ℝ) :
    kern2 ((-t) • P) Y 0 r r'
      = (Y * fcalc hP (fun i => cexp (-t * (1 - r + r' * r) * hP.eigenvalues i))
          * Y * fcalc hP (fun i => cexp (-t * ((1 - r') * r) * hP.eigenvalues i))).trace := by
  unfold kern2
  simp only [zero_smul, add_zero, smul_smul]
  rw [exp_smul_eq_fcalc hP, exp_smul_eq_fcalc hP, exp_smul_eq_fcalc hP, Matrix.mul_assoc Y,
    fcalc_mul]
  congr 4
  · congr 1
    funext i
    simp only [Pi.mul_apply, ← Complex.exp_add]
    congr 1
    ring
  · funext i
    congr 1
    ring

end Kernel

/-! ### The explicit double integral -/

lemma hasDerivAt_cexp_affine' (c d : ℂ) (r : ℝ) :
    HasDerivAt (fun r : ℝ => cexp (c * r + d)) (c * cexp (c * r + d)) r := by
  have h : HasDerivAt (fun r : ℝ => c * (r : ℂ) + d) c r := by
    have := ((hasDerivAt_id r).ofReal_comp).const_mul c
    simpa using this.add_const d
  exact h.cexp.congr_deriv (by ring)

/-- `I(p,q) = ∫_0^1 ∫_0^1 r e^{-tp(1 - r + r'r)} e^{-tq(1-r')r} dr' dr`. -/
noncomputable def Ipq (t : ℂ) (p q : ℝ) : ℂ :=
  ∫ r in (0:ℝ)..1, ∫ r' in (0:ℝ)..1,
    (r : ℂ) * (cexp (-t * (1 - r + r' * r) * p) * cexp (-t * ((1 - r') * r) * q))

/-- Closed form of `I(p,q)` for `c = t(q - p) ≠ 0`. -/
lemma Ipq_eq (t : ℂ) (p q : ℝ) (hc : t * ((q : ℂ) - p) ≠ 0) :
    Ipq t p q = cexp (-t * p) * (1 / (t * ((q : ℂ) - p)))
      * (1 - (1 - cexp (-(t * ((q : ℂ) - p)))) / (t * ((q : ℂ) - p))) := by
  set c : ℂ := t * ((q : ℂ) - p) with hc_def
  unfold Ipq
  -- inner integral
  have hin : ∀ r : ℝ, ∫ r' in (0:ℝ)..1,
      (r : ℂ) * (cexp (-t * (1 - r + r' * r) * p) * cexp (-t * ((1 - r') * r) * q))
      = (cexp (-t * p) - cexp (-t * p - c * r)) / c := by
    intro r
    have hd : ∀ r' : ℝ, HasDerivAt (fun r' : ℝ => cexp (c * r * r' + (-t * p - c * r)) / c)
        ((r : ℂ) * (cexp (-t * (1 - r + r' * r) * p) * cexp (-t * ((1 - r') * r) * q))) r' := by
      intro r'
      have h1 := (hasDerivAt_cexp_affine' (c * r) (-t * p - c * r) r').div_const c
      refine h1.congr_deriv ?_
      rw [← Complex.exp_add]
      have e : -t * (1 - (r : ℂ) + r' * r) * p + -t * ((1 - r') * r) * q
          = c * r * r' + (-t * p - c * r) := by rw [hc_def]; ring
      rw [e]
      field_simp
    have hcont : Continuous (fun r' : ℝ =>
        (r : ℂ) * (cexp (-t * (1 - r + r' * r) * p) * cexp (-t * ((1 - r') * r) * q))) := by
      fun_prop
    rw [integral_eq_sub_of_hasDerivAt (fun r' _ => hd r') (hcont.intervalIntegrable 0 1)]
    simp only [Complex.ofReal_one, Complex.ofReal_zero, mul_one, mul_zero, zero_add]
    ring
  simp_rw [hin]
  have hd : ∀ r : ℝ, HasDerivAt
      (fun r : ℝ => (cexp (-t * p) * r + cexp (-c * r + -t * p) / c) / c)
      ((cexp (-t * p) - cexp (-t * p - c * r)) / c) r := by
    intro r
    have h1 := ((hasDerivAt_id r).ofReal_comp).const_mul (cexp (-t * p))
    have h2 := (hasDerivAt_cexp_affine' (-c) (-t * p) r).div_const c
    have h3 := (h1.add h2).div_const c
    refine h3.congr_deriv ?_
    have e : -c * (r : ℂ) + -t * p = -t * p - c * r := by ring
    rw [e]
    simp only [Complex.ofReal_one]
    field_simp
    ring
  have hcont : Continuous (fun r : ℝ => (cexp (-t * p) - cexp (-t * p - c * r)) / c) := by
    fun_prop
  rw [integral_eq_sub_of_hasDerivAt (fun r _ => hd r) (hcont.intervalIntegrable 0 1)]
  simp only [Complex.ofReal_one, Complex.ofReal_zero, mul_one, mul_zero, zero_add]
  have e1 : cexp (-c + -t * p) = cexp (-t * p) * cexp (-c) := by
    rw [← Complex.exp_add]; ring_nf
  rw [e1]
  field_simp
  ring

/-- `I(p,q) + I(q,p) = (e^{-tp} - e^{-tq}) / (t(q - p))` for `t(q - p) ≠ 0`. -/
lemma Ipq_add_Iqp (t : ℂ) (p q : ℝ) (hc : t * ((q : ℂ) - p) ≠ 0) :
    Ipq t p q + Ipq t q p = (cexp (-t * p) - cexp (-t * q)) / (t * ((q : ℂ) - p)) := by
  have hc' : t * ((p : ℂ) - q) ≠ 0 := by
    rw [show t * ((p : ℂ) - q) = -(t * ((q : ℂ) - p)) by ring]; exact neg_ne_zero.mpr hc
  rw [Ipq_eq t p q hc, Ipq_eq t q p hc']
  have e1 : cexp (-t * q) = cexp (-t * p) * cexp (-(t * ((q : ℂ) - p))) := by
    rw [← Complex.exp_add]; ring_nf
  have e2 : cexp (-(t * ((p : ℂ) - q))) = (cexp (-(t * ((q : ℂ) - p))))⁻¹ := by
    rw [← Complex.exp_neg]; ring_nf
  have hE : cexp (-(t * ((q : ℂ) - p))) ≠ 0 := Complex.exp_ne_zero _
  rw [e1, e2, show t * ((p : ℂ) - q) = -(t * ((q : ℂ) - p)) by ring]
  field_simp
  ring

/-- Symmetrisation of a sum over ordered pairs of distinct points. -/
lemma sum_offdiag_symm (S : Finset ℝ) (F : ℝ → ℝ → ℂ) :
    ∑ p ∈ S, ∑ q ∈ S, (if p = q then 0 else F p q)
      = ∑ p ∈ S, ∑ q ∈ S, (if p < q then F p q + F q p else 0) := by
  have h1 : ∀ p q : ℝ, (if p = q then 0 else F p q)
      = (if p < q then F p q else 0) + (if q < p then F p q else 0) := by
    intro p q
    rcases lt_trichotomy p q with h | h | h
    · simp [h, h.ne, not_lt.mpr h.le]
    · subst h; simp
    · simp [h, h.ne', not_lt.mpr h.le]
  simp_rw [h1, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun p q => if q < p then F p q else 0)]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  split_ifs <;> ring

/-! ### The marginal -/

section Marginal

variable {P g : Matrix (Fin M) (Fin M) ℂ} (hP : P.IsHermitian) (hg : g.IsHermitian)
include hP

/-- `D(a, t) = a² (Φ_{X,g}(a) - Φ_{X,g_d}(a))`, `X = -tP`. -/
theorem bmvDG_eq_phi2 (a t : ℂ) :
    bmvDG hP g a t = a ^ 2 * (phi2 ((-t) • P) g a - phi2 ((-t) • P) (pinchH hP g) a) := by
  unfold bmvDG
  have e1 : a • g - t • P = (-t) • P + a • g := by rw [neg_smul]; abel
  have e2 : a • pinchH hP g - t • P = (-t) • P + a • pinchH hP g := by rw [neg_smul]; abel
  have htr : (g * NormedSpace.exp ((-t) • P)).trace
      = (pinchH hP g * NormedSpace.exp ((-t) • P)).trace := by
    rw [exp_smul_eq_fcalc hP]
    exact (trace_pinchH_mul_fcalc hP g (fun x => cexp (-t * x))).symm
  rw [e1, e2, trace_exp_add_smul, trace_exp_add_smul, htr]
  ring

/-- `Φ_{X,g}(0) - Φ_{X,g_d}(0) = Σ_{p ≠ q} I(p,q) Tr(g Q_p g Q_q)`. -/
lemma phi2G_diff_zero_sum (t : ℂ) :
    phi2 ((-t) • P) g 0 - phi2 ((-t) • P) (pinchH hP g) 0
      = ∑ p ∈ spec hP, ∑ q ∈ spec hP,
          if p = q then 0 else Ipq t p q * (g * sproj hP p * g * sproj hP q).trace := by
  unfold phi2
  have hi1 := (continuous_outer2_slice ((-t) • P) g 0).intervalIntegrable (μ := volume) 0 1
  have hi2 := (continuous_outer2_slice ((-t) • P) (pinchH hP g) 0).intervalIntegrable
    (μ := volume) 0 1
  rw [← intervalIntegral.integral_sub hi1 hi2]
  have hin : ∀ r : ℝ, (r : ℂ) * (∫ r' in (0:ℝ)..1, kern2 ((-t) • P) g 0 r r')
      - (r : ℂ) * (∫ r' in (0:ℝ)..1, kern2 ((-t) • P) (pinchH hP g) 0 r r')
      = ∑ p ∈ spec hP, ∑ q ∈ spec hP, if p = q then 0 else
          (∫ r' in (0:ℝ)..1, (r : ℂ) * (cexp (-t * (1 - r + r' * r) * p)
            * cexp (-t * ((1 - r') * r) * q))) * (g * sproj hP p * g * sproj hP q).trace := by
    intro r
    have c1 := continuous_kern2_slice ((-t) • P) g 0 r
    have c2 := continuous_kern2_slice ((-t) • P) (pinchH hP g) 0 r
    rw [← mul_sub, ← intervalIntegral.integral_sub (c1.intervalIntegrable 0 1)
      (c2.intervalIntegrable 0 1), ← intervalIntegral.integral_const_mul]
    have hpt : ∀ r' : ℝ, (r : ℂ) * (kern2 ((-t) • P) g 0 r r'
        - kern2 ((-t) • P) (pinchH hP g) 0 r r')
        = ∑ p ∈ spec hP, ∑ q ∈ spec hP, if p = q then 0 else
          (r : ℂ) * (cexp (-t * (1 - r + r' * r) * p) * cexp (-t * ((1 - r') * r) * q))
            * (g * sproj hP p * g * sproj hP q).trace := by
      intro r'
      have h1 := trace_sandwich_diff hP g (fun x : ℝ => cexp (-t * (1 - r + r' * r) * x))
        (fun x : ℝ => cexp (-t * ((1 - r') * r) * x))
      rw [kern2G_zero hP, kern2G_zero hP, h1, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      split_ifs
      · ring
      · ring
    rw [intervalIntegral.integral_congr (fun r' _ => hpt r')]
    rw [intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl fun p _ => ?_
      rw [intervalIntegral.integral_finsetSum]
      · refine Finset.sum_congr rfl fun q _ => ?_
        split_ifs
        · simp
        · rw [intervalIntegral.integral_mul_const]
      · intro q _
        split_ifs
        · exact intervalIntegrable_const
        · exact (by fun_prop : Continuous (fun r' : ℝ => (r : ℂ) * (cexp (-t * (1 - r + r' * r) * p)
            * cexp (-t * ((1 - r') * r) * q)) * (g * sproj hP p * g * sproj hP q).trace)).intervalIntegrable 0 1
    · intro p _
      refine (continuous_finsetSum _ fun q _ => ?_).intervalIntegrable 0 1
      split_ifs
      · exact continuous_const
      · fun_prop
  rw [intervalIntegral.integral_congr (fun r _ => hin r), intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun p _ => ?_
    rw [intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl fun q _ => ?_
      split_ifs
      · simp
      · rw [intervalIntegral.integral_mul_const]
        rfl
    · intro q _
      split_ifs
      · exact intervalIntegrable_const
      · refine Continuous.intervalIntegrable ?_ 0 1
        refine Continuous.mul ?_ continuous_const
        have h : Continuous (Function.uncurry fun (r : ℝ) (r' : ℝ) =>
            (r : ℂ) * (cexp (-t * (1 - r + r' * r) * p) * cexp (-t * ((1 - r') * r) * q))) := by
          unfold Function.uncurry; fun_prop
        exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' h 0 1
  · intro p _
    refine (continuous_finsetSum _ fun q _ => ?_).intervalIntegrable 0 1
    split_ifs
    · exact continuous_const
    · refine Continuous.mul ?_ continuous_const
      have h : Continuous (Function.uncurry fun (r : ℝ) (r' : ℝ) =>
          (r : ℂ) * (cexp (-t * (1 - r + r' * r) * p) * cexp (-t * ((1 - r') * r) * q))) := by
        unfold Function.uncurry; fun_prop
      exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' h 0 1

/-- Symmetry of the weights: `Tr(g Q_p g Q_q) = Tr(g Q_q g Q_p)`. -/
lemma trace_sandwich_symm (p q : ℝ) :
    (g * sproj hP p * g * sproj hP q).trace = (g * sproj hP q * g * sproj hP p).trace := by
  rw [show g * sproj hP p * g * sproj hP q = (g * sproj hP p) * (g * sproj hP q) by
      simp only [Matrix.mul_assoc],
    Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

/-- **`Φ_{X,g}(0) - Φ_{X,g_d}(0)` in closed form**, `t ≠ 0`. -/
theorem phi2G_diff_zero (t : ℂ) (ht : t ≠ 0) :
    phi2 ((-t) • P) g 0 - phi2 ((-t) • P) (pinchH hP g) 0
      = ∑ p ∈ spec hP, ∑ q ∈ spec hP, if p < q then
          (g * sproj hP p * g * sproj hP q).trace
            * ((cexp (-t * p) - cexp (-t * q)) / (t * ((q : ℂ) - p))) else 0 := by
  rw [phi2G_diff_zero_sum hP t, sum_offdiag_symm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  split_ifs with hpq
  · have hc : t * ((q : ℂ) - p) ≠ 0 := by
      refine mul_ne_zero ht ?_
      rw [sub_ne_zero, Ne, Complex.ofReal_inj]
      exact hpq.ne'
    rw [trace_sandwich_symm hP q p, ← Ipq_add_Iqp t p q hc]
    ring
  · rfl

include hg in
/-- **The `τ`-marginal in Laplace form** (from `Hyp_RI_gen M`): for `t ≠ 0`,
`∫∫ e^{-tτ} ρ = Σ_{p<q} Tr(g Q_p g Q_q) (e^{-tp} - e^{-tq})/(t(q - p))`. -/
theorem laplaceG_zero (hspec : ∀ p ∈ spec hP, 0 ≤ p ∧ p ≤ 1) (hRI : Hyp_RI_gen M) (t : ℂ)
    (ht : t ≠ 0) :
    laplaceG P g 0 t
      = ∑ p ∈ spec hP, ∑ q ∈ spec hP, if p < q then
          (g * sproj hP p * g * sproj hP q).trace
            * ((cexp (-t * p) - cexp (-t * q)) / (t * ((q : ℂ) - p))) else 0 := by
  rw [← phi2G_diff_zero hP t ht]
  have hL : Continuous (fun a : ℂ => laplaceG P g a t) :=
    (differentiable_laplaceG_a hP hg hspec hRI t).continuous
  have hΦ : Continuous (fun a : ℂ => phi2 ((-t) • P) g a - phi2 ((-t) • P) (pinchH hP g) a) :=
    (continuous_phi2 _ _).sub (continuous_phi2 _ _)
  have heq : ∀ a : ℂ, a ≠ 0 →
      laplaceG P g a t = phi2 ((-t) • P) g a - phi2 ((-t) • P) (pinchH hP g) a := by
    intro a ha
    have h1 := theoremA_gen hP hg hspec hRI a t
    rw [bmvDG_eq_phi2 hP] at h1
    exact (mul_left_cancel₀ (pow_ne_zero 2 ha) h1).symm
  have h1 : Tendsto (fun a : ℂ => laplaceG P g a t) (𝓝[≠] 0) (𝓝 (laplaceG P g 0 t)) :=
    hL.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun a : ℂ => laplaceG P g a t) (𝓝[≠] 0)
      (𝓝 (phi2 ((-t) • P) g 0 - phi2 ((-t) • P) (pinchH hP g) 0)) := by
    refine (hΦ.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with a ha
    exact (heq a ha).symm
  exact tendsto_nhds_unique h1 h2

end Marginal

/-! ### The sine moment -/

section Sine

variable {P g : Matrix (Fin M) (Fin M) ℂ} (hP : P.IsHermitian) (hg : g.IsHermitian)
include hP hg

/-- `Tr(g Q_p g Q_q) = ‖Q_q g Q_p‖_F²` (as a complex number) for Hermitian `g`. -/
lemma trace_sandwich_eq_frob (p q : ℝ) :
    (g * sproj hP p * g * sproj hP q).trace
      = ((∑ i, ∑ j, ‖(sproj hP q * g * sproj hP p) i j‖ ^ 2 : ℝ) : ℂ) := by
  have hX : (sproj hP q * g * sproj hP p) * (sproj hP q * g * sproj hP p)ᴴ
      = sproj hP q * g * sproj hP p * g * sproj hP q := by
    rw [conjTranspose_mul, conjTranspose_mul, (isHermitian_sproj hP p).eq, hg.eq,
      (isHermitian_sproj hP q).eq]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (sproj hP p) (sproj hP p), sproj_mul_self]
  have h1 : ((∑ i, ∑ j, ‖(sproj hP q * g * sproj hP p) i j‖ ^ 2 : ℝ) : ℂ)
      = ((sproj hP q * g * sproj hP p) * (sproj hP q * g * sproj hP p)ᴴ).trace := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
    push_cast
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.star_def, Complex.mul_conj']
  rw [h1, hX, Matrix.trace_mul_comm (sproj hP q * g * sproj hP p * g) (sproj hP q),
    show sproj hP q * (sproj hP q * g * sproj hP p * g) = sproj hP q * g * sproj hP p * g by
      simp only [← Matrix.mul_assoc, sproj_mul_self],
    Matrix.trace_mul_comm (g * sproj hP p * g) (sproj hP q)]
  simp only [Matrix.mul_assoc]

/-- **The sine moment of the density** (from `Hyp_RI_gen M`):
`∫∫ sin(πτ) ρ = Σ_{p<q} ‖Q_q g Q_p‖_F² (cos πp - cos πq)/(π(q - p))`. -/
theorem integral_sin_mul_rhoG (hspec : ∀ p ∈ spec hP, 0 ≤ p ∧ p ≤ 1) (hRI : Hyp_RI_gen M) :
    ∫ q : ℝ × ℝ, Real.sin (π * q.2) * rhoG P g q.1 q.2
      = ∑ p ∈ spec hP, ∑ q ∈ spec hP, if p < q then
          (∑ i, ∑ j, ‖(sproj hP q * g * sproj hP p) i j‖ ^ 2)
            * ((Real.cos (π * p) - Real.cos (π * q)) / (π * (q - p))) else 0 := by
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hI : (I * π : ℂ) ≠ 0 := mul_ne_zero I_ne_zero hpi
  have hI' : (-(I * π) : ℂ) ≠ 0 := neg_ne_zero.mpr hI
  have hint : ∀ a t : ℂ, Integrable (fun q : ℝ × ℝ => cexp (a * q.1 - t * q.2)
      * (rhoG P g q.1 q.2 : ℂ)) := integrable_laplaceG_integrand hP hg hspec hRI
  have hm := laplaceG_zero hP hg hspec hRI (-(I * π)) hI'
  have hp := laplaceG_zero hP hg hspec hRI (I * π) hI
  unfold laplaceG at hm hp
  have hsub := congrArg₂ (· - ·) hm hp
  rw [← integral_sub (hint 0 (-(I * π))) (hint 0 (I * π))] at hsub
  have hfun : ∀ q : ℝ × ℝ, cexp (0 * q.1 - -(I * π) * q.2) * (rhoG P g q.1 q.2 : ℂ)
      - cexp (0 * q.1 - I * π * q.2) * (rhoG P g q.1 q.2 : ℂ)
      = (2 * I) * ((Real.sin (π * q.2) * rhoG P g q.1 q.2 : ℝ) : ℂ) := by
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
  -- the right-hand side
  simp only [← Finset.sum_sub_distrib] at hsub
  have hterm : ∀ p ∈ spec hP, ∀ q ∈ spec hP,
      ((if p < q then (g * sproj hP p * g * sproj hP q).trace
          * ((cexp (-(-(I * π)) * p) - cexp (-(-(I * π)) * q)) / (-(I * π) * ((q : ℂ) - p)))
        else 0)
      - (if p < q then (g * sproj hP p * g * sproj hP q).trace
          * ((cexp (-(I * π) * p) - cexp (-(I * π) * q)) / (I * π * ((q : ℂ) - p))) else 0))
      = (2 * I) * (((if p < q then
          (∑ i, ∑ j, ‖(sproj hP q * g * sproj hP p) i j‖ ^ 2)
            * ((Real.cos (π * p) - Real.cos (π * q)) / (π * (q - p))) else 0 : ℝ) : ℂ)) := by
    intro p _ q _
    split_ifs with hpq
    · rw [trace_sandwich_eq_frob hP hg]
      have hqp : ((q : ℂ) - p) ≠ 0 := by
        rw [sub_ne_zero, Ne, Complex.ofReal_inj]; exact hpq.ne'
      have hcp : Complex.cos ((π : ℂ) * p) = (cexp (I * π * p) + cexp (-(I * π * p))) / 2 := by
        rw [Complex.cos]
        ring_nf
      have hcq : Complex.cos ((π : ℂ) * q) = (cexp (I * π * q) + cexp (-(I * π * q))) / 2 := by
        rw [Complex.cos]
        ring_nf
      push_cast
      rw [hcp, hcq]
      have e1 : -(-(I * π)) * (p : ℂ) = I * π * p := by ring
      have e2 : -(-(I * π)) * (q : ℂ) = I * π * q := by ring
      have e3 : -(I * π) * (p : ℂ) = -(I * π * p) := by ring
      have e4 : -(I * π) * (q : ℂ) = -(I * π * q) := by ring
      rw [e1, e2, e3, e4]
      field_simp
      ring_nf
      rw [Complex.I_sq]
      ring
    · simp
  rw [Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun q hq => hterm p hp q hq] at hsub
  simp_rw [← Finset.mul_sum] at hsub
  have h2I : (2 * I : ℂ) ≠ 0 := mul_ne_zero two_ne_zero I_ne_zero
  have hfin := mul_left_cancel₀ h2I hsub
  exact_mod_cast hfin

end Sine

end HarmonicMajorization
