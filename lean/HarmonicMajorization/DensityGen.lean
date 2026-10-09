import HarmonicMajorization.MainGen

/-!
# Theorem A with the properties of the density (general `P`, no hypotheses)

Authors: Ansh Mishra, Aryan Senthilkumar.  License: MIT.

`P` Hermitian with spectrum in `[0, 1]`, `g` Hermitian, `ρ = rhoG P g`.
Main results:
* `rhoG_eq_zero_of_outside`: `ρ(s, τ) = 0` unless `min spec P < τ < max spec P`;
* `theoremA_package`: measurability, `ρ ≥ 0`, the support in `s` and in `τ`, the integrable profile
  `ρ ≤ C Ψ`, integrability of `e^{as - tτ} ρ` for all `(a, t) ∈ ℂ²`, and Theorem A;
* `total_mass`: `∫∫ ρ = Σ_{p<q} ‖Q_p g Q_q‖_F²` (THEOREMS.md, Theorem A, properties of `ρ`).
-/

set_option autoImplicit false

namespace HarmonicMajorization

open Matrix Complex MeasureTheory Filter Topology Set
open scoped Real ComplexOrder

variable {M : ℕ}

/-- `(e^{-tp} - e^{-tq})/(t(q - p)) → 1` as `t → 0`. -/
lemma tendsto_exp_quot {p q : ℝ} (hpq : p ≠ q) :
    Tendsto (fun t : ℂ => (cexp (-t * p) - cexp (-t * q)) / (t * ((q : ℂ) - p))) (𝓝[≠] 0)
      (𝓝 1) := by
  have hexp : ∀ r : ℝ, HasDerivAt (fun t : ℂ => cexp (-t * r)) (-(r : ℂ)) 0 := by
    intro r
    have h := (((hasDerivAt_id (0 : ℂ)).neg).mul_const (r : ℂ)).cexp
    refine h.congr_deriv ?_
    simp
  have hd : HasDerivAt (fun t : ℂ => cexp (-t * p) - cexp (-t * q)) ((q : ℂ) - p) 0 := by
    have h := (hexp p).sub (hexp q)
    refine h.congr_deriv ?_
    ring
  have hqp : ((q : ℂ) - p) ≠ 0 := by
    rw [sub_ne_zero]; exact_mod_cast hpq.symm
  have hs := hd.tendsto_slope_zero.div_const ((q : ℂ) - p)
  rw [div_self hqp] at hs
  refine hs.congr' (Eventually.of_forall fun t => ?_)
  simp only [zero_add, neg_zero, zero_mul, Complex.exp_zero, sub_self, sub_zero, smul_eq_mul,
    div_eq_mul_inv, mul_inv]
  ring

section Density

variable {P g : Matrix (Fin M) (Fin M) ℂ} (hP : P.IsHermitian) (hg : g.IsHermitian)
include hP hg

/-- **Support in `τ`**: `ρ(s, τ) = 0` unless `min spec P < τ < max spec P`. -/
theorem rhoG_eq_zero_of_outside {τ : ℝ}
    (hτ : (∀ p ∈ spec hP, τ ≤ p) ∨ (∀ p ∈ spec hP, p ≤ τ)) (s : ℝ) : rhoG P g s τ = 0 := by
  unfold rhoG
  by_cases hτs : τ ∈ spec hP
  · rw [imAbsSum_pencilRoots_of_mem_spec hP hτs, zero_div]
  · have hdef : (∀ p ∈ spec hP, τ < p) ∨ (∀ p ∈ spec hP, p < τ) := by
      rcases hτ with h | h
      · exact Or.inl fun p hp => lt_of_le_of_ne (h p hp) (fun e => hτs (e ▸ hp))
      · exact Or.inr fun p hp => lt_of_le_of_ne (h p hp) (fun e => hτs (e.symm ▸ hp))
    rw [imAbsSum_pencilRoots_eq_zero_of_definite hP (isHermitian_g_sub hg s) hdef, zero_div]

variable (hspec : ∀ p ∈ spec hP, 0 ≤ p ∧ p ≤ 1)
include hspec

/-- **Theorem A with the properties of the density** (THEOREMS.md, Section 1; no hypotheses):
`ρ` is jointly measurable and nonnegative, vanishes unless `λ_min(g) < s < λ_max(g)` and
`min spec P < τ < max spec P`, satisfies `ρ ≤ C Ψ` with `Ψ = domG hP` integrable, `e^{as - tτ} ρ` is
integrable for all `(a, t) ∈ ℂ²`, and `Tr e^{ag - tP} - Tr e^{a g_d - tP} = a² ∫∫ e^{as - tτ} ρ`. -/
theorem theoremA_package :
    Measurable (Function.uncurry (rhoG P g)) ∧
    (∀ s τ, 0 ≤ rhoG P g s τ) ∧
    (∀ s τ, ((∀ i, s ≤ hg.eigenvalues i) ∨ (∀ i, hg.eigenvalues i ≤ s)) → rhoG P g s τ = 0) ∧
    (∀ s τ, ((∀ p ∈ spec hP, τ ≤ p) ∨ (∀ p ∈ spec hP, p ≤ τ)) → rhoG P g s τ = 0) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ s τ : ℝ, rhoG P g s τ ≤ C * domG hP τ) ∧ Integrable (domG hP) ∧
    (∀ a t : ℂ, Integrable (fun q : ℝ × ℝ => cexp (a * q.1 - t * q.2) * (rhoG P g q.1 q.2 : ℂ))) ∧
    (∀ a t : ℂ, bmvDG hP g a t = a ^ 2 * laplaceG P g a t) :=
  ⟨measurable_rhoG hP g, fun s τ => rhoG_nonneg P g s τ,
    fun _ τ hs => rhoG_eq_zero_of_semidef hP hg hs τ,
    fun s _ hτ => rhoG_eq_zero_of_outside hP hg hτ s,
    rhoG_le_domG hP hg, integrable_domG hP,
    fun a t => integrable_laplaceG_integrand hP hg hspec (hyp_RI_gen M) a t,
    fun a t => theoremA hP hg hspec a t⟩

/-- **Total mass of the density**: `∫∫ ρ = Σ_{p<q} ‖Q_p g Q_q‖_F²`. -/
theorem total_mass :
    ∫ q : ℝ × ℝ, rhoG P g q.1 q.2
      = ∑ p ∈ spec hP, ∑ q ∈ spec hP, if p < q then frobNorm (sproj hP p * g * sproj hP q) ^ 2
          else 0 := by
  have hcont : Continuous (fun t : ℂ => laplaceG P g 0 t) := by
    have h := (differentiable_laplaceG_t hP hg hspec (hyp_RI_gen M) 0).continuous
    simpa using h
  have hL0 : laplaceG P g 0 0 = ((∫ q : ℝ × ℝ, rhoG P g q.1 q.2 : ℝ) : ℂ) := by
    unfold laplaceG
    simp only [zero_mul, sub_zero, Complex.exp_zero, one_mul]
    exact integral_ofReal
  set T : ℝ → ℝ → ℂ := fun p q => (g * sproj hP p * g * sproj hP q).trace with hT
  have hlim : Tendsto (fun t : ℂ => laplaceG P g 0 t) (𝓝[≠] 0)
      (𝓝 (∑ p ∈ spec hP, ∑ q ∈ spec hP, if p < q then T p q * 1 else 0)) := by
    have h : Tendsto (fun t : ℂ => ∑ p ∈ spec hP, ∑ q ∈ spec hP, if p < q then
        T p q * ((cexp (-t * p) - cexp (-t * q)) / (t * ((q : ℂ) - p))) else 0) (𝓝[≠] 0)
        (𝓝 (∑ p ∈ spec hP, ∑ q ∈ spec hP, if p < q then T p q * 1 else 0)) := by
      refine tendsto_finsetSum _ fun p _ => tendsto_finsetSum _ fun q _ => ?_
      by_cases hpq : p < q
      · simp only [hpq, if_true]
        exact tendsto_const_nhds.mul (tendsto_exp_quot hpq.ne)
      · simp only [hpq, if_false]
        exact tendsto_const_nhds
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (tau_marginal hP hg hspec t ht).symm
  have heq := tendsto_nhds_unique (hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hlim
  rw [hL0] at heq
  have hfrob : ∀ p q : ℝ, T p q * 1 = ((frobNorm (sproj hP p * g * sproj hP q) ^ 2 : ℝ) : ℂ) := by
    intro p q
    rw [mul_one, hT]
    simp only
    rw [trace_sandwich_eq_frob hP hg, frobNorm_sandwich_sq hP hg]
  have hsum : (∑ p ∈ spec hP, ∑ q ∈ spec hP, if p < q then T p q * 1 else 0)
      = ((∑ p ∈ spec hP, ∑ q ∈ spec hP, if p < q then
          frobNorm (sproj hP p * g * sproj hP q) ^ 2 else 0 : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    split_ifs
    · rw [hfrob]
    · rfl
  rw [hsum] at heq
  exact_mod_cast heq

end Density

end HarmonicMajorization
