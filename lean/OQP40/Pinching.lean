import OQP40.Statement
import HarmonicMajorization.DensityGen
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Uniqueness

/-!
# The pinching inequality for word averages, for all word lengths

Authors: Ansh Mishra, Aryan Senthilkumar. License: MIT.

This file proves `PinchingInequality` of `OQP40/Statement.lean`, T. H. Dinh's Conjecture 5.1
(arXiv:2605.17782), for all word lengths: for positive semidefinite $A, B$ and all $n, m \ge 0$,
$$\operatorname{Tr}(A^n E_A(B)^m) \le p_{n,m}(A,B),$$
where $E_A(B)$ is the pinching of $B$ onto the eigenspaces of $A$ (`pinching`) and $p_{n,m}$ is the
word average (`wordAverage`). Dinh proved the case $m = 2$. Mathematics:
`publish/OQP-40/math/01-pinching-theorem.md` (Theorems 1 and 2).

## Main results
- `gap_identity` (Theorem 1 of the note, for $P$ with spectrum in $[0, 1]$): for Hermitian $P$
  and $g$, with $C = \binom{n+m}{n}$ and $g_d$ the pinching of $g$ onto the eigenspaces of $P$,
  $$\sum_W \operatorname{Tr} W(P, g) - C \operatorname{Tr}(P^n g_d^m)
    = C\, m(m-1) \iint \tau^n s^{m-2} \rho(s, \tau)\, ds\, d\tau,$$
  the sum over the words with $n$ letters $P$ and $m$ letters $g$, and $\rho$ = `rhoG P g` the
  density of Theorem A;
- `wordAverage_eq_trace_pinching_add`: for positive semidefinite $A, B$,
  $p_{n,m}(A,B) = \operatorname{Tr}(A^n E_A(B)^m) + r$ with an explicit $r \ge 0$;
- `trace_pinching_le_wordAverage` (in the order of `ComplexOrder`) and `pinchingInequality`
  (`PinchingInequality`, for the real parts): Dinh's Conjecture 5.1 for all $n, m$.
- Checks of the definition of `pinching`: `commute_pinching`, `trace_pinching`,
  `pinching_eq_self_of_commute`.

No hypotheses: the only analytic input is Theorem A, `HarmonicMajorization.theoremA`, proved in
`HarmonicMajorization/` without hypotheses, together with the support and integrability
properties of its density (`HarmonicMajorization/PencilGen.lean`, `DensityGen.lean`).

## Proof
Theorem A: $\operatorname{Tr} e^{ag - tP} - \operatorname{Tr} e^{a g_d - tP}
= a^2 \iint e^{as - t\tau} \rho(s, \tau)\, ds\, d\tau$ for all $(a, t) \in \mathbb{C}^2$, when
the spectrum of $P$ lies in $[0, 1]$.
1. On the ray $(a, t) = (z, -zv)$ both sides are power series in $z$: the exponential series
   (`hasSum_trace_exp`) and, by dominated convergence, the moment series of $\rho$
   (`hasSum_laplace`; $\rho$ is integrable and vanishes outside a compact rectangle,
   `integrable_rhoG_smul`). Uniqueness of power series coefficients (`coeff_unique`) gives
   `moment_identity`: $\operatorname{Tr}(g + vP)^{k+2} - \operatorname{Tr}(g_d + vP)^{k+2}
   = (k+2)(k+1) \iint (s + v\tau)^k \rho$.
2. Both sides are polynomials in $v$: the left side by the word expansion `add_smul_pow_eq_sum`
   (Pascal's recursion `wordSum_succ_succ`) and the binomial theorem for the commuting pair
   $P, g_d$; the right side by the binomial theorem under the integral. Comparing coefficients
   again gives `coeff_identity`, and `gap_identity` follows with `choose_identity`.
3. For $A, B \ge 0$ apply this to $P = A/c$ with $c = 1 + \sum_{ij} |A_{ij}|$, whose spectrum lies
   in $[0, 1]$ (`spec_smul_mem_Icc`). The pinching does not change (`pinchH_smul`: the pinching
   is determined by the commutant of $A$, `eq_of_commute_of_trace`), and both sides scale by
   $c^n$ (`wordSum_smul_left`). On the support of $\rho$, $s \ge \lambda_{\min}(B) \ge 0$ and
   $\tau > 0$, so the right side of the gap identity is $\ge 0$ (`integral_moment_nonneg`).
-/

set_option autoImplicit false

namespace OpenQuantumProblem40

open Matrix Complex MeasureTheory Filter Topology HarmonicMajorization
open scoped ComplexOrder

/- ### Coefficients of everywhere convergent power series -/

/-- A series `Σ a_n z^n` that converges to `f z` for every `z` is a power series of `f` at `0`. -/
lemma hasFPowerSeriesAt_ofScalars {a : ℕ → ℂ} {f : ℂ → ℂ}
    (ha : ∀ z : ℂ, HasSum (fun n => a n * z ^ n) (f z)) :
    HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℂ a) 0 := by
  have h1 : Tendsto a atTop (𝓝 0) := by
    simpa using (ha 1).summable.tendsto_atTop_zero
  have hlim : Tendsto (fun n => ‖FormalMultilinearSeries.ofScalars ℂ a n‖ * ((1 : NNReal) : ℝ) ^ n)
      atTop (𝓝 0) := by
    simpa [FormalMultilinearSeries.ofScalars_norm] using h1.norm
  refine ⟨1, by simpa using FormalMultilinearSeries.le_radius_of_tendsto _ hlim, one_pos,
    fun {y} _ => ?_⟩
  rw [zero_add]
  exact (ha y).congr_fun fun n => by simp [mul_comm]

/-- **Uniqueness of coefficients**: two everywhere convergent power series with the same sum have
the same coefficients. -/
lemma coeff_unique {a b : ℕ → ℂ} {f : ℂ → ℂ}
    (ha : ∀ z : ℂ, HasSum (fun n => a n * z ^ n) (f z))
    (hb : ∀ z : ℂ, HasSum (fun n => b n * z ^ n) (f z)) : a = b :=
  FormalMultilinearSeries.ofScalars_series_injective ℂ ℂ
    ((hasFPowerSeriesAt_ofScalars ha).eq_formalMultilinearSeries (hasFPowerSeriesAt_ofScalars hb))

/-- The exponential series of a real number. -/
lemma hasSum_real_exp (r : ℝ) :
    HasSum (fun k : ℕ => (k.factorial : ℝ)⁻¹ * r ^ k) (Real.exp r) := by
  simpa [Real.exp_eq_exp_ℝ, smul_eq_mul] using NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) r

/-- The exponential series of a complex number. -/
lemma hasSum_cexp (c : ℂ) :
    HasSum (fun k : ℕ => (k.factorial : ℂ)⁻¹ * c ^ k) (cexp c) := by
  simpa [Complex.exp_eq_exp_ℂ, smul_eq_mul] using NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) c

variable {M : ℕ}

/-- `Tr e^{zX} = Σ_N z^N Tr X^N / N!`. -/
lemma hasSum_trace_exp (X : Matrix (Fin M) (Fin M) ℂ) (z : ℂ) :
    HasSum (fun N : ℕ => ((N.factorial : ℂ)⁻¹ * (X ^ N).trace) * z ^ N)
      (NormedSpace.exp (z • X)).trace := by
  open scoped Matrix.Norms.Operator in
  have h := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (z • X)).mapL
    (LinearMap.toContinuousLinearMap (Matrix.traceLinearMap (Fin M) ℂ ℂ))
  exact h.congr_fun fun N => by
    simp only [LinearMap.coe_toContinuousLinearMap', Matrix.traceLinearMap_apply, smul_pow,
      trace_smul, smul_eq_mul]
    ring

section Density

variable {P g : Matrix (Fin M) (Fin M) ℂ} (hP : P.IsHermitian) (hg : g.IsHermitian)
include hP hg

/-- The density `ρ` is integrable. -/
lemma integrable_rhoG : Integrable (fun q : ℝ × ℝ => rhoG P g q.1 q.2) := by
  simpa using integrable_exp_mul_rhoG hP hg (hyp_RI_gen M) 0

variable (hspec : ∀ p ∈ spec hP, 0 ≤ p ∧ p ≤ 1)
include hspec

/-- `ρ` vanishes outside a compact rectangle: its product with a continuous function is
integrable. -/
lemma integrable_rhoG_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ : ℝ × ℝ → E} (hφ : Continuous φ) :
    Integrable (fun q : ℝ × ℝ => rhoG P g q.1 q.2 • φ q) := by
  obtain ⟨R, -, hsupp⟩ := rhoG_support hP hg
  obtain ⟨K, hK⟩ := (isCompact_Icc.prod isCompact_Icc :
    IsCompact (Set.Icc (-R) R ×ˢ Set.Icc (0 : ℝ) 1)).exists_bound_of_continuousOn hφ.continuousOn
  have hρ := integrable_rhoG hP hg
  have hmeas : AEStronglyMeasurable (fun q : ℝ × ℝ => rhoG P g q.1 q.2 • φ q) volume :=
    hρ.aestronglyMeasurable.smul hφ.aestronglyMeasurable
  refine (hρ.mul_const K).mono' hmeas (ae_of_all _ fun q => ?_)
  rw [norm_smul, Real.norm_of_nonneg (rhoG_nonneg _ _ _ _)]
  by_cases h0 : rhoG P g q.1 q.2 = 0
  · simp [h0]
  · have hs : |q.1| < R := by
      by_contra hc
      exact h0 (hsupp q.1 q.2 (not_lt.1 hc))
    have hτ : 0 < q.2 ∧ q.2 < 1 := by
      by_contra hc
      exact h0 (rhoG_eq_zero_of_not_mem_Ioo hP hg hspec hc q.1)
    have hq : q ∈ Set.Icc (-R) R ×ˢ Set.Icc (0 : ℝ) 1 :=
      ⟨⟨by linarith [neg_abs_le q.1], by linarith [le_abs_self q.1]⟩, ⟨hτ.1.le, hτ.2.le⟩⟩
    exact mul_le_mul_of_nonneg_left (hK q hq) (rhoG_nonneg _ _ _ _)

/-- `φ ρ` is integrable for continuous complex `φ`. -/
lemma integrable_mul_rhoG {φ : ℝ × ℝ → ℂ} (hφ : Continuous φ) :
    Integrable (fun q : ℝ × ℝ => φ q * (rhoG P g q.1 q.2 : ℂ)) := by
  refine (integrable_rhoG_smul hP hg hspec hφ).congr (ae_of_all _ fun q => ?_)
  simp only [Complex.real_smul, mul_comm]

/-- `φ ρ` is integrable for continuous real `φ`. -/
lemma integrable_mul_rhoG_real {φ : ℝ × ℝ → ℝ} (hφ : Continuous φ) :
    Integrable (fun q : ℝ × ℝ => φ q * rhoG P g q.1 q.2) := by
  refine (integrable_rhoG_smul hP hg hspec hφ).congr (ae_of_all _ fun q => ?_)
  simp only [smul_eq_mul, mul_comm]

/-- **The moment series of `ρ`** along the direction `(1, v)`:
`∫∫ e^{z(s + vτ)} ρ = Σ_k z^k/k! ∫∫ (s + vτ)^k ρ`. -/
lemma hasSum_laplace (v z : ℂ) :
    HasSum (fun k : ℕ => ((k.factorial : ℂ)⁻¹
        * ∫ q : ℝ × ℝ, ((q.1 : ℂ) + v * q.2) ^ k * (rhoG P g q.1 q.2 : ℂ)) * z ^ k)
      (∫ q : ℝ × ℝ, cexp (z * ((q.1 : ℂ) + v * q.2)) * (rhoG P g q.1 q.2 : ℂ)) := by
  have key := hasSum_integral_of_dominated_convergence
    (F := fun (k : ℕ) (q : ℝ × ℝ) =>
      ((k.factorial : ℂ)⁻¹ * (z * ((q.1 : ℂ) + v * q.2)) ^ k) * (rhoG P g q.1 q.2 : ℂ))
    (f := fun q : ℝ × ℝ => cexp (z * ((q.1 : ℂ) + v * q.2)) * (rhoG P g q.1 q.2 : ℂ))
    (fun (k : ℕ) (q : ℝ × ℝ) =>
      ((k.factorial : ℝ)⁻¹ * (‖z‖ * ‖(q.1 : ℂ) + v * q.2‖) ^ k) * rhoG P g q.1 q.2)
    (fun k => (integrable_mul_rhoG hP hg hspec (by fun_prop)).aestronglyMeasurable)
    (fun k => ae_of_all _ fun q => le_of_eq (by
      rw [norm_mul, norm_mul, norm_inv, norm_pow, norm_mul, Complex.norm_natCast, Complex.norm_real,
        Real.norm_of_nonneg (rhoG_nonneg _ _ _ _)]))
    (ae_of_all _ fun q => ((hasSum_real_exp _).mul_right _).summable)
    (by
      have e : (fun q : ℝ × ℝ => ∑' k : ℕ,
          ((k.factorial : ℝ)⁻¹ * (‖z‖ * ‖(q.1 : ℂ) + v * q.2‖) ^ k) * rhoG P g q.1 q.2)
          = fun q => Real.exp (‖z‖ * ‖(q.1 : ℂ) + v * q.2‖) * rhoG P g q.1 q.2 := by
        funext q
        exact ((hasSum_real_exp _).mul_right _).tsum_eq
      rw [e]
      exact integrable_mul_rhoG_real hP hg hspec (by fun_prop))
    (ae_of_all _ fun q => (hasSum_cexp _).mul_right _)
  have e : ∀ k : ℕ, ∫ q : ℝ × ℝ,
      ((k.factorial : ℂ)⁻¹ * (z * ((q.1 : ℂ) + v * q.2)) ^ k) * (rhoG P g q.1 q.2 : ℂ)
      = ((k.factorial : ℂ)⁻¹
          * ∫ q : ℝ × ℝ, ((q.1 : ℂ) + v * q.2) ^ k * (rhoG P g q.1 q.2 : ℂ)) * z ^ k := by
    intro k
    have h : (fun q : ℝ × ℝ =>
        ((k.factorial : ℂ)⁻¹ * (z * ((q.1 : ℂ) + v * q.2)) ^ k) * (rhoG P g q.1 q.2 : ℂ))
        = fun q => ((k.factorial : ℂ)⁻¹ * z ^ k)
            * (((q.1 : ℂ) + v * q.2) ^ k * (rhoG P g q.1 q.2 : ℂ)) := by
      funext q
      rw [mul_pow]
      ring
    rw [h, integral_const_mul]
    ring
  simpa only [e] using key

/-- **The moment identity** (coefficient of `z^{k+2}` in Theorem A on the ray
`(a, t) = (z, -zv)`): `Tr (g + vP)^{k+2} - Tr (g_d + vP)^{k+2}
= (k+2)(k+1) ∫∫ (s + vτ)^k ρ(s, τ) ds dτ`. -/
theorem moment_identity (v : ℂ) (k : ℕ) :
    ((g + v • P) ^ (k + 2)).trace - ((pinchH hP g + v • P) ^ (k + 2)).trace
      = ((k + 2) * (k + 1) : ℂ)
        * ∫ q : ℝ × ℝ, ((q.1 : ℂ) + v * q.2) ^ k * (rhoG P g q.1 q.2 : ℂ) := by
  set I : ℕ → ℂ := fun j => ∫ q : ℝ × ℝ, ((q.1 : ℂ) + v * q.2) ^ j * (rhoG P g q.1 q.2 : ℂ)
    with hI
  have hf1 : ∀ z : ℂ, HasSum (fun N : ℕ => ((N.factorial : ℂ)⁻¹
      * (((g + v • P) ^ N).trace - ((pinchH hP g + v • P) ^ N).trace)) * z ^ N)
      (bmvDG hP g z (-(z * v))) := by
    intro z
    have h := (hasSum_trace_exp (g + v • P) z).sub (hasSum_trace_exp (pinchH hP g + v • P) z)
    have e : bmvDG hP g z (-(z * v)) = (NormedSpace.exp (z • (g + v • P))).trace
        - (NormedSpace.exp (z • (pinchH hP g + v • P))).trace := by
      unfold bmvDG
      congr 3 <;> module
    rw [e]
    exact h.congr_fun fun N => by ring
  have hf2 : ∀ z : ℂ, HasSum (fun N : ℕ =>
      (if N < 2 then 0 else ((N - 2).factorial : ℂ)⁻¹ * I (N - 2)) * z ^ N)
      (bmvDG hP g z (-(z * v))) := by
    intro z
    rw [theoremA hP hg hspec]
    have hL : laplaceG P g z (-(z * v))
        = ∫ q : ℝ × ℝ, cexp (z * ((q.1 : ℂ) + v * q.2)) * (rhoG P g q.1 q.2 : ℂ) := by
      unfold laplaceG
      congr 1
      funext q
      congr 2
      ring
    refine (hasSum_nat_add_iff' 2).1 ?_
    have e2 : ∑ i ∈ Finset.range 2,
        (if i < 2 then 0 else ((i - 2).factorial : ℂ)⁻¹ * I (i - 2)) * z ^ i = 0 := by
      simp [Finset.sum_range_succ]
    rw [hL, e2, sub_zero]
    exact ((hasSum_laplace hP hg hspec v z).mul_left (z ^ 2)).congr_fun fun n => by
      simp only [show ¬ (n + 2 < 2) by omega, if_false, Nat.add_sub_cancel]
      ring
  have hc := congrFun (coeff_unique hf1 hf2) (k + 2)
  simp only [show ¬ (k + 2 < 2) by omega, if_false, Nat.add_sub_cancel] at hc
  have hfac : ((k + 2).factorial : ℂ) = ((k + 2) * (k + 1) : ℂ) * (k.factorial : ℂ) := by
    rw [Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  have hk : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero k)
  have hk2 : ((k + 2).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  calc ((g + v • P) ^ (k + 2)).trace - ((pinchH hP g + v • P) ^ (k + 2)).trace
      = ((k + 2).factorial : ℂ) * (((k + 2).factorial : ℂ)⁻¹
          * (((g + v • P) ^ (k + 2)).trace - ((pinchH hP g + v • P) ^ (k + 2)).trace)) := by
        field_simp
    _ = ((k + 2).factorial : ℂ) * ((k.factorial : ℂ)⁻¹ * I k) := by rw [hc]
    _ = ((k + 2) * (k + 1) : ℂ) * I k := by
        rw [hfac]
        field_simp

end Density

/- ### The expansion of `(Y + vX)^N` into words -/

section Expansion

variable {d : ℕ}

/-- **Word expansion**: `(Y + vX)^N = Σ_n v^n Σ_W W`, where the inner sum runs over the words of
length `N` with `n` letters `X` and `N - n` letters `Y`. -/
theorem add_smul_pow_eq_sum (X Y : Matrix (Fin d) (Fin d) ℂ) (v : ℂ) (N : ℕ) :
    (Y + v • X) ^ N = ∑ n ∈ Finset.range (N + 1), v ^ n • wordSum X Y N n := by
  induction N with
  | zero => simp [wordSum_zero_zero]
  | succ N ih =>
    have hY : ∑ n ∈ Finset.range (N + 1), v ^ n • (Y * wordSum X Y N n)
        = Y * wordSum X Y N 0
          + ∑ n ∈ Finset.range (N + 1), v ^ (n + 1) • (Y * wordSum X Y N (n + 1)) := by
      rw [Finset.sum_range_succ' (fun n => v ^ n • (Y * wordSum X Y N n)),
        Finset.sum_range_succ (fun n => v ^ (n + 1) • (Y * wordSum X Y N (n + 1))),
        wordSum_eq_zero_of_lt X Y (Nat.lt_succ_self N), Matrix.mul_zero, smul_zero, add_zero,
        pow_zero, one_smul, add_comm]
    rw [pow_succ', ih, Finset.sum_range_succ' (fun n => v ^ n • wordSum X Y (N + 1) n),
      Matrix.add_mul, Finset.mul_sum, Finset.mul_sum]
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, wordSum_succ_succ, wordSum_succ_zero,
      smul_add, Finset.sum_add_distrib, pow_zero, one_smul]
    rw [hY]
    simp only [pow_succ]
    abel

/-- The trace of `(Y + vX)^N` as a polynomial in `v`. -/
theorem trace_add_smul_pow (X Y : Matrix (Fin d) (Fin d) ℂ) (v : ℂ) (N : ℕ) :
    ((Y + v • X) ^ N).trace = ∑ n ∈ Finset.range (N + 1), (wordSum X Y N n).trace * v ^ n := by
  rw [add_smul_pow_eq_sum, trace_sum]
  exact Finset.sum_congr rfl fun n _ => by rw [trace_smul, smul_eq_mul, mul_comm]

/-- The trace of `(Y + vX)^N` for commuting `X`, `Y` (binomial theorem). -/
theorem trace_add_smul_pow_of_commute {X Y : Matrix (Fin d) (Fin d) ℂ} (h : Commute X Y) (v : ℂ)
    (N : ℕ) :
    ((Y + v • X) ^ N).trace
      = ∑ n ∈ Finset.range (N + 1), ((N.choose n : ℂ) * (X ^ n * Y ^ (N - n)).trace) * v ^ n := by
  rw [trace_add_smul_pow]
  exact Finset.sum_congr rfl fun n _ => by rw [wordSum_of_commute h, trace_smul, smul_eq_mul]

/-- Scaling the letter `X`: `Σ_W W(cX, Y) = c^n Σ_W W(X, Y)` for words with `n` letters `X`. -/
theorem wordSum_smul_left (c : ℂ) (X Y : Matrix (Fin d) (Fin d) ℂ) (N k : ℕ) :
    wordSum (c • X) Y N k = c ^ k • wordSum X Y N k := by
  induction N generalizing k with
  | zero =>
    cases k with
    | zero => simp [wordSum_zero_zero]
    | succ k => simp [wordSum_eq_zero_of_lt _ _ (Nat.succ_pos k)]
  | succ N ih =>
    cases k with
    | zero => simp [wordSum_succ_zero, ih]
    | succ k =>
      rw [wordSum_succ_succ, wordSum_succ_succ, ih, ih, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.mul_smul, smul_smul, smul_add, pow_succ']

end Expansion

/- ### The pinching is determined by the commutant -/

section Bridge

variable {P : Matrix (Fin M) (Fin M) ℂ} (hP : P.IsHermitian)
include hP

/-- `Q_p Y Q_q = 0` for `p ≠ q` if `Y` commutes with `P`. -/
lemma sproj_mul_mul_sproj_of_commute {Y : Matrix (Fin M) (Fin M) ℂ} (hY : Commute P Y)
    {p q : ℝ} (hpq : p ≠ q) : sproj hP p * Y * sproj hP q = 0 := by
  have h1 : sproj hP p * (P * Y) * sproj hP q = (p : ℂ) • (sproj hP p * Y * sproj hP q) := by
    rw [← Matrix.mul_assoc, sproj_mul_P, Matrix.smul_mul, Matrix.smul_mul]
  have h2 : sproj hP p * (Y * P) * sproj hP q = (q : ℂ) • (sproj hP p * Y * sproj hP q) := by
    rw [← Matrix.mul_assoc (sproj hP p) Y P, Matrix.mul_assoc (sproj hP p * Y) P (sproj hP q),
      P_mul_sproj, Matrix.mul_smul]
  rw [hY.eq] at h1
  have h3 : ((p : ℂ) - q) • (sproj hP p * Y * sproj hP q) = 0 := by
    rw [sub_smul, ← h1, ← h2, sub_self]
  have hne : ((p : ℂ) - q) ≠ 0 := by
    rw [sub_ne_zero]
    exact_mod_cast hpq
  exact (smul_eq_zero.1 h3).resolve_left hne

/-- A matrix that commutes with `P` commutes with its spectral projections. -/
lemma commute_sproj_of_commute {Y : Matrix (Fin M) (Fin M) ℂ} (hY : Commute P Y) (p : ℝ) :
    Commute (sproj hP p) Y := by
  have hL : Y * sproj hP p = ∑ q ∈ spec hP, sproj hP q * Y * sproj hP p := by
    rw [← Finset.sum_mul, ← Finset.sum_mul, sum_sproj, Matrix.one_mul]
  have hR : sproj hP p * Y = ∑ q ∈ spec hP, sproj hP p * Y * sproj hP q := by
    rw [← Finset.mul_sum, sum_sproj, Matrix.mul_one]
  unfold Commute SemiconjBy
  by_cases hp : p ∈ spec hP
  · rw [hR, hL, Finset.sum_eq_single p
      (fun q _ hqp => sproj_mul_mul_sproj_of_commute hP hY (Ne.symm hqp)) (fun h => absurd hp h),
      Finset.sum_eq_single p (fun q _ hqp => sproj_mul_mul_sproj_of_commute hP hY hqp)
      (fun h => absurd hp h)]
  · rw [hR, hL, Finset.sum_eq_zero fun q hq => sproj_mul_mul_sproj_of_commute hP hY
      (fun h : p = q => hp (h ▸ hq)), Finset.sum_eq_zero fun q hq =>
      sproj_mul_mul_sproj_of_commute hP hY (fun h : q = p => hp (h ▸ hq))]

/-- The pinching commutes with `P`. -/
lemma commute_pinchH (H : Matrix (Fin M) (Fin M) ℂ) : Commute P (pinchH hP H) := by
  unfold Commute SemiconjBy pinchH
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, P_mul_sproj, Matrix.mul_assoc _ _ P, sproj_mul_P,
    Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul]

/-- `Tr(H_d Y) = Tr(H Y)` for every `Y` that commutes with `P`. -/
lemma trace_pinchH_mul_of_commute (H : Matrix (Fin M) (Fin M) ℂ) {Y : Matrix (Fin M) (Fin M) ℂ}
    (hY : Commute P Y) : (pinchH hP H * Y).trace = (H * Y).trace := by
  unfold pinchH
  rw [Finset.sum_mul, trace_sum]
  have h : ∀ p ∈ spec hP,
      (sproj hP p * H * sproj hP p * Y).trace = (H * Y * sproj hP p).trace := by
    intro p _
    rw [Matrix.mul_assoc (sproj hP p * H), (commute_sproj_of_commute hP hY p).eq,
      Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc,
      sproj_mul_self, ← Matrix.mul_assoc]
  rw [Finset.sum_congr rfl h, ← trace_sum, ← Finset.mul_sum, sum_sproj, Matrix.mul_one]

/-- Two matrices in the commutant of `P` with the same traces against the commutant are equal. -/
lemma eq_of_commute_of_trace {X X' : Matrix (Fin M) (Fin M) ℂ} (hX : Commute P X)
    (hX' : Commute P X') (h : ∀ Y, Commute P Y → (X * Y).trace = (X' * Y).trace) : X = X' := by
  have hD : Commute P (X - X') := hX.sub_right hX'
  have hDs : Commute P (X - X')ᴴ := by
    have e := congrArg conjTranspose hD.eq
    rw [conjTranspose_mul, conjTranspose_mul, hP.eq] at e
    exact e.symm
  have h0 : ((X - X') * (X - X')ᴴ).trace = 0 := by
    rw [Matrix.sub_mul, trace_sub, h _ hDs, sub_self]
  exact sub_eq_zero.1 (trace_mul_conjTranspose_self_eq_zero_iff.1 h0)

omit hP in
/-- The pinching does not change if `A` is multiplied by a nonzero scalar. -/
lemma pinchH_smul {A : Matrix (Fin M) (Fin M) ℂ} (hA : A.IsHermitian) {c : ℂ} (hc : c ≠ 0)
    (hcA : (c • A).IsHermitian) (H : Matrix (Fin M) (Fin M) ℂ) : pinchH hcA H = pinchH hA H := by
  have hcomm : ∀ Y : Matrix (Fin M) (Fin M) ℂ, Commute (c • A) Y ↔ Commute A Y := fun Y =>
    ⟨fun h => by simpa [smul_smul, inv_mul_cancel₀ hc] using h.smul_left c⁻¹,
      fun h => h.smul_left c⟩
  refine eq_of_commute_of_trace hA ((hcomm _).1 (commute_pinchH hcA H)) (commute_pinchH hA H)
    fun Y hY => ?_
  rw [trace_pinchH_mul_of_commute hcA H ((hcomm Y).2 hY), trace_pinchH_mul_of_commute hA H hY]

end Bridge

/- ### The exact gap identity (spectrum of `P` in `[0, 1]`) -/

/-- `(n + j + 2)(n + j + 1) C(n + j, n) = C(n + j + 2, n)(j + 2)(j + 1)`. -/
lemma choose_identity (n j : ℕ) :
    (n + j + 2) * (n + j + 1) * (n + j).choose n = (n + j + 2).choose n * ((j + 2) * (j + 1)) := by
  have h1 := Nat.choose_mul_succ_eq (n + j) n
  have h2 := Nat.choose_mul_succ_eq (n + j + 1) n
  rw [show n + j + 1 - n = j + 1 by omega] at h1
  rw [show n + j + 1 + 1 - n = j + 2 by omega, show n + j + 1 + 1 = n + j + 2 by ring] at h2
  calc (n + j + 2) * (n + j + 1) * (n + j).choose n
      = (n + j + 2) * ((n + j).choose n * (n + j + 1)) := by ring
    _ = (n + j + 2) * ((n + j + 1).choose n * (j + 1)) := by rw [h1]
    _ = ((n + j + 1).choose n * (n + j + 2)) * (j + 1) := by ring
    _ = ((n + j + 2).choose n * (j + 2)) * (j + 1) := by rw [h2]
    _ = (n + j + 2).choose n * ((j + 2) * (j + 1)) := by ring

section Gap

variable {P g : Matrix (Fin M) (Fin M) ℂ} (hP : P.IsHermitian) (hg : g.IsHermitian)
  (hspec : ∀ p ∈ spec hP, 0 ≤ p ∧ p ≤ 1)
include hP hg hspec

/-- **Coefficient identity**: the coefficient of `v^n` in the moment identity. -/
theorem coeff_identity (k n : ℕ) :
    (wordSum P g (k + 2) n).trace
        - ((k + 2).choose n : ℂ) * (P ^ n * pinchH hP g ^ (k + 2 - n)).trace
      = ((k + 2) * (k + 1) : ℂ) * (k.choose n : ℂ)
        * ∫ q : ℝ × ℝ, (q.2 : ℂ) ^ n * (q.1 : ℂ) ^ (k - n) * (rhoG P g q.1 q.2 : ℂ) := by
  set J : ℕ → ℂ := fun j =>
    ∫ q : ℝ × ℝ, (q.2 : ℂ) ^ j * (q.1 : ℂ) ^ (k - j) * (rhoG P g q.1 q.2 : ℂ) with hJ
  have hcomm : Commute P (pinchH hP g) := commute_pinchH hP g
  have hA : ∀ v : ℂ, HasSum (fun j => ((wordSum P g (k + 2) j).trace
      - ((k + 2).choose j : ℂ) * (P ^ j * pinchH hP g ^ (k + 2 - j)).trace) * v ^ j)
      (((g + v • P) ^ (k + 2)).trace - ((pinchH hP g + v • P) ^ (k + 2)).trace) := by
    intro v
    have hz : ∀ j ∉ Finset.range (k + 2 + 1), ((wordSum P g (k + 2) j).trace
        - ((k + 2).choose j : ℂ) * (P ^ j * pinchH hP g ^ (k + 2 - j)).trace) * v ^ j = 0 := by
      intro j hj
      have hlt : k + 2 < j := by
        simp only [Finset.mem_range, not_lt] at hj
        omega
      simp [wordSum_eq_zero_of_lt P g hlt, Nat.choose_eq_zero_of_lt hlt]
    rw [trace_add_smul_pow, trace_add_smul_pow_of_commute hcomm, ← Finset.sum_sub_distrib]
    have e : ∑ x ∈ Finset.range (k + 2 + 1), ((wordSum P g (k + 2) x).trace * v ^ x
        - ((k + 2).choose x : ℂ) * (P ^ x * pinchH hP g ^ (k + 2 - x)).trace * v ^ x)
        = ∑ j ∈ Finset.range (k + 2 + 1), ((wordSum P g (k + 2) j).trace
          - ((k + 2).choose j : ℂ) * (P ^ j * pinchH hP g ^ (k + 2 - j)).trace) * v ^ j :=
      Finset.sum_congr rfl fun j _ => by ring
    rw [e]
    exact hasSum_sum_of_ne_finset_zero hz
  have hint : ∀ v : ℂ, ∫ q : ℝ × ℝ, ((q.1 : ℂ) + v * q.2) ^ k * (rhoG P g q.1 q.2 : ℂ)
      = ∑ j ∈ Finset.range (k + 1), ((k.choose j : ℂ) * J j) * v ^ j := by
    intro v
    have e : (fun q : ℝ × ℝ => ((q.1 : ℂ) + v * q.2) ^ k * (rhoG P g q.1 q.2 : ℂ))
        = fun q => ∑ j ∈ Finset.range (k + 1), ((k.choose j : ℂ) * v ^ j)
            * ((q.2 : ℂ) ^ j * (q.1 : ℂ) ^ (k - j) * (rhoG P g q.1 q.2 : ℂ)) := by
      funext q
      rw [add_comm, add_pow, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_pow]
      ring
    rw [e, integral_finsetSum]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_const_mul]
      ring
    · intro j _
      exact (integrable_mul_rhoG hP hg hspec
        (φ := fun q : ℝ × ℝ => (q.2 : ℂ) ^ j * (q.1 : ℂ) ^ (k - j)) (by fun_prop)).const_mul _
  have hB : ∀ v : ℂ, HasSum (fun j => (((k + 2) * (k + 1) : ℂ) * (k.choose j : ℂ) * J j) * v ^ j)
      (((g + v • P) ^ (k + 2)).trace - ((pinchH hP g + v • P) ^ (k + 2)).trace) := by
    intro v
    have hz : ∀ j ∉ Finset.range (k + 1),
        (((k + 2) * (k + 1) : ℂ) * (k.choose j : ℂ) * J j) * v ^ j = 0 := by
      intro j hj
      have hlt : k < j := by
        simp only [Finset.mem_range, not_lt] at hj
        omega
      simp [Nat.choose_eq_zero_of_lt hlt]
    rw [moment_identity hP hg hspec v k, hint v, Finset.mul_sum]
    have e : ∑ i ∈ Finset.range (k + 1), ((k + 2) * (k + 1) : ℂ) * ((k.choose i : ℂ) * J i * v ^ i)
        = ∑ j ∈ Finset.range (k + 1), (((k + 2) * (k + 1) : ℂ) * (k.choose j : ℂ) * J j) * v ^ j :=
      Finset.sum_congr rfl fun j _ => by ring
    rw [e]
    exact hasSum_sum_of_ne_finset_zero hz
  exact congrFun (coeff_unique hA hB) n

/-- **The exact gap identity** (Theorem 1 of `math/01-pinching-theorem.md`, for `P` with spectrum
in `[0, 1]`): with `C = C(n+m, n)` and `ρ = rhoG P g`,
`Σ_W Tr W(P, g) - C Tr(P^n g_d^m) = C m(m-1) ∫∫ τ^n s^{m-2} ρ(s, τ) ds dτ`. -/
theorem gap_identity (n m : ℕ) :
    (wordSum P g (n + m) n).trace - ((n + m).choose n : ℂ) * (P ^ n * pinchH hP g ^ m).trace
      = ((n + m).choose n : ℂ) * ((m * (m - 1) : ℕ) : ℂ)
        * ∫ q : ℝ × ℝ, (q.2 : ℂ) ^ n * (q.1 : ℂ) ^ (m - 2) * (rhoG P g q.1 q.2 : ℂ) := by
  obtain _ | _ | j := m
  · simp [wordSum_self]
  · obtain _ | n := n
    · simp [wordSum_zero_right, trace_pinchH]
    · have h := coeff_identity hP hg hspec n (n + 1)
      rw [Nat.choose_eq_zero_of_lt (Nat.lt_succ_self n), show n + 2 - (n + 1) = 1 by omega,
        show n + 2 = n + 1 + (0 + 1) by omega] at h
      simp only [Nat.cast_zero, mul_zero, zero_mul] at h
      rw [h]
      simp
  · have h := coeff_identity hP hg hspec (n + j) n
    rw [show n + j + 2 - n = j + 1 + 1 by omega, show n + j - n = j + 1 + 1 - 2 by omega,
      show n + j + 2 = n + (j + 1 + 1) by omega] at h
    rw [h]
    have key : ((((n + j : ℕ) : ℂ) + 2) * (((n + j : ℕ) : ℂ) + 1)) * ((n + j).choose n : ℂ)
        = ((n + (j + 1 + 1)).choose n : ℂ) * (((j + 1 + 1) * (j + 1 + 1 - 1) : ℕ) : ℂ) := by
      have e := choose_identity n j
      rw [show n + (j + 1 + 1) = n + j + 2 by omega, show j + 1 + 1 - 1 = j + 1 by omega]
      exact_mod_cast e
    rw [key]

end Gap

/- ### Positivity and the pinching inequality -/

section Main

variable {d : ℕ}

/-- Check of the definition of `pinching`: `E_A(B)` commutes with `A`. -/
theorem commute_pinching {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian)
    (B : Matrix (Fin d) (Fin d) ℂ) : Commute A (pinching hA B) :=
  commute_pinchH hA B

/-- Check of the definition of `pinching`: `Tr E_A(B) = Tr B`. -/
theorem trace_pinching {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian)
    (B : Matrix (Fin d) (Fin d) ℂ) : (pinching hA B).trace = B.trace :=
  trace_pinchH hA B

/-- Check of the definition of `pinching`: `E_A(B) = B` if `B` commutes with `A`. -/
theorem pinching_eq_self_of_commute {A B : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian)
    (h : Commute A B) : pinching hA B = B :=
  eq_of_commute_of_trace hA (commute_pinchH hA B) h fun _ hY => trace_pinchH_mul_of_commute hA B hY

/-- `|⟨w, A w⟩| ≤ Σ_{ij} |A_ij|` for `|w_i| ≤ 1`. -/
lemma norm_star_dotProduct_mulVec_le (A : Matrix (Fin d) (Fin d) ℂ) {w : Fin d → ℂ}
    (hw : ∀ i, ‖w i‖ ≤ 1) : ‖star w ⬝ᵥ (A *ᵥ w)‖ ≤ ∑ i, ∑ j, ‖A i j‖ := by
  simp only [dotProduct, mulVec, Pi.star_apply]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul, norm_star]
  calc ‖w i‖ * ‖∑ j, A i j * w j‖ ≤ 1 * ∑ j, ‖A i j‖ := by
        refine mul_le_mul (hw i) ((norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_))
          (norm_nonneg _) zero_le_one
        rw [norm_mul]
        exact mul_le_of_le_one_right (norm_nonneg _) (hw j)
    _ = ∑ j, ‖A i j‖ := one_mul _

/-- For positive semidefinite `A` and `c > Σ_{ij} |A_ij|`, the spectrum of `c⁻¹ A` lies in
`[0, 1]`. -/
lemma spec_smul_mem_Icc {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.PosSemidef) {c : ℝ}
    (hc : ∑ i, ∑ j, ‖A i j‖ < c) (hP : (((c⁻¹ : ℝ) : ℂ) • A).IsHermitian) :
    ∀ p ∈ spec hP, 0 ≤ p ∧ p ≤ 1 := by
  have hc0 : 0 < c := lt_of_le_of_lt (by positivity) hc
  intro p hp
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
  set v := hP.eigenvectorBasis i with hv_def
  have hv1 : ‖v‖ = 1 := hP.eigenvectorBasis.orthonormal.1 i
  have hw : ∀ j, ‖v.ofLp j‖ ≤ 1 := fun j => (PiLp.norm_apply_le v j).trans hv1.le
  have hself : star v.ofLp ⬝ᵥ v.ofLp = 1 := by
    have h := EuclideanSpace.inner_eq_star_dotProduct v v
    rw [inner_self_eq_norm_sq_to_K, hv1] at h
    rw [dotProduct_comm, ← h]
    simp
  have hPv := hP.mulVec_eigenvectorBasis i
  rw [← hv_def] at hPv
  have key : (hP.eigenvalues i : ℂ) = ((c⁻¹ : ℝ) : ℂ) * (star v.ofLp ⬝ᵥ (A *ᵥ v.ofLp)) := by
    have e := congrArg (fun x => star v.ofLp ⬝ᵥ x) hPv
    simp only [Matrix.smul_mulVec, dotProduct_smul, hself, Complex.real_smul, smul_eq_mul,
      mul_one] at e
    exact e.symm
  have hnn := Complex.nonneg_iff.mp (hA.dotProduct_mulVec_nonneg v.ofLp)
  have hle : (star v.ofLp ⬝ᵥ (A *ᵥ v.ofLp)).re ≤ ∑ i, ∑ j, ‖A i j‖ :=
    (Complex.re_le_norm _).trans (norm_star_dotProduct_mulVec_le A hw)
  have hlam : hP.eigenvalues i = c⁻¹ * (star v.ofLp ⬝ᵥ (A *ᵥ v.ofLp)).re := by
    have e := congrArg Complex.re key
    simpa using e
  rw [hlam]
  constructor
  · exact mul_nonneg (inv_nonneg.2 hc0.le) hnn.1
  · rw [inv_mul_le_iff₀ hc0]
    linarith

/-- The moments `∫∫ τ^n s^j ρ` are nonnegative for `B ≥ 0` and `spec P ⊆ [0, 1]`: on the
support of `ρ`, `s ≥ λ_min(B) ≥ 0` and `τ > 0`. -/
lemma integral_moment_nonneg {P B : Matrix (Fin d) (Fin d) ℂ} (hP : P.IsHermitian)
    (hB : B.PosSemidef) (hspec : ∀ p ∈ spec hP, 0 ≤ p ∧ p ≤ 1) (n j : ℕ) :
    0 ≤ ∫ q : ℝ × ℝ, q.2 ^ n * q.1 ^ j * rhoG P B q.1 q.2 := by
  refine integral_nonneg fun q => ?_
  by_cases h0 : rhoG P B q.1 q.2 = 0
  · simp [h0]
  · have hs : 0 ≤ q.1 := by
      by_contra hc
      exact h0 (rhoG_eq_zero_of_semidef hP hB.isHermitian
        (Or.inl fun i => (not_le.1 hc).le.trans (hB.eigenvalues_nonneg i)) q.2)
    have hτ : 0 < q.2 := by
      by_contra hc
      exact h0 (rhoG_eq_zero_of_not_mem_Ioo hP hB.isHermitian hspec (fun h => hc h.1) q.1)
    exact mul_nonneg (mul_nonneg (pow_nonneg hτ.le n) (pow_nonneg hs j)) (rhoG_nonneg _ _ _ _)

/-- **The pinching inequality with its gap**: for positive semidefinite `A`, `B` and all `n`,
`m`, `p_{n,m}(A, B) = Tr(A^n E_A(B)^m) + r` with `r ≥ 0`. Explicitly
`r = c^n m(m-1) ∫∫ τ^n s^{m-2} ρ(s, τ) ds dτ` with `c = 1 + Σ_{ij} |A_ij|` and `ρ` the density
of Theorem A for `(g, P) = (B, A/c)`. -/
theorem wordAverage_eq_trace_pinching_add {A B : Matrix (Fin d) (Fin d) ℂ} (hA : A.PosSemidef)
    (hB : B.PosSemidef) (n m : ℕ) :
    ∃ r : ℝ, 0 ≤ r ∧ wordAverage n m A B = (A ^ n * pinching hA.isHermitian B ^ m).trace + r := by
  set c : ℝ := 1 + ∑ i, ∑ j, ‖A i j‖ with hc_def
  have hc : ∑ i, ∑ j, ‖A i j‖ < c := by linarith
  have hc0 : 0 < c := lt_of_le_of_lt (by positivity) hc
  have hP : (((c⁻¹ : ℝ) : ℂ) • A).IsHermitian :=
    hA.isHermitian.smul (Complex.conj_ofReal _ : IsSelfAdjoint ((c⁻¹ : ℝ) : ℂ))
  have hspec := spec_smul_mem_Icc hA hc hP
  have hcinv : ((c⁻¹ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (inv_pos.2 hc0).ne'
  have hpinch : pinching hA.isHermitian B = pinchH hP B :=
    (pinchH_smul hA.isHermitian hcinv hP B).symm
  have hAP : A = (c : ℂ) • (((c⁻¹ : ℝ) : ℂ) • A) := by
    rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hc0.ne', Complex.ofReal_one, one_smul]
  have hgap := gap_identity hP hB.isHermitian hspec n m
  have hI : ∫ q : ℝ × ℝ, (q.2 : ℂ) ^ n * (q.1 : ℂ) ^ (m - 2)
        * (rhoG (((c⁻¹ : ℝ) : ℂ) • A) B q.1 q.2 : ℂ)
      = ((∫ q : ℝ × ℝ, q.2 ^ n * q.1 ^ (m - 2) * rhoG (((c⁻¹ : ℝ) : ℂ) • A) B q.1 q.2 : ℝ)
          : ℂ) := by
    rw [← integral_complex_ofReal]
    congr 1
    funext q
    push_cast
    ring
  have hIn := integral_moment_nonneg hP hB hspec n (m - 2)
  set I : ℝ := ∫ q : ℝ × ℝ, q.2 ^ n * q.1 ^ (m - 2) * rhoG (((c⁻¹ : ℝ) : ℂ) • A) B q.1 q.2
  refine ⟨c ^ n * ((m * (m - 1) : ℕ) : ℝ) * I, by positivity, ?_⟩
  rw [hI] at hgap
  have hC : ((n + m).choose n : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Nat.choose_pos (Nat.le_add_right n m)).ne'
  have hW : wordSum A B (n + m) n = (c : ℂ) ^ n • wordSum (((c⁻¹ : ℝ) : ℂ) • A) B (n + m) n := by
    conv_lhs => rw [hAP]
    rw [wordSum_smul_left]
  have hApow : A ^ n = (c : ℂ) ^ n • (((c⁻¹ : ℝ) : ℂ) • A) ^ n := by
    conv_lhs => rw [hAP]
    rw [smul_pow]
  rw [wordAverage_eq, hpinch, hW, hApow, trace_smul, Matrix.smul_mul, trace_smul,
    sub_eq_iff_eq_add.1 hgap]
  push_cast
  field_simp
  ring

/-- **Dinh's Conjecture 5.1 for all word lengths** (in the complex order):
`Tr(A^n E_A(B)^m) ≤ p_{n,m}(A, B)` for positive semidefinite `A`, `B`; the difference is a
nonnegative real number. -/
theorem trace_pinching_le_wordAverage {A B : Matrix (Fin d) (Fin d) ℂ} (hA : A.PosSemidef)
    (hB : B.PosSemidef) (n m : ℕ) :
    (A ^ n * pinching hA.isHermitian B ^ m).trace ≤ wordAverage n m A B := by
  obtain ⟨r, hr, h⟩ := wordAverage_eq_trace_pinching_add hA hB n m
  rw [h]
  exact le_add_of_nonneg_right (Complex.zero_le_real.2 hr)

/-- **The pinching inequality** `PinchingInequality` (T. H. Dinh, Conjecture 5.1) holds for all
`n`, `m`. -/
theorem pinchingInequality : PinchingInequality := by
  intro d A B hA hB n m
  obtain ⟨r, hr, h⟩ := wordAverage_eq_trace_pinching_add hA hB n m
  rw [h, Complex.add_re, Complex.ofReal_re]
  linarith

end Main

end OpenQuantumProblem40
