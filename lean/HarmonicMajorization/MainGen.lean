import HarmonicMajorization.RIG4b
import HarmonicMajorization.TheoremCGen

/-!
# Theorems A, B, C for general `0 ≤ B ≤ 1`, without hypotheses

Authors: Ansh Mishra, Aryan Senthilkumar.  License: MIT.

The multi-line Radon identity `hyp_RI_gen M` (`HarmonicMajorization/RIG4b.lean`) discharges the
hypothesis `Hyp_RI_gen M` of `TheoremAGen`, `MarginalGen`, `TheoremBGen`, `TheoremCGen`.

Setting (THEOREMS.md, Section 0): `0 ≤ B ≤ 1` (`B.PosSemidef`, `(1 - B).PosSemidef`), `P = 1 - B` with
distinct eigenvalues `p ∈ spec P` and spectral projections `Q_p = sproj hP p`, `g` Hermitian,
`g_d = Σ_p Q_p g Q_p = pinchH hP g`, `ρ = rhoG P g` (`ρ(s, τ) = (1/2π) Σ_i |Im ξ_i(s, τ)|`, `ξ_i` the roots
of `det(g - s - ξ(P - τ))`), `h_λ = hLam λ`, `V = stripBalayage ρ`.

Main results (no hypotheses):
* `theoremA`: `Tr e^{ag - tP} - Tr e^{a g_d - tP} = a² ∫∫ e^{as - tτ} ρ(s, τ) ds dτ` for all `(a, t) ∈ ℂ²`
  (for any Hermitian `P` with spectrum in `[0, 1]`);
* `tau_marginal`, `sine_moment`: the `τ`-marginal of `ρ` in Laplace form and the sine moment;
* `theoremB`, `theoremB_ineq`, `theoremB_eq_iff`: Theorem B (left edge): the defect identity
  `Σ_{spec(B+ig)} h_λ - Σ_{spec(B+ig_d)} h_λ = V(λ) ≥ 0`, with equality iff `[B, g] = 0`;
* `theoremC`, `theoremC_balayage`: Theorem C (quantitative form).
-/

set_option autoImplicit false

namespace HarmonicMajorization

open Matrix Complex MeasureTheory
open scoped Real ComplexOrder
open OQP27.StripL3a (stripKernel stripBalayage hLam)

variable {M : ℕ}

section A

variable {P g : Matrix (Fin M) (Fin M) ℂ} (hP : P.IsHermitian) (hg : g.IsHermitian)
  (hspec : ∀ p ∈ spec hP, 0 ≤ p ∧ p ≤ 1)
include hP hg hspec

/-- **Theorem A** (THEOREMS.md, Section 1; no hypotheses): for all `(a, t) ∈ ℂ²`,
`Tr e^{ag - tP} - Tr e^{a g_d - tP} = a² ∫∫ e^{as - tτ} ρ(s, τ) ds dτ`. -/
theorem theoremA (a t : ℂ) : bmvDG hP g a t = a ^ 2 * laplaceG P g a t :=
  theoremA_gen hP hg hspec (hyp_RI_gen M) a t

/-- **The `τ`-marginal** (Laplace form, no hypotheses): for `t ≠ 0`,
`∫∫ e^{-tτ} ρ = Σ_{p<q} Tr(g Q_p g Q_q) (e^{-tp} - e^{-tq})/(t(q - p))`. -/
theorem tau_marginal (t : ℂ) (ht : t ≠ 0) :
    laplaceG P g 0 t
      = ∑ p ∈ spec hP, ∑ q ∈ spec hP, if p < q then
          (g * sproj hP p * g * sproj hP q).trace
            * ((cexp (-t * p) - cexp (-t * q)) / (t * ((q : ℂ) - p))) else 0 :=
  laplaceG_zero hP hg hspec (hyp_RI_gen M) t ht

/-- **The sine moment of `ρ`** (no hypotheses):
`∫∫ sin(πτ) ρ = Σ_{p<q} ‖Q_q g Q_p‖_F² (cos πp - cos πq)/(π(q - p))`. -/
theorem sine_moment :
    ∫ q : ℝ × ℝ, Real.sin (π * q.2) * rhoG P g q.1 q.2
      = ∑ p ∈ spec hP, ∑ q ∈ spec hP, if p < q then
          (∑ i, ∑ j, ‖(sproj hP q * g * sproj hP p) i j‖ ^ 2)
            * ((Real.cos (π * p) - Real.cos (π * q)) / (π * (q - p))) else 0 :=
  integral_sin_mul_rhoG hP hg hspec (hyp_RI_gen M)

end A

section BC

variable {B g : Matrix (Fin M) (Fin M) ℂ} (hB0 : B.PosSemidef) (hB1 : (1 - B).PosSemidef)
  (hg : g.IsHermitian)
include hB0 hB1 hg

/-- **Theorem B, left edge** (THEOREMS.md, Section 1; no hypotheses): for every real `λ`,
`Σ_{ν ∈ spec(B+ig)} h_λ(ν) - Σ_{ν ∈ spec(B+ig_d)} h_λ(ν) = V(λ)`. -/
theorem theoremB (lam : ℝ) :
    ((B + I • g).charpoly.roots.map (hLam lam)).sum
      - ((B + I • pinchH hB1.isHermitian g).charpoly.roots.map (hLam lam)).sum
      = stripBalayage (rhoG (1 - B) g) lam :=
  theoremB_gen hB0 hB1 hg (hyp_RI_gen M) lam

/-- **Theorem B, left edge, inequality**: `Σ_{spec(B+ig_d)} h_λ ≤ Σ_{spec(B+ig)} h_λ`. -/
theorem theoremB_ineq (lam : ℝ) :
    ((B + I • pinchH hB1.isHermitian g).charpoly.roots.map (hLam lam)).sum
      ≤ ((B + I • g).charpoly.roots.map (hLam lam)).sum :=
  theoremB_gen_ineq hB0 hB1 hg (hyp_RI_gen M) lam

/-- **Theorem B, equality case**: equality at one `λ` iff `[B, g] = 0`. -/
theorem theoremB_eq_iff (lam : ℝ) :
    ((B + I • g).charpoly.roots.map (hLam lam)).sum
        = ((B + I • pinchH hB1.isHermitian g).charpoly.roots.map (hLam lam)).sum
      ↔ Commute B g :=
  theoremB_gen_eq_iff hB0 hB1 hg (hyp_RI_gen M) lam

/-- **Theorem C** (THEOREMS.md, Section 1; no hypotheses): for every real `λ`, with
`R = |λ| + ‖g‖`,
`V(λ) ≥ 1/(2(1 + cosh(πR))) · Σ_{p<q} ‖Q_p g Q_q‖_F² (1/(q - p)) ∫_p^q sin(πτ) dτ`. -/
theorem theoremC_balayage (lam : ℝ) :
    1 / (2 * (1 + Real.cosh (π * (|lam| + opNorm g))))
        * (∑ p ∈ spec hB1.isHermitian, ∑ q ∈ spec hB1.isHermitian, if p < q then
            frobNorm (sproj hB1.isHermitian p * g * sproj hB1.isHermitian q) ^ 2
              * (1 / (q - p) * ∫ τ in p..q, Real.sin (π * τ)) else 0)
      ≤ stripBalayage (rhoG (1 - B) g) lam :=
  stripBalayage_ge_gen hB0 hB1 hg (hyp_RI_gen M) lam

/-- **Theorem C** in terms of the eigenvalues: for every real `λ`, with `R = |λ| + ‖g‖`,
`Σ_{spec(B+ig)} h_λ - Σ_{spec(B+ig_d)} h_λ
  ≥ 1/(2(1 + cosh(πR))) · Σ_{p<q} ‖Q_p g Q_q‖_F² (1/(q - p)) ∫_p^q sin(πτ) dτ`. -/
theorem theoremC (lam : ℝ) :
    1 / (2 * (1 + Real.cosh (π * (|lam| + opNorm g))))
        * (∑ p ∈ spec hB1.isHermitian, ∑ q ∈ spec hB1.isHermitian, if p < q then
            frobNorm (sproj hB1.isHermitian p * g * sproj hB1.isHermitian q) ^ 2
              * (1 / (q - p) * ∫ τ in p..q, Real.sin (π * τ)) else 0)
      ≤ ((B + I • g).charpoly.roots.map (hLam lam)).sum
        - ((B + I • pinchH hB1.isHermitian g).charpoly.roots.map (hLam lam)).sum :=
  theoremC_gen hB0 hB1 hg (hyp_RI_gen M) lam

end BC

end HarmonicMajorization
