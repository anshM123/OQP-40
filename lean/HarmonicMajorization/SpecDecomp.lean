import Mathlib.Analysis.Matrix.Spectrum
import OQP27.StripBMV

/-!
# Spectral decomposition of a Hermitian matrix and the pinching

Authors: Ansh Mishra, Aryan Senthilkumar.  License: MIT.

For a Hermitian `P` (`hP : P.IsHermitian`) with eigenvalues `λ_i` and eigenvector unitary `U`:
* `fcalc hP f = U diag(f) U*` (functional calculus on the eigenbasis), multiplicative and additive;
* `spec hP` the finite set of distinct eigenvalues, `sproj hP p` the spectral projection for `p`;
* `pinchH hP H = Σ_{p ∈ spec} Q_p H Q_p`, the pinching onto the eigenspaces of `P`;
* `exp_smul_eq_sum`: `e^{cP} = Σ_p e^{cp} Q_p`; `inv_sub_eq_fcalc`: `(P - τ)⁻¹ = φ((λ - τ)⁻¹)` for
  `τ ∉ spec P`;
* `trace_pinchH_mul_fcalc`: `Tr(H_d φ(P)) = Tr(H φ(P))`; `isHermitian_inv_mul_pinchH`:
  `(P - τ)⁻¹ H_d` is Hermitian (so the pinched pencil has real roots).

No hypotheses.
-/

set_option autoImplicit false

namespace HarmonicMajorization

open Matrix Complex

variable {M : ℕ}

section Spec

variable {P : Matrix (Fin M) (Fin M) ℂ} (hP : P.IsHermitian)

/-- The eigenvector unitary `U` of `P`, as a matrix. -/
noncomputable def eU : Matrix (Fin M) (Fin M) ℂ := (hP.eigenvectorUnitary : Matrix (Fin M) (Fin M) ℂ)

/-- Functional calculus on the eigenbasis: `φ(f) = U diag(f) U*`. -/
noncomputable def fcalc (f : Fin M → ℂ) : Matrix (Fin M) (Fin M) ℂ :=
  eU hP * diagonal f * star (eU hP)

lemma eU_mul_star : eU hP * star (eU hP) = 1 := Unitary.coe_mul_star_self _

lemma star_mul_eU : star (eU hP) * eU hP = 1 := Unitary.coe_star_mul_self _

lemma fcalc_mul (f g : Fin M → ℂ) : fcalc hP f * fcalc hP g = fcalc hP (f * g) := by
  unfold fcalc
  have e : eU hP * diagonal f * star (eU hP) * (eU hP * diagonal g * star (eU hP))
      = eU hP * diagonal f * (star (eU hP) * eU hP) * diagonal g * star (eU hP) := by
    simp only [Matrix.mul_assoc]
  rw [e, star_mul_eU, Matrix.mul_one, Matrix.mul_assoc (eU hP) (diagonal f),
    diagonal_mul_diagonal]
  rfl

lemma fcalc_add (f g : Fin M → ℂ) : fcalc hP (f + g) = fcalc hP f + fcalc hP g := by
  unfold fcalc
  rw [show diagonal (f + g) = diagonal f + diagonal g from (diagonal_add f g).symm, Matrix.mul_add,
    Matrix.add_mul]

lemma fcalc_sub (f g : Fin M → ℂ) : fcalc hP (f - g) = fcalc hP f - fcalc hP g := by
  unfold fcalc
  rw [show diagonal (f - g) = diagonal f - diagonal g from (diagonal_sub f g).symm, Matrix.mul_sub,
    Matrix.sub_mul]

lemma fcalc_smul (c : ℂ) (f : Fin M → ℂ) : fcalc hP (c • f) = c • fcalc hP f := by
  unfold fcalc
  rw [diagonal_smul, Matrix.mul_smul, Matrix.smul_mul]

lemma fcalc_one : fcalc hP 1 = 1 := by
  unfold fcalc
  rw [show (diagonal (1 : Fin M → ℂ)) = 1 from diagonal_one, Matrix.mul_one, eU_mul_star]

lemma fcalc_const (c : ℂ) : fcalc hP (fun _ => c) = c • 1 := by
  rw [show (fun _ : Fin M => c) = c • (1 : Fin M → ℂ) by funext; simp, fcalc_smul, fcalc_one]

lemma fcalc_sum {ι : Type*} (s : Finset ι) (f : ι → Fin M → ℂ) :
    fcalc hP (∑ k ∈ s, f k) = ∑ k ∈ s, fcalc hP (f k) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    unfold fcalc
    rw [show (diagonal (0 : Fin M → ℂ)) = 0 from diagonal_zero, Matrix.mul_zero, Matrix.zero_mul]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, fcalc_add, ih]

/-- `P = φ(λ)`. -/
lemma fcalc_eigenvalues : fcalc hP (fun i => (hP.eigenvalues i : ℂ)) = P := by
  unfold fcalc eU
  conv_rhs => rw [hP.spectral_theorem, Unitary.conjStarAlgAut_apply]
  rfl

lemma fcalc_conjTranspose (f : Fin M → ℂ) : (fcalc hP f)ᴴ = fcalc hP (star f) := by
  unfold fcalc
  rw [conjTranspose_mul, conjTranspose_mul, diagonal_conjTranspose, Matrix.star_eq_conjTranspose,
    conjTranspose_conjTranspose, Matrix.mul_assoc]

lemma isHermitian_fcalc_ofReal (f : Fin M → ℝ) : (fcalc hP (fun i => (f i : ℂ))).IsHermitian := by
  unfold IsHermitian
  rw [fcalc_conjTranspose]
  congr 1
  funext i
  simp [Complex.conj_ofReal]

lemma trace_fcalc (f : Fin M → ℂ) : (fcalc hP f).trace = ∑ i, f i := by
  unfold fcalc
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, star_mul_eU, Matrix.one_mul, trace_diagonal]

/-! ### Spectrum and spectral projections -/

/-- The distinct eigenvalues of `P`. -/
noncomputable def spec : Finset ℝ := Finset.univ.image hP.eigenvalues

lemma eigenvalues_mem_spec (i : Fin M) : hP.eigenvalues i ∈ spec hP :=
  Finset.mem_image_of_mem _ (Finset.mem_univ i)

/-- The indicator of the eigenvalue `p`. -/
noncomputable def ind (p : ℝ) : Fin M → ℂ := fun i => if hP.eigenvalues i = p then 1 else 0

/-- The spectral projection `Q_p` of `P` for the eigenvalue `p`. -/
noncomputable def sproj (p : ℝ) : Matrix (Fin M) (Fin M) ℂ := fcalc hP (ind hP p)

lemma ind_mul_ind (p q : ℝ) : ind hP p * ind hP q = if p = q then ind hP p else 0 := by
  by_cases hpq : p = q
  · rw [if_pos hpq]
    subst hpq
    funext i
    simp only [ind, Pi.mul_apply]
    split_ifs <;> simp
  · rw [if_neg hpq]
    funext i
    simp only [ind, Pi.mul_apply, Pi.zero_apply]
    split_ifs with h1 h2 <;> simp_all

lemma sproj_mul_sproj (p q : ℝ) :
    sproj hP p * sproj hP q = if p = q then sproj hP p else 0 := by
  unfold sproj
  rw [fcalc_mul, ind_mul_ind]
  split_ifs
  · rfl
  · unfold fcalc
    rw [show (diagonal (0 : Fin M → ℂ)) = 0 from diagonal_zero, Matrix.mul_zero, Matrix.zero_mul]

lemma sproj_mul_self (p : ℝ) : sproj hP p * sproj hP p = sproj hP p := by
  rw [sproj_mul_sproj, if_pos rfl]

lemma sproj_mul_of_ne {p q : ℝ} (h : p ≠ q) : sproj hP p * sproj hP q = 0 := by
  rw [sproj_mul_sproj, if_neg h]

lemma isHermitian_sproj (p : ℝ) : (sproj hP p).IsHermitian := by
  have e : ind hP p = fun i => ((if hP.eigenvalues i = p then 1 else 0 : ℝ) : ℂ) := by
    funext i; simp only [ind]; split_ifs <;> simp
  unfold sproj
  rw [e]
  exact isHermitian_fcalc_ofReal hP _

lemma sum_ind : ∑ p ∈ spec hP, ind hP p = 1 := by
  funext i
  simp only [Finset.sum_apply, ind, Pi.one_apply]
  rw [Finset.sum_ite_eq (spec hP) (hP.eigenvalues i) (fun _ => (1 : ℂ))]
  rw [if_pos (eigenvalues_mem_spec hP i)]

lemma sum_sproj : ∑ p ∈ spec hP, sproj hP p = 1 := by
  unfold sproj
  rw [← fcalc_sum, sum_ind, fcalc_one]

/-- `f(λ) = Σ_p f(p) 1_{λ = p}`. -/
lemma comp_eq_sum_ind (g : ℝ → ℂ) :
    (fun i => g (hP.eigenvalues i)) = ∑ p ∈ spec hP, g p • ind hP p := by
  funext i
  simp only [Finset.sum_apply, Pi.smul_apply, ind, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq (spec hP) (hP.eigenvalues i) g, if_pos (eigenvalues_mem_spec hP i)]

/-- `φ(g ∘ λ) = Σ_p g(p) Q_p`. -/
lemma fcalc_comp (g : ℝ → ℂ) :
    fcalc hP (fun i => g (hP.eigenvalues i)) = ∑ p ∈ spec hP, g p • sproj hP p := by
  rw [comp_eq_sum_ind, fcalc_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [fcalc_smul]
  rfl

/-- `φ(g ∘ λ) Q_p = g(p) Q_p`. -/
lemma fcalc_comp_mul_sproj (g : ℝ → ℂ) (p : ℝ) :
    fcalc hP (fun i => g (hP.eigenvalues i)) * sproj hP p = g p • sproj hP p := by
  unfold sproj
  rw [fcalc_mul, ← fcalc_smul]
  congr 1
  funext i
  simp only [Pi.mul_apply, Pi.smul_apply, ind, smul_eq_mul]
  split_ifs with h
  · rw [h]
  · simp

lemma sproj_mul_fcalc_comp (g : ℝ → ℂ) (p : ℝ) :
    sproj hP p * fcalc hP (fun i => g (hP.eigenvalues i)) = g p • sproj hP p := by
  unfold sproj
  rw [fcalc_mul, ← fcalc_smul]
  congr 1
  funext i
  simp only [Pi.mul_apply, Pi.smul_apply, ind, smul_eq_mul]
  split_ifs with h
  · rw [h, mul_comm]
  · simp

lemma P_mul_sproj (p : ℝ) : P * sproj hP p = (p : ℂ) • sproj hP p := by
  have h := fcalc_comp_mul_sproj hP (fun x => (x : ℂ)) p
  rwa [fcalc_eigenvalues] at h

lemma sproj_mul_P (p : ℝ) : sproj hP p * P = (p : ℂ) • sproj hP p := by
  have h := sproj_mul_fcalc_comp hP (fun x => (x : ℂ)) p
  rwa [fcalc_eigenvalues] at h

lemma sum_smul_sproj : ∑ p ∈ spec hP, (p : ℂ) • sproj hP p = P := by
  rw [← fcalc_comp hP (fun x => (x : ℂ)), fcalc_eigenvalues]

/-! ### The exponential and the resolvent -/

/-- `e^{cP} = Σ_p e^{cp} Q_p`. -/
theorem exp_smul_eq_sum (c : ℂ) :
    NormedSpace.exp (c • P) = ∑ p ∈ spec hP, cexp (c * p) • sproj hP p := by
  calc NormedSpace.exp (c • P) = NormedSpace.exp (c • P) * ∑ p ∈ spec hP, sproj hP p := by
        rw [sum_sproj, Matrix.mul_one]
    _ = ∑ p ∈ spec hP, NormedSpace.exp (c • P) * sproj hP p := Finset.mul_sum _ _ _
    _ = ∑ p ∈ spec hP, cexp (c * p) • sproj hP p := by
        refine Finset.sum_congr rfl fun p _ => ?_
        apply OQP27.StripL3b.exp_mul_of_mul_eq_smul
        rw [Matrix.smul_mul, P_mul_sproj, smul_smul]

lemma exp_smul_eq_fcalc (c : ℂ) :
    NormedSpace.exp (c • P) = fcalc hP (fun i => cexp (c * hP.eigenvalues i)) := by
  rw [exp_smul_eq_sum, fcalc_comp hP (fun x => cexp (c * x))]

/-- `P - τ = φ(λ - τ)`. -/
lemma sub_smul_eq_fcalc (τ : ℝ) :
    P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ)
      = fcalc hP (fun i => ((hP.eigenvalues i - τ : ℝ) : ℂ)) := by
  rw [show (fun i => ((hP.eigenvalues i - τ : ℝ) : ℂ))
      = (fun i => (hP.eigenvalues i : ℂ)) - (fun _ => (τ : ℂ)) by funext i; push_cast; rfl,
    fcalc_sub, fcalc_eigenvalues, fcalc_const]

/-- For `τ ∉ spec P`: `(P - τ) φ((λ - τ)⁻¹) = 1`. -/
lemma sub_mul_fcalc_inv {τ : ℝ} (hτ : τ ∉ spec hP) :
    (P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ))
      * fcalc hP (fun i => ((hP.eigenvalues i - τ : ℝ) : ℂ)⁻¹) = 1 := by
  rw [sub_smul_eq_fcalc hP τ, fcalc_mul]
  have : (fun i => ((hP.eigenvalues i - τ : ℝ) : ℂ)) * (fun i => ((hP.eigenvalues i - τ : ℝ) : ℂ)⁻¹)
      = 1 := by
    funext i
    have hne : ((hP.eigenvalues i - τ : ℝ) : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero, sub_ne_zero]
      intro h
      exact hτ (h ▸ eigenvalues_mem_spec hP i)
    simp only [Pi.mul_apply, Pi.one_apply]
    exact mul_inv_cancel₀ hne
  rw [this, fcalc_one]

/-- For `τ ∉ spec P`: `(P - τ)⁻¹ = φ((λ - τ)⁻¹)`. -/
theorem inv_sub_eq_fcalc {τ : ℝ} (hτ : τ ∉ spec hP) :
    (P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ))⁻¹
      = fcalc hP (fun i => ((hP.eigenvalues i - τ : ℝ) : ℂ)⁻¹) :=
  Matrix.inv_eq_right_inv (sub_mul_fcalc_inv hP hτ)

lemma isUnit_det_sub {τ : ℝ} (hτ : τ ∉ spec hP) :
    IsUnit (P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ)).det :=
  Matrix.isUnit_det_of_right_inverse (sub_mul_fcalc_inv hP hτ)

lemma inv_sub_mul_self {τ : ℝ} (hτ : τ ∉ spec hP) :
    (P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ))⁻¹ * (P - (τ : ℂ) • 1) = 1 :=
  Matrix.nonsing_inv_mul _ (isUnit_det_sub hP hτ)

/-! ### The pinching -/

lemma isHermitian_finset_sum {ι : Type*} (s : Finset ι) (f : ι → Matrix (Fin M) (Fin M) ℂ)
    (h : ∀ i ∈ s, (f i).IsHermitian) : (∑ i ∈ s, f i).IsHermitian := by
  unfold IsHermitian
  rw [Matrix.conjTranspose_sum]
  exact Finset.sum_congr rfl fun i hi => (h i hi).eq

/-- The pinching `H_d = Σ_{p ∈ spec P} Q_p H Q_p` onto the eigenspaces of `P`. -/
noncomputable def pinchH (H : Matrix (Fin M) (Fin M) ℂ) : Matrix (Fin M) (Fin M) ℂ :=
  ∑ p ∈ spec hP, sproj hP p * H * sproj hP p

lemma pinchH_add (A B : Matrix (Fin M) (Fin M) ℂ) :
    pinchH hP (A + B) = pinchH hP A + pinchH hP B := by
  unfold pinchH
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Matrix.mul_add, Matrix.add_mul]

lemma pinchH_sub (A B : Matrix (Fin M) (Fin M) ℂ) :
    pinchH hP (A - B) = pinchH hP A - pinchH hP B := by
  unfold pinchH
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Matrix.mul_sub, Matrix.sub_mul]

lemma pinchH_smul (c : ℂ) (A : Matrix (Fin M) (Fin M) ℂ) :
    pinchH hP (c • A) = c • pinchH hP A := by
  unfold pinchH
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Matrix.mul_smul, Matrix.smul_mul]

/-- `Q_q H_d = Q_q H Q_q`. -/
lemma sproj_mul_pinchH (H : Matrix (Fin M) (Fin M) ℂ) {q : ℝ} (hq : q ∈ spec hP) :
    sproj hP q * pinchH hP H = sproj hP q * H * sproj hP q := by
  unfold pinchH
  rw [Finset.mul_sum, Finset.sum_eq_single q]
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, sproj_mul_self]
  · intro p _ hpq
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, sproj_mul_of_ne hP (Ne.symm hpq), Matrix.zero_mul,
      Matrix.zero_mul]
  · intro h; exact absurd hq h

lemma pinchH_mul_sproj (H : Matrix (Fin M) (Fin M) ℂ) {q : ℝ} (hq : q ∈ spec hP) :
    pinchH hP H * sproj hP q = sproj hP q * H * sproj hP q := by
  unfold pinchH
  rw [Finset.sum_mul, Finset.sum_eq_single q]
  · rw [Matrix.mul_assoc, sproj_mul_self]
  · intro p _ hpq
    rw [Matrix.mul_assoc, sproj_mul_of_ne hP hpq, Matrix.mul_zero]
  · intro h; exact absurd hq h

lemma pinchH_one : pinchH hP 1 = 1 := by
  unfold pinchH
  calc ∑ p ∈ spec hP, sproj hP p * 1 * sproj hP p = ∑ p ∈ spec hP, sproj hP p :=
        Finset.sum_congr rfl fun p _ => by rw [Matrix.mul_one, sproj_mul_self]
    _ = 1 := sum_sproj hP

lemma pinchH_fcalc_comp (g : ℝ → ℂ) :
    pinchH hP (fcalc hP (fun i => g (hP.eigenvalues i)))
      = fcalc hP (fun i => g (hP.eigenvalues i)) := by
  unfold pinchH
  calc ∑ p ∈ spec hP, sproj hP p * fcalc hP (fun i => g (hP.eigenvalues i)) * sproj hP p
      = ∑ p ∈ spec hP, g p • sproj hP p := Finset.sum_congr rfl fun p _ => by
        rw [Matrix.mul_assoc, fcalc_comp_mul_sproj, Matrix.mul_smul, sproj_mul_self]
    _ = _ := (fcalc_comp hP g).symm

lemma pinchH_self : pinchH hP P = P := by
  have h := pinchH_fcalc_comp hP (fun x => (x : ℂ))
  rwa [fcalc_eigenvalues] at h

lemma isHermitian_pinchH {H : Matrix (Fin M) (Fin M) ℂ} (hH : H.IsHermitian) :
    (pinchH hP H).IsHermitian := by
  unfold pinchH
  refine isHermitian_finset_sum _ _ fun p _ => ?_
  unfold IsHermitian
  rw [conjTranspose_mul, conjTranspose_mul, (isHermitian_sproj hP p).eq, hH.eq, Matrix.mul_assoc]

/-- `Tr(H_d · φ(g ∘ λ)) = Tr(H · φ(g ∘ λ))`. -/
lemma trace_pinchH_mul_fcalc (H : Matrix (Fin M) (Fin M) ℂ) (g : ℝ → ℂ) :
    (pinchH hP H * fcalc hP (fun i => g (hP.eigenvalues i))).trace
      = (H * fcalc hP (fun i => g (hP.eigenvalues i))).trace := by
  rw [fcalc_comp, Matrix.mul_sum, Matrix.mul_sum, Matrix.trace_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Matrix.mul_smul, Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_smul, pinchH_mul_sproj hP H hp,
    Matrix.trace_mul_comm (sproj hP p * H), ← Matrix.mul_assoc, sproj_mul_self, Matrix.trace_mul_comm]

lemma trace_pinchH (H : Matrix (Fin M) (Fin M) ℂ) : (pinchH hP H).trace = H.trace := by
  have h := trace_pinchH_mul_fcalc hP H (fun _ => 1)
  rwa [fcalc_const, one_smul, Matrix.mul_one, Matrix.mul_one] at h

/-- For `τ ∉ spec P`, `(P - τ)⁻¹ H_d = Σ_p (p - τ)⁻¹ Q_p H Q_p` is Hermitian. -/
theorem isHermitian_inv_mul_pinchH {H : Matrix (Fin M) (Fin M) ℂ} (hH : H.IsHermitian) {τ : ℝ}
    (hτ : τ ∉ spec hP) :
    ((P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ))⁻¹ * pinchH hP H).IsHermitian := by
  rw [inv_sub_eq_fcalc hP hτ, fcalc_comp hP (fun x => ((x - τ : ℝ) : ℂ)⁻¹), Finset.sum_mul]
  have e : ∀ p ∈ spec hP, (((p - τ : ℝ) : ℂ)⁻¹ • sproj hP p) * pinchH hP H
      = (((p - τ)⁻¹ : ℝ) : ℂ) • (sproj hP p * H * sproj hP p) := by
    intro p hp
    rw [Matrix.smul_mul, sproj_mul_pinchH hP H hp]
    push_cast
    rfl
  rw [Finset.sum_congr rfl e]
  refine isHermitian_finset_sum _ _ fun p _ => ?_
  refine IsHermitian.smul ?_ (OQP27.StripL3b.isSelfAdjoint_ofReal _)
  unfold IsHermitian
  rw [conjTranspose_mul, conjTranspose_mul, (isHermitian_sproj hP p).eq, hH.eq, Matrix.mul_assoc]

/-- The pencil `(P - τ)⁻¹ H` and its pinched version have the same trace. -/
theorem trace_inv_mul_pinchH (H : Matrix (Fin M) (Fin M) ℂ) {τ : ℝ} (hτ : τ ∉ spec hP) :
    ((P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ))⁻¹ * pinchH hP H).trace
      = ((P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ))⁻¹ * H).trace := by
  rw [Matrix.trace_mul_comm, Matrix.trace_mul_comm _ H, inv_sub_eq_fcalc hP hτ]
  exact trace_pinchH_mul_fcalc hP H (fun x => ((x - τ : ℝ) : ℂ)⁻¹)

end Spec

end HarmonicMajorization
