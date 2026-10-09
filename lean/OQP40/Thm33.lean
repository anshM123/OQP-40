import OQP40.Statement
import OQP40.Thm33Reduction

/-!
# Theorem 1 of the lower-half note: `p_{3,3}(A,B) ≥ Tr((AB)^3)`

Authors: Ansh Mishra, Aryan Senthilkumar. License: MIT.

This file proves Theorem 1 of `math/04-lower-half-new-cases.md`: for positive semidefinite complex
matrices $A, B$ of any size,
$$3 \operatorname{Re}\operatorname{Tr}((AB)^3) \le \operatorname{Re}\operatorname{Tr}(A^3 B^3)
  + 2 \operatorname{Re}\operatorname{Tr}(A^2 B A B^2) \qquad (\texttt{three\_mul\_trace\_mul\_cube\_le}),$$
and its word-average form
$$\operatorname{Re}\operatorname{Tr}((AB)^3) \le \operatorname{Re} p_{3,3}(A,B)
  \qquad (\texttt{trace\_mul\_cube\_le\_wordAverage}),$$
where $p_{3,3}$ is `wordAverage 3 3` of `OQP40/Statement.lean`. For Hermitian $A, B$ the word
average, $\operatorname{Tr}(A^3B^3)$ and $\operatorname{Tr}((AB)^3)$ are real, while
$\operatorname{Tr}(A^2BAB^2)$ need not be; the statements compare real parts.
The classical last step of the note ($\operatorname{Tr}((AB)^3) \ge \operatorname{Tr}\exp(3\log A +
3\log B)$, by the Araki-Lieb-Thirring inequality) is not formalized here.

## Proof
- **The eigenbasis** (`three_mul_trace_mul_cube_le`): write $A = U D U^*$ with $D$ the diagonal
  matrix of the eigenvalues $\alpha_i \ge 0$ (`Matrix.IsHermitian.spectral_theorem`) and
  $b = U^* B U \ge 0$. The three traces do not change.
- **Coordinates** (`trace_diag_mul_cube`, `trace_diag_cube_mul_cube`, `trace_diag_sq_mul`): with
  $T(i,j,k) = b_{ij} b_{jk} b_{ki}$, the traces are $\sum T(i,j,k)$ times $\alpha_i\alpha_j\alpha_k$,
  $\alpha_i^3$ and $\alpha_i^2\alpha_j$.
- **Symmetrization** (`sum_kappa_eq`): $\operatorname{Re} T$ is invariant under all permutations
  of $(i,j,k)$, so the difference of the two sides is one third of
  $\sum_{i,j,k} \operatorname{Re} T(i,j,k)\, \kappa(\alpha_i,\alpha_j,\alpha_k)$, which is
  nonnegative by `kernel_sum_nonneg` (`OQP40/Thm33Reduction.lean`).
- **Words** (`wordAverage_three_three`): the 20 words with three letters $A$ and three letters
  $B$ fall into the rotation classes of $A^3B^3$, $A^2BAB^2$, $A^2B^2AB$ and $(AB)^3$, of sizes 6,
  6, 6 and 2, so $20\,p_{3,3} = 6\operatorname{Tr}(A^3B^3) + 6\operatorname{Tr}(A^2BAB^2)
  + 6\operatorname{Tr}(A^2B^2AB) + 2\operatorname{Tr}((AB)^3)$ for all square matrices. For
  Hermitian $A, B$ the middle two traces are complex conjugates.

## Main results
- `OpenQuantumProblem40.three_mul_trace_mul_cube_le`: (core) for positive semidefinite `A, B`
  indexed by any finite type.
- `OpenQuantumProblem40.trace_mul_cube_le_wordAverage`: (main) for positive semidefinite `A, B`.
- `OpenQuantumProblem40.wordAverage_three_three`: the word identity, for all `A, B`.
-/

namespace OpenQuantumProblem40

open Matrix Finset
open scoped ComplexOrder

namespace Thm33

/-! ### The traces in the eigenbasis of the first matrix -/

section Traces

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem trace_diag_mul_cube (α : n → ℝ) (b : Matrix n n ℂ) :
    ((diagonal (fun i => (α i : ℂ)) * b) ^ 3).trace
      = ∑ i, ∑ j, ∑ k, ((α i * α j * α k : ℝ) : ℂ) * (b i j * b j k * b k i) := by
  have hMe : ∀ i j, (diagonal (fun i => (α i : ℂ)) * b) i j = (α i : ℂ) * b i j :=
    fun i j => Matrix.diagonal_mul _ _ _ _
  generalize diagonal (fun i => (α i : ℂ)) * b = M at hMe ⊢
  rw [pow_three]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.mul_sum, hMe]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => ?_
  push_cast
  ring

theorem trace_diag_cube_mul_cube (α : n → ℝ) (b : Matrix n n ℂ) :
    ((diagonal (fun i => (α i : ℂ))) ^ 3 * b ^ 3).trace
      = ∑ i, ∑ j, ∑ k, ((α i ^ 3 : ℝ) : ℂ) * (b i j * b j k * b k i) := by
  rw [Matrix.diagonal_pow, pow_three b]
  simp only [Matrix.trace, Matrix.diag]
  simp only [Matrix.diagonal_mul]
  simp only [Matrix.mul_apply, Finset.mul_sum, Pi.pow_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => ?_
  push_cast
  ring

theorem trace_diag_sq_mul (α : n → ℝ) (b : Matrix n n ℂ) :
    ((diagonal (fun i => (α i : ℂ))) ^ 2 * b * diagonal (fun i => (α i : ℂ)) * b ^ 2).trace
      = ∑ i, ∑ j, ∑ k, ((α i ^ 2 * α j : ℝ) : ℂ) * (b i j * b j k * b k i) := by
  have hNe : ∀ i k,
      ((diagonal (fun i => (α i : ℂ))) ^ 2 * b * diagonal (fun i => (α i : ℂ))) i k
        = (α i : ℂ) ^ 2 * b i k * (α k : ℂ) := by
    intro i k
    rw [Matrix.mul_diagonal, Matrix.diagonal_pow, Matrix.diagonal_mul, Pi.pow_apply]
  generalize (diagonal (fun i => (α i : ℂ))) ^ 2 * b * diagonal (fun i => (α i : ℂ)) = N
    at hNe ⊢
  rw [pow_two b]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.mul_sum, hNe]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => ?_
  push_cast
  ring

end Traces

/-! ### Symmetrization -/

/-- If `t` is invariant under rotation and reversal of its arguments, then
$\sum t(i,j,k)\,\kappa(\alpha_i,\alpha_j,\alpha_k)
= 3 \sum t(i,j,k)\,(\alpha_i^3 + 2\alpha_i^2\alpha_j - 3\alpha_i\alpha_j\alpha_k)$. -/
theorem sum_kappa_eq {ι : Type*} [Fintype ι] (t : ι → ι → ι → ℝ)
    (hcyc : ∀ i j k, t i j k = t j k i) (hrev : ∀ i j k, t i k j = t i j k) (α : ι → ℝ) :
    ∑ i, ∑ j, ∑ k, t i j k * kappa (α i) (α j) (α k)
      = 3 * ∑ i, ∑ j, ∑ k, t i j k * (α i ^ 3 + 2 * α i ^ 2 * α j - 3 * α i * α j * α k) := by
  let p : ℝ → ℝ → ℝ → ℝ := fun x y z => x ^ 3 + x ^ 2 * y + x ^ 2 * z - 3 * x * y * z
  have e1 : ∑ i, ∑ j, ∑ k, t i j k * kappa (α i) (α j) (α k)
      = ∑ i, ∑ j, ∑ k, t i j k * p (α i) (α j) (α k)
        + ∑ i, ∑ j, ∑ k, t i j k * p (α j) (α k) (α i)
        + ∑ i, ∑ j, ∑ k, t i j k * p (α k) (α i) (α j) := by
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => ?_
    simp only [p, kappa]
    ring
  have e2 : ∑ i, ∑ j, ∑ k, t i j k * p (α j) (α k) (α i)
      = ∑ i, ∑ j, ∑ k, t i j k * p (α i) (α j) (α k) := by
    rw [← sum_rotate (fun a b c => t a b c * p (α a) (α b) (α c))]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => ?_
    rw [hcyc i j k]
  have e3 : ∑ i, ∑ j, ∑ k, t i j k * p (α k) (α i) (α j)
      = ∑ i, ∑ j, ∑ k, t i j k * p (α i) (α j) (α k) := by
    rw [sum_rotate (fun a b c => t c a b * p (α c) (α a) (α b))]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => ?_
    rw [hcyc i j k, hcyc j k i]
  have e4 : ∑ i, ∑ j, ∑ k, t i j k * (α i ^ 2 * α k)
      = ∑ i, ∑ j, ∑ k, t i j k * (α i ^ 2 * α j) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [hrev i j k]
  have e5 : ∑ i, ∑ j, ∑ k, t i j k * p (α i) (α j) (α k)
      = ∑ i, ∑ j, ∑ k, t i j k * (α i ^ 3 + 2 * α i ^ 2 * α j - 3 * α i * α j * α k)
        + (∑ i, ∑ j, ∑ k, t i j k * (α i ^ 2 * α k)
          - ∑ i, ∑ j, ∑ k, t i j k * (α i ^ 2 * α j)) := by
    simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => ?_
    simp only [p]
    ring
  rw [e1, e2, e3, e5, e4]
  ring

/-- **Theorem 1 in the eigenbasis of the first matrix**: for `α i ≥ 0` and `b` positive
semidefinite, with `D = diagonal α`,
$3\operatorname{Re}\operatorname{Tr}((Db)^3) \le \operatorname{Re}\operatorname{Tr}(D^3 b^3)
+ 2\operatorname{Re}\operatorname{Tr}(D^2 b D b^2)$. -/
theorem core_diag {n : Type*} [Fintype n] [DecidableEq n] (α : n → ℝ) (hα : ∀ i, 0 ≤ α i)
    {b : Matrix n n ℂ} (hb : b.PosSemidef) :
    3 * ((diagonal (fun i => (α i : ℂ)) * b) ^ 3).trace.re
      ≤ ((diagonal (fun i => (α i : ℂ))) ^ 3 * b ^ 3).trace.re
        + 2 * ((diagonal (fun i => (α i : ℂ))) ^ 2 * b * diagonal (fun i => (α i : ℂ))
          * b ^ 2).trace.re := by
  rw [trace_diag_mul_cube, trace_diag_cube_mul_cube, trace_diag_sq_mul]
  simp only [Complex.re_sum, Complex.re_ofReal_mul]
  have hcyc : ∀ i j k, (fun i j k => (b i j * b j k * b k i).re) i j k
      = (fun i j k => (b i j * b j k * b k i).re) j k i := by
    intro i j k
    simp only
    rw [show b i j * b j k * b k i = b j k * b k i * b i j by ring]
  have hrev : ∀ i j k, (fun i j k => (b i j * b j k * b k i).re) i k j
      = (fun i j k => (b i j * b j k * b k i).re) i j k := by
    intro i j k
    simp only
    rw [← hb.isHermitian.apply i k, ← hb.isHermitian.apply k j, ← hb.isHermitian.apply j i]
    have : star (b k i) * star (b j k) * star (b i j) = star (b i j * b j k * b k i) := by
      simp only [star_mul']
      ring
    rw [this, Complex.star_def, Complex.conj_re]
  have h := kernel_sum_nonneg hb α hα
  rw [sum_kappa_eq (fun i j k => (b i j * b j k * b k i).re) hcyc hrev α] at h
  have key : ∑ i, ∑ j, ∑ k, (b i j * b j k * b k i).re
        * (α i ^ 3 + 2 * α i ^ 2 * α j - 3 * α i * α j * α k)
      = ∑ i, ∑ j, ∑ k, α i ^ 3 * (b i j * b j k * b k i).re
        + 2 * ∑ i, ∑ j, ∑ k, α i ^ 2 * α j * (b i j * b j k * b k i).re
        - 3 * ∑ i, ∑ j, ∑ k, α i * α j * α k * (b i j * b j k * b k i).re := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [key] at h
  linarith

end Thm33

open Thm33

/-! ### Theorem 1 -/

/-- **Theorem 1 of the lower-half note (core form).** For positive semidefinite complex matrices
`A, B` indexed by any finite type,
$$3\operatorname{Re}\operatorname{Tr}((AB)^3) \le \operatorname{Re}\operatorname{Tr}(A^3B^3)
  + 2\operatorname{Re}\operatorname{Tr}(A^2BAB^2).$$ -/
theorem three_mul_trace_mul_cube_le {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    3 * ((A * B) ^ 3).trace.re
      ≤ (A ^ 3 * B ^ 3).trace.re + 2 * (A ^ 2 * B * A * B ^ 2).trace.re := by
  set U := hA.isHermitian.eigenvectorUnitary with hU
  set φ := Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) U with hφ
  set α := hA.isHermitian.eigenvalues with hα
  have hAD : A = φ (diagonal (fun i => (α i : ℂ))) := hA.isHermitian.spectral_theorem
  set b := φ.symm B with hbdef
  have hBb : B = φ b := (φ.apply_symm_apply B).symm
  have hb : b.PosSemidef := by
    have h := hB.conjTranspose_mul_mul_same (U : Matrix n n ℂ)
    rw [hbdef, hφ, Unitary.conjStarAlgAut_symm_apply, Matrix.star_eq_conjTranspose]
    exact h
  have htr : ∀ M : Matrix n n ℂ, (φ M).trace = M.trace := by
    intro M
    rw [hφ, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle, Unitary.coe_star_mul_self,
      Matrix.one_mul]
  have e1 : (A * B) ^ 3 = φ ((diagonal (fun i => (α i : ℂ)) * b) ^ 3) := by
    rw [map_pow, map_mul, ← hAD, ← hBb]
  have e2 : A ^ 3 * B ^ 3 = φ ((diagonal (fun i => (α i : ℂ))) ^ 3 * b ^ 3) := by
    rw [map_mul, map_pow, map_pow, ← hAD, ← hBb]
  have e3 : A ^ 2 * B * A * B ^ 2
      = φ ((diagonal (fun i => (α i : ℂ))) ^ 2 * b * diagonal (fun i => (α i : ℂ)) * b ^ 2) := by
    rw [map_mul, map_mul, map_mul, map_pow, map_pow, ← hAD, ← hBb]
  rw [e1, e2, e3, htr, htr, htr]
  exact core_diag α (fun i => hA.eigenvalues_nonneg i) hb

/-- **The word identity**: for all square matrices `A, B`,
$20\,p_{3,3}(A,B) = 6\operatorname{Tr}(A^3B^3) + 6\operatorname{Tr}(A^2BAB^2)
+ 6\operatorname{Tr}(A^2B^2AB) + 2\operatorname{Tr}((AB)^3)$. -/
theorem wordAverage_three_three {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℂ) :
    20 * wordAverage 3 3 A B = 6 * (A ^ 3 * B ^ 3).trace + 6 * (A ^ 2 * B * A * B ^ 2).trace
      + 6 * (A ^ 2 * B ^ 2 * A * B).trace + 2 * ((A * B) ^ 3).trace := by
  rw [wordAverage_eq, show Nat.choose (3 + 3) 3 = 20 by decide,
    wordSum_succ_succ A B 5 2, wordSum_succ_succ A B 4 1, wordSum_succ_succ A B 4 2,
    wordSum_succ_succ A B 3 0, wordSum_succ_succ A B 3 1, wordSum_succ_succ A B 3 2,
    wordSum_succ_succ A B 2 0, wordSum_succ_succ A B 2 1, wordSum_succ_succ A B 1 0,
    wordSum_zero_right A B 3, wordSum_zero_right A B 2, wordSum_zero_right A B 1,
    wordSum_self A B 3, wordSum_self A B 2, wordSum_self A B 1]
  simp only [Matrix.mul_add, Matrix.trace_add, pow_succ, pow_zero, Matrix.one_mul, Matrix.mul_assoc]
  have w3 : (A * (A * (B * (B * (B * A))))).trace = (A * (A * (A * (B * (B * B))))).trace := by
    rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
  have w4 : (A * (B * (A * (A * (B * B))))).trace = (A * (A * (B * (B * (A * B))))).trace := by
    rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
  have w6 : (A * (B * (A * (B * (B * A))))).trace = (A * (A * (B * (A * (B * B))))).trace := by
    rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
  have w7 : (A * (B * (B * (A * (A * B))))).trace = (A * (A * (B * (A * (B * B))))).trace := by
    rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
  have w8 : (A * (B * (B * (A * (B * A))))).trace = (A * (A * (B * (B * (A * B))))).trace := by
    rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
  have w9 : (A * (B * (B * (B * (A * A))))).trace = (A * (A * (A * (B * (B * B))))).trace := by
    rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
  have w10 : (B * (A * (A * (A * (B * B))))).trace = (A * (A * (A * (B * (B * B))))).trace := by
    rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
  have w11 : (B * (A * (A * (B * (A * B))))).trace = (A * (A * (B * (A * (B * B))))).trace := by
    rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
  have w12 : (B * (A * (A * (B * (B * A))))).trace = (A * (A * (B * (B * (A * B))))).trace := by
    rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
  have w13 : (B * (A * (B * (A * (A * B))))).trace = (A * (A * (B * (B * (A * B))))).trace := by
    rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
  have w14 : (B * (A * (B * (A * (B * A))))).trace = (A * (B * (A * (B * (A * B))))).trace := by
    rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
  have w15 : (B * (A * (B * (B * (A * A))))).trace = (A * (A * (B * (A * (B * B))))).trace := by
    rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
  have w16 : (B * (B * (A * (A * (A * B))))).trace = (A * (A * (A * (B * (B * B))))).trace := by
    rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
  have w17 : (B * (B * (A * (A * (B * A))))).trace = (A * (A * (B * (A * (B * B))))).trace := by
    rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
  have w18 : (B * (B * (A * (B * (A * A))))).trace = (A * (A * (B * (B * (A * B))))).trace := by
    rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
  have w19 : (B * (B * (B * (A * (A * A))))).trace = (A * (A * (A * (B * (B * B))))).trace := by
    rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
  simp only [w3, w4, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19]
  push_cast
  ring

/-- For Hermitian `A, B`, $\operatorname{Tr}(A^2B^2AB)$ is the complex conjugate of
$\operatorname{Tr}(A^2BAB^2)$, so the two have the same real part. -/
theorem trace_sq_sq_mul_re {n : Type*} [Fintype n] [DecidableEq n] {A B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (A ^ 2 * B ^ 2 * A * B).trace.re = (A ^ 2 * B * A * B ^ 2).trace.re := by
  have h : (A ^ 2 * B * A * B ^ 2).trace = star (A ^ 2 * B ^ 2 * A * B).trace := by
    rw [← Matrix.trace_conjTranspose]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_pow, hA.eq, hB.eq, Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [h, Complex.star_def, Complex.conj_re]

/-- **Theorem 1 of the lower-half note (word-average form).** For positive semidefinite complex
matrices `A, B`, $\operatorname{Re}\operatorname{Tr}((AB)^3) \le \operatorname{Re} p_{3,3}(A,B)$,
where $p_{3,3}$ is `wordAverage 3 3`. -/
theorem trace_mul_cube_le_wordAverage {d : ℕ} {A B : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    ((A * B) ^ 3).trace.re ≤ (wordAverage 3 3 A B).re := by
  have h20 := congrArg Complex.re (wordAverage_three_three A B)
  simp only [Complex.add_re, Complex.mul_re] at h20
  norm_num at h20
  have hc := three_mul_trace_mul_cube_le hA hB
  have hs := trace_sq_sq_mul_re hA.isHermitian hB.isHermitian
  linarith

end OpenQuantumProblem40
