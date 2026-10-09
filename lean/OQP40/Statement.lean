import Mathlib

/-!
# Open Quantum Problem 40: the refined Bessis-Moussa-Villani conjecture

Authors: Ansh Mishra, Aryan Senthilkumar. License: MIT.

## Mathematical problem
Problem 40 of the IQOQI Vienna list (D. Hägele, communicated by R. F. Werner) refines the
Bessis-Moussa-Villani (BMV) conjecture. For positive semidefinite $d \times d$ matrices $A, B$ and
integers $n, m \ge 0$, let $p_{n,m}(A,B)$ be the average of $\operatorname{Tr} W$ over the
$\binom{n+m}{n}$ words $W$ with $n$ letters $A$ and $m$ letters $B$. Equivalently,
$\binom{n+m}{n} p_{n,m}(A,B)$ is the coefficient of $t^m$ in $\operatorname{Tr}(A + tB)^{n+m}$.
The problem asks whether, for all $n, m \ge 0$,
$$\operatorname{Tr}(A^n B^m) \ge p_{n,m}(A,B) \ge \operatorname{Tr}\exp(n \log A + m \log B).$$
The logarithm needs $A, B$ positive definite. As suggested in Formal Conjectures issue #3457, the
chain is stated for positive definite matrices (`RefinedBMV`); the upper half is also stated for
positive semidefinite matrices (`UpperHalf`).

## What this file formalizes
All definitions are written from scratch with Mathlib:
- `word A B S`: the ordered product with the letter $A$ at the positions in `S` and $B$ elsewhere;
- `wordAverage n m A B`: $p_{n,m}(A,B)$, the average of the traces of the words given by the
  position sets `S` with $n$ elements;
- `spectralProj`, `pinching`: the spectral projections $Q_\mu$ of a Hermitian matrix $A$ and the
  pinching $E_A(B) = \sum_\mu Q_\mu B Q_\mu$ of $B$ onto the eigenspaces of $A$;
- `RefinedBMV`: the chain of the problem, for positive definite $A, B$ and all $n, m$;
- `UpperHalf`, `LowerHalf`: its two halves;
- `PinchingInequality`: the inequality $p_{n,m}(A,B) \ge \operatorname{Tr}(A^n E_A(B)^m)$ for
  positive semidefinite $A, B$ and all $n, m$ (T. H. Dinh, Conjecture 5.1).

The traces in the problem are real for Hermitian $A, B$; they are compared through their real parts.

This is the standalone version of the file written for Formal Conjectures. It imports only Mathlib,
and the answer is stated as `False ↔ RefinedBMV` in place of `answer(False) ↔ RefinedBMV`.

### Main results
- `refinedBMV`: the answer to the problem is negative. The Cha-Lee pair $A_x, B_x$ at
  $x = 1/1000$ and $n = m = 5$ gives $\operatorname{Tr}(A_x^5 B_x^5) < p_{5,5}(A_x, B_x)$
  (`chaLee_counterexample`, with the exact values `chaLee_trace` and `chaLee_wordAverage`), so the
  upper half fails for positive semidefinite matrices (`not_upperHalf`). The same holds for the
  positive definite pair $A_x + 10^{-4}, B_x + 10^{-4}$ (`chaLee_perturbed_counterexample`), so the
  chain fails for positive definite matrices (`not_refinedBMV`).
- `LowerHalf` is open. It is stated here as a `Prop` and not proved.
- `PinchingInequality` is proved for all $n, m$ in `OQP40/Pinching.lean`.

All values are computed in exact arithmetic by Lean: the words are summed with Pascal's recursion
`wordSum_succ_succ` on integer matrices (the pairs scaled by $10^3$ and $10^4$; both sides of the
inequality are homogeneous of degree $n + m$).

### Checks of the definitions
- `card_words`: there are $\binom{n+m}{n}$ words with $n$ letters $A$ and $m$ letters $B$;
- `wordSum_succ_succ`, `wordSum_succ_zero`, `wordSum_zero_zero`: Pascal's recursion for the sums of
  words, by the first letter;
- `wordAverage_of_commute`: if $AB = BA$ then $p_{n,m}(A,B) = \operatorname{Tr}(A^n B^m)$;
- `wordAverage_one_one`: $p_{1,1}(A,B) = \operatorname{Tr}(AB)$;
- `wordAverage_zero_left`, `wordAverage_zero_right`: $p_{0,m} = \operatorname{Tr} B^m$ and
  $p_{n,0} = \operatorname{Tr} A^n$;
- `wordAverage_im`, `trace_pow_mul_pow_im`, `trace_exp_log_im`: the three quantities of the chain
  are real for Hermitian $A, B$, so comparing their real parts loses nothing;
- `chaLeeA_posSemidef`, `chaLeeB_posSemidef`, `chaLeeA_add_posDef`, `chaLeeB_add_posDef`: the
  Cha-Lee matrices are positive semidefinite, and positive definite after adding $\varepsilon > 0$;
- `chaLee_trace`, `chaLee_wordAverage`: the closed forms of Cha and Lee at $x = 1/1000$,
  $\operatorname{Tr}(A_x^5 B_x^5) = 32x^5 + 256x^{10}$ and
  $p_{5,5}(A_x,B_x) = \frac{x^4}{126}(5 + 1422x + 1675x^2 + 3130x^3 + 4875x^4 + 5930x^5 + 4881x^6)$.

## References
- IQOQI Vienna Open Quantum Problems, problem 40, *Refinement of the Bessis-Moussa-Villani
  conjecture*.
- Formal Conjectures issue #3457:
  https://github.com/google-deepmind/formal-conjectures/issues/3457
- H. Cha and J. Lee, arXiv:2603.19927 (2026): the counterexample to the upper half.
- T. H. Dinh, arXiv:2605.17782 (2026), Conjecture 5.1: the pinching inequality.
- H. R. Stahl, *Proof of the BMV conjecture*, Acta Math. 211 (2013) 255-290.
- E. H. Lieb and R. Seiringer, *Equivalent forms of the Bessis-Moussa-Villani conjecture*,
  J. Stat. Phys. 115 (2004) 185-190.
-/


noncomputable section

namespace OpenQuantumProblem40

open Matrix
open scoped ComplexOrder

/- ## Part 0: the problem -/

section Definitions

variable {d : ℕ}

/-- The word of length `N` with the letter `A` at the positions in `S` and the letter `B` at the
other positions: the ordered product $W_0 W_1 \cdots W_{N-1}$ with $W_i = A$ for $i \in S$ and
$W_i = B$ for $i \notin S$. -/
def word (A B : Matrix (Fin d) (Fin d) ℂ) {N : ℕ} (S : Finset (Fin N)) :
    Matrix (Fin d) (Fin d) ℂ :=
  (List.ofFn fun i => if i ∈ S then A else B).prod

/-- **The word average** $p_{n,m}(A,B)$: the average of $\operatorname{Tr} W$ over the
$\binom{n+m}{n}$ words $W$ of length $n + m$ with $n$ letters $A$ and $m$ letters $B$. A word is
given by the set `S` of the positions of its letters $A$. -/
def wordAverage (n m : ℕ) (A B : Matrix (Fin d) (Fin d) ℂ) : ℂ :=
  ((n + m).choose n : ℂ)⁻¹ *
    ∑ S ∈ (Finset.univ : Finset (Fin (n + m))).powersetCard n, (word A B S).trace

/-- The spectral projection $Q_\mu$ of a Hermitian matrix `A` for $\mu \in \mathbb{R}$: in the
orthonormal eigenbasis of `A` given by Mathlib, the orthogonal projection onto the span of the
eigenvectors with eigenvalue $\mu$ (zero if $\mu$ is not an eigenvalue). -/
def spectralProj {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) (μ : ℝ) :
    Matrix (Fin d) (Fin d) ℂ :=
  (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)
    * diagonal (fun i => if hA.eigenvalues i = μ then 1 else 0)
    * star (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)

/-- **The pinching** $E_A(B) = \sum_\mu Q_\mu B Q_\mu$ of `B` onto the eigenspaces of the
Hermitian matrix `A`; the sum runs over the distinct eigenvalues $\mu$ of `A`. -/
def pinching {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) (B : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  ∑ μ ∈ Finset.univ.image hA.eigenvalues, spectralProj hA μ * B * spectralProj hA μ

end Definitions

/-- **Open Quantum Problem 40** (refined BMV conjecture), in the form of Formal Conjectures issue
#3457: for all positive definite $A, B$ and all $n, m \ge 0$,
$$\operatorname{Tr}\exp(n \log A + m \log B) \le p_{n,m}(A,B) \le \operatorname{Tr}(A^n B^m).$$
The logarithm is the continuous functional calculus `cfc Real.log`. -/
def RefinedBMV : Prop :=
  ∀ (d : ℕ) (A B : Matrix (Fin d) (Fin d) ℂ), A.PosDef → B.PosDef → ∀ n m : ℕ,
    (NormedSpace.exp (n • cfc Real.log A + m • cfc Real.log B)).trace.re
        ≤ (wordAverage n m A B).re ∧
      (wordAverage n m A B).re ≤ (A ^ n * B ^ m).trace.re

/-- **The upper half** of OQP 40, for positive semidefinite $A, B$:
$p_{n,m}(A,B) \le \operatorname{Tr}(A^n B^m)$ for all $n, m \ge 0$. It is false
(`not_upperHalf`). -/
def UpperHalf : Prop :=
  ∀ (d : ℕ) (A B : Matrix (Fin d) (Fin d) ℂ), A.PosSemidef → B.PosSemidef → ∀ n m : ℕ,
    (wordAverage n m A B).re ≤ (A ^ n * B ^ m).trace.re

/-- **The lower half** of OQP 40, for positive definite $A, B$:
$\operatorname{Tr}\exp(n \log A + m \log B) \le p_{n,m}(A,B)$ for all $n, m \ge 0$. It is open.
It implies $p_{n,m}(A,B) > 0$, which is the Lieb-Seiringer form of the BMV conjecture (Stahl's
theorem). -/
def LowerHalf : Prop :=
  ∀ (d : ℕ) (A B : Matrix (Fin d) (Fin d) ℂ), A.PosDef → B.PosDef → ∀ n m : ℕ,
    (NormedSpace.exp (n • cfc Real.log A + m • cfc Real.log B)).trace.re
      ≤ (wordAverage n m A B).re

/-- **The pinching inequality** (T. H. Dinh, Conjecture 5.1): for positive semidefinite $A, B$ and
all $n, m \ge 0$, $\operatorname{Tr}(A^n E_A(B)^m) \le p_{n,m}(A,B)$, where $E_A(B)$ is the
pinching of $B$ onto the eigenspaces of $A$. It is proved in `OQP40/Pinching.lean`. -/
def PinchingInequality : Prop :=
  ∀ (d : ℕ) (A B : Matrix (Fin d) (Fin d) ℂ) (hA : A.PosSemidef), B.PosSemidef → ∀ n m : ℕ,
    (A ^ n * pinching hA.isHermitian B ^ m).trace.re ≤ (wordAverage n m A B).re

/-- The Cha-Lee matrix
$A_x = \begin{pmatrix} 1 & 0 & 0 \\ 0 & x & -x \\ 0 & -x & x \end{pmatrix}$. -/
def chaLeeA (x : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1, 0, 0; 0, (x : ℂ), -(x : ℂ); 0, -(x : ℂ), (x : ℂ)]

/-- The Cha-Lee matrix
$B_x = \begin{pmatrix} x & -x & 0 \\ -x & x & 0 \\ 0 & 0 & 1 \end{pmatrix}$. -/
def chaLeeB (x : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![(x : ℂ), -(x : ℂ), 0; -(x : ℂ), (x : ℂ), 0; 0, 0, 1]

/- ## Part 1: sums of words -/

section Words

variable {d : ℕ}

/-- The sum of the words of length `N` with `k` letters `A` and `N - k` letters `B`. -/
def wordSum (A B : Matrix (Fin d) (Fin d) ℂ) (N k : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard k, word A B S

/-- $p_{n,m}(A,B) = \binom{n+m}{n}^{-1} \operatorname{Tr} \sum_W W$. -/
theorem wordAverage_eq (n m : ℕ) (A B : Matrix (Fin d) (Fin d) ℂ) :
    wordAverage n m A B = ((n + m).choose n : ℂ)⁻¹ * (wordSum A B (n + m) n).trace := by
  rw [wordAverage, wordSum, trace_sum]

/-- There are $\binom{n+m}{n}$ words with $n$ letters $A$ and $m$ letters $B$. -/
theorem card_words (n m : ℕ) :
    ((Finset.univ : Finset (Fin (n + m))).powersetCard n).card = (n + m).choose n := by
  simp

/-- Prepending the letter `B`. -/
theorem word_map_succ (A B : Matrix (Fin d) (Fin d) ℂ) {N : ℕ} (S : Finset (Fin N)) :
    word A B (S.map (Fin.succEmb N)) = B * word A B S := by
  simp only [word, List.ofFn_succ, List.prod_cons]
  congr 1
  · simp [Fin.succ_ne_zero]
  · simp

/-- Prepending the letter `A`. -/
theorem word_insert_zero (A B : Matrix (Fin d) (Fin d) ℂ) {N : ℕ} (S : Finset (Fin N)) :
    word A B (insert 0 (S.map (Fin.succEmb N))) = A * word A B S := by
  simp only [word, List.ofFn_succ, List.prod_cons]
  congr 1
  · simp
  · simp [Fin.succ_ne_zero]

/-- The positions of a word of length `N + 1`: `0` and the successors of the positions of a word
of length `N`. -/
theorem univ_fin_succ (N : ℕ) : (Finset.univ : Finset (Fin (N + 1)))
    = insert 0 ((Finset.univ : Finset (Fin N)).map (Fin.succEmb N)) := by
  ext i
  refine ⟨fun _ => ?_, fun _ => Finset.mem_univ _⟩
  cases i using Fin.cases with
  | zero => simp
  | succ j => simp

/-- **Pascal's recursion** for the sums of words, by the first letter:
$\Sigma_{N+1,k+1} = A \Sigma_{N,k} + B \Sigma_{N,k+1}$. -/
theorem wordSum_succ_succ (A B : Matrix (Fin d) (Fin d) ℂ) (N k : ℕ) :
    wordSum A B (N + 1) (k + 1) = A * wordSum A B N k + B * wordSum A B N (k + 1) := by
  classical
  have h0 : (0 : Fin (N + 1)) ∉ (Finset.univ : Finset (Fin N)).map (Fin.succEmb N) := by
    simp [Fin.succ_ne_zero]
  unfold wordSum
  rw [univ_fin_succ, Finset.powersetCard_succ_insert h0, Finset.sum_union, Finset.sum_image,
    Finset.powersetCard_map, Finset.powersetCard_map, Finset.sum_map, Finset.sum_map, add_comm,
    Finset.mul_sum, Finset.mul_sum]
  · congr 1
    · exact Finset.sum_congr rfl fun S _ => word_insert_zero A B S
    · exact Finset.sum_congr rfl fun S _ => word_map_succ A B S
  · exact Finset.insert_erase_invOn.2.injOn.mono fun t ht =>
      Finset.notMem_mono (Finset.mem_powersetCard.1 ht).1 h0
  · refine Finset.disjoint_left.2 fun T hT1 hT2 => ?_
    obtain ⟨U, -, rfl⟩ := Finset.mem_image.1 hT2
    exact h0 ((Finset.mem_powersetCard.1 hT1).1 (Finset.mem_insert_self _ _))

/-- Pascal's recursion, words without the letter `A`: $\Sigma_{N+1,0} = B \Sigma_{N,0}$. -/
theorem wordSum_succ_zero (A B : Matrix (Fin d) (Fin d) ℂ) (N : ℕ) :
    wordSum A B (N + 1) 0 = B * wordSum A B N 0 := by
  simp only [wordSum, Finset.powersetCard_zero, Finset.sum_singleton]
  simpa using word_map_succ A B (∅ : Finset (Fin N))

/-- The empty word. -/
theorem wordSum_zero_zero (A B : Matrix (Fin d) (Fin d) ℂ) : wordSum A B 0 0 = 1 := by
  simp [wordSum, word]

/-- There is no word of length `N` with more than `N` letters `A`. -/
theorem wordSum_eq_zero_of_lt (A B : Matrix (Fin d) (Fin d) ℂ) {N k : ℕ} (h : N < k) :
    wordSum A B N k = 0 := by
  unfold wordSum
  rw [Finset.powersetCard_eq_empty.2 (by simpa using h), Finset.sum_empty]

/-- The only word without the letter `A` is $B^N$. -/
theorem wordSum_zero_right (A B : Matrix (Fin d) (Fin d) ℂ) (N : ℕ) :
    wordSum A B N 0 = B ^ N := by
  induction N with
  | zero => rw [wordSum_zero_zero, pow_zero]
  | succ N ih => rw [wordSum_succ_zero, ih, pow_succ']

/-- The only word without the letter `B` is $A^N$. -/
theorem wordSum_self (A B : Matrix (Fin d) (Fin d) ℂ) (N : ℕ) : wordSum A B N N = A ^ N := by
  induction N with
  | zero => rw [wordSum_zero_zero, pow_zero]
  | succ N ih =>
    rw [wordSum_succ_succ, ih, wordSum_eq_zero_of_lt A B (Nat.lt_succ_self N), Matrix.mul_zero,
      add_zero, pow_succ']

/-- For commuting letters all words with `k` letters `A` are equal to $A^k B^{N-k}$. -/
theorem wordSum_of_commute {A B : Matrix (Fin d) (Fin d) ℂ} (h : Commute A B) (N k : ℕ) :
    wordSum A B N k = (N.choose k : ℂ) • (A ^ k * B ^ (N - k)) := by
  induction N generalizing k with
  | zero =>
    cases k with
    | zero => simp [wordSum_zero_zero]
    | succ k => simp [wordSum_eq_zero_of_lt A B (Nat.succ_pos k)]
  | succ N ih =>
    cases k with
    | zero => simp [wordSum_zero_right, pow_succ']
    | succ k =>
      rw [wordSum_succ_succ, ih, ih, Nat.choose_succ_succ', Nat.cast_add, add_smul]
      congr 1
      · rw [Matrix.mul_smul, ← Matrix.mul_assoc, ← pow_succ', Nat.add_sub_add_right]
      · rcases Nat.lt_or_ge N (k + 1) with hlt | hle
        · rw [Nat.choose_eq_zero_of_lt hlt]
          simp
        · rw [Matrix.mul_smul, ← Matrix.mul_assoc, ((h.pow_left (k + 1)).symm).eq,
            Matrix.mul_assoc, ← pow_succ', Nat.add_sub_add_right,
            show N - (k + 1) + 1 = N - k by omega]

/-- **Commuting case**: if $AB = BA$ then $p_{n,m}(A,B) = \operatorname{Tr}(A^n B^m)$, so both
halves of the chain are equalities. -/
theorem wordAverage_of_commute {A B : Matrix (Fin d) (Fin d) ℂ} (h : Commute A B) (n m : ℕ) :
    wordAverage n m A B = (A ^ n * B ^ m).trace := by
  rw [wordAverage_eq, wordSum_of_commute h, trace_smul, Nat.add_sub_cancel_left, smul_eq_mul,
    ← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.2 (Nat.choose_pos (Nat.le_add_right n m)).ne'),
    one_mul]

/-- $p_{1,1}(A,B) = \frac12 \operatorname{Tr}(AB + BA) = \operatorname{Tr}(AB)$. -/
theorem wordAverage_one_one (A B : Matrix (Fin d) (Fin d) ℂ) :
    wordAverage 1 1 A B = (A * B).trace := by
  rw [wordAverage_eq, wordSum_succ_succ A B 1 0, wordSum_zero_right, wordSum_self, pow_one,
    pow_one, trace_add, trace_mul_comm B A]
  norm_num
  ring

/-- $p_{0,m}(A,B) = \operatorname{Tr} B^m$. -/
theorem wordAverage_zero_left (A B : Matrix (Fin d) (Fin d) ℂ) (m : ℕ) :
    wordAverage 0 m A B = (B ^ m).trace := by
  rw [wordAverage_eq, wordSum_zero_right, Nat.choose_zero_right, zero_add]
  simp

/-- $p_{n,0}(A,B) = \operatorname{Tr} A^n$. -/
theorem wordAverage_zero_right (A B : Matrix (Fin d) (Fin d) ℂ) (n : ℕ) :
    wordAverage n 0 A B = (A ^ n).trace := by
  rw [wordAverage_eq, add_zero, wordSum_self, Nat.choose_self]
  simp

/-- `(List.ofFn f).reverse = List.ofFn (f ∘ Fin.rev)`. -/
theorem ofFn_reverse {α : Type*} {N : ℕ} (f : Fin N → α) :
    (List.ofFn f).reverse = List.ofFn fun i => f (Fin.rev i) := by
  rw [List.ofFn_eq_map, List.ofFn_eq_map, ← List.map_reverse, List.finRange_reverse, List.map_map]
  rfl

/-- The adjoint of a word in Hermitian letters is the reversed word: its letters $A$ are at the
reflected positions $\{N - 1 - i : i \in S\}$. -/
theorem word_conjTranspose {A B : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) {N : ℕ} (S : Finset (Fin N)) :
    (word A B S)ᴴ = word A B (S.map Fin.revPerm.toEmbedding) := by
  rw [word, word, conjTranspose_list_prod, List.map_ofFn, ofFn_reverse]
  congr 2
  funext i
  have hmem : i ∈ S.map Fin.revPerm.toEmbedding ↔ Fin.rev i ∈ S := by
    simp [Finset.mem_map_equiv]
  simp only [Function.comp_apply, hmem]
  split_ifs
  · exact hA.eq
  · exact hB.eq

/-- Reflecting the positions permutes the words with `n` letters `A`. -/
theorem sum_powersetCard_map_rev {N n : ℕ} (F : Finset (Fin N) → ℂ) :
    ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard n, F (S.map Fin.revPerm.toEmbedding)
      = ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard n, F S := by
  calc ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard n, F (S.map Fin.revPerm.toEmbedding)
      = ∑ T ∈ ((Finset.univ : Finset (Fin N)).powersetCard n).map
          (Finset.mapEmbedding Fin.revPerm.toEmbedding).toEmbedding, F T := by
        rw [Finset.sum_map]
        rfl
    _ = ∑ T ∈ ((Finset.univ : Finset (Fin N)).map Fin.revPerm.toEmbedding).powersetCard n,
          F T := by
        rw [Finset.powersetCard_map]
    _ = ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard n, F S := by
        rw [Finset.map_univ_equiv]

/-- **Reality check**: for Hermitian $A, B$ the word average $p_{n,m}(A,B)$ is real. -/
theorem wordAverage_im {A B : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (n m : ℕ) : (wordAverage n m A B).im = 0 := by
  apply Complex.conj_eq_iff_im.1
  have h : star (∑ S ∈ (Finset.univ : Finset (Fin (n + m))).powersetCard n, (word A B S).trace)
      = ∑ S ∈ (Finset.univ : Finset (Fin (n + m))).powersetCard n, (word A B S).trace := by
    rw [star_sum]
    calc ∑ S ∈ (Finset.univ : Finset (Fin (n + m))).powersetCard n, star (word A B S).trace
        = ∑ S ∈ (Finset.univ : Finset (Fin (n + m))).powersetCard n,
            (word A B (S.map Fin.revPerm.toEmbedding)).trace := by
          refine Finset.sum_congr rfl fun S _ => ?_
          rw [← trace_conjTranspose, word_conjTranspose hA hB]
      _ = _ := sum_powersetCard_map_rev (fun S => (word A B S).trace)
  change star (wordAverage n m A B) = wordAverage n m A B
  rw [wordAverage, star_mul', h]
  congr 1
  simp

/-- **Reality check**: for Hermitian $A, B$ the trace $\operatorname{Tr}(A^n B^m)$ is real. -/
theorem trace_pow_mul_pow_im {A B : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (n m : ℕ) : (A ^ n * B ^ m).trace.im = 0 := by
  apply Complex.conj_eq_iff_im.1
  change star (A ^ n * B ^ m).trace = (A ^ n * B ^ m).trace
  rw [← trace_conjTranspose, conjTranspose_mul, conjTranspose_pow, conjTranspose_pow, hA.eq, hB.eq,
    trace_mul_comm]

/-- **Reality check**: $\operatorname{Tr}\exp(n \log A + m \log B)$ is real (the functional
calculus `cfc Real.log` gives Hermitian matrices). -/
theorem trace_exp_log_im (A B : Matrix (Fin d) (Fin d) ℂ) (n m : ℕ) :
    (NormedSpace.exp (n • cfc Real.log A + m • cfc Real.log B)).trace.im = 0 := by
  have hA' : (cfc Real.log A)ᴴ = cfc Real.log A := cfc_predicate Real.log A
  have hB' : (cfc Real.log B)ᴴ = cfc Real.log B := cfc_predicate Real.log B
  have hH : (n • cfc Real.log A + m • cfc Real.log B)ᴴ
      = n • cfc Real.log A + m • cfc Real.log B := by
    rw [conjTranspose_add, conjTranspose_nsmul, conjTranspose_nsmul, hA', hB']
  apply Complex.conj_eq_iff_im.1
  change star (NormedSpace.exp (n • cfc Real.log A + m • cfc Real.log B)).trace = _
  rw [← trace_conjTranspose, ← Matrix.exp_conjTranspose, hH]

/-- An ordered product of `N` scalar multiples. -/
theorem prod_ofFn_smul (c : ℂ) {N : ℕ} (f : Fin N → Matrix (Fin d) (Fin d) ℂ) :
    (List.ofFn fun i => c • f i).prod = c ^ N • (List.ofFn f).prod := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.ofFn_succ, List.prod_cons, List.ofFn_succ, List.prod_cons, ih (fun i => f i.succ),
      smul_mul_smul_comm, pow_succ']

/-- **Homogeneity**: $p_{n,m}(cA, cB) = c^{n+m} p_{n,m}(A,B)$. -/
theorem wordAverage_smul (c : ℂ) (n m : ℕ) (A B : Matrix (Fin d) (Fin d) ℂ) :
    wordAverage n m (c • A) (c • B) = c ^ (n + m) * wordAverage n m A B := by
  have hw : ∀ S : Finset (Fin (n + m)), word (c • A) (c • B) S = c ^ (n + m) • word A B S := by
    intro S
    have e : (fun i => if i ∈ S then c • A else c • B) = fun i => c • (if i ∈ S then A else B) := by
      funext i
      split_ifs <;> rfl
    rw [word, word, e, prod_ofFn_smul]
  simp only [wordAverage, hw, trace_smul, smul_eq_mul, ← Finset.mul_sum]
  ring

end Words

/- ## Part 2: the Cha-Lee counterexample -/

section ChaLee

/-- $A_x = e_1 e_1^* + x (e_2 - e_3)(e_2 - e_3)^*$ is positive semidefinite for $x \ge 0$. -/
theorem chaLeeA_posSemidef {x : ℝ} (hx : 0 ≤ x) : (chaLeeA x).PosSemidef := by
  have e : chaLeeA x = vecMulVec ![(1 : ℂ), 0, 0] (star ![(1 : ℂ), 0, 0])
      + (x : ℂ) • vecMulVec ![(0 : ℂ), 1, -1] (star ![(0 : ℂ), 1, -1]) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [chaLeeA, vecMulVec]
  rw [e]
  exact (posSemidef_vecMulVec_self_star _).add
    ((posSemidef_vecMulVec_self_star _).smul (Complex.zero_le_real.2 hx))

/-- $B_x = x (e_1 - e_2)(e_1 - e_2)^* + e_3 e_3^*$ is positive semidefinite for $x \ge 0$. -/
theorem chaLeeB_posSemidef {x : ℝ} (hx : 0 ≤ x) : (chaLeeB x).PosSemidef := by
  have e : chaLeeB x = (x : ℂ) • vecMulVec ![(1 : ℂ), -1, 0] (star ![(1 : ℂ), -1, 0])
      + vecMulVec ![(0 : ℂ), 0, 1] (star ![(0 : ℂ), 0, 1]) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [chaLeeB, vecMulVec]
  rw [e]
  exact ((posSemidef_vecMulVec_self_star _).smul (Complex.zero_le_real.2 hx)).add
    (posSemidef_vecMulVec_self_star _)

/-- $A_x + \varepsilon$ is positive definite for $x \ge 0$ and $\varepsilon > 0$. -/
theorem chaLeeA_add_posDef {x ε : ℝ} (hx : 0 ≤ x) (hε : 0 < ε) :
    (chaLeeA x + (ε : ℂ) • 1).PosDef := by
  rw [add_comm]
  exact (PosDef.one.smul (Complex.zero_lt_real.2 hε)).add_posSemidef (chaLeeA_posSemidef hx)

/-- $B_x + \varepsilon$ is positive definite for $x \ge 0$ and $\varepsilon > 0$. -/
theorem chaLeeB_add_posDef {x ε : ℝ} (hx : 0 ≤ x) (hε : 0 < ε) :
    (chaLeeB x + (ε : ℂ) • 1).PosDef := by
  rw [add_comm]
  exact (PosDef.one.smul (Complex.zero_lt_real.2 hε)).add_posSemidef (chaLeeB_posSemidef hx)

local notation "A₁" => (!![1000, 0, 0; 0, 1, -1; 0, -1, 1] : Matrix (Fin 3) (Fin 3) ℂ)
local notation "B₁" => (!![1, -1, 0; -1, 1, 0; 0, 0, 1000] : Matrix (Fin 3) (Fin 3) ℂ)
local notation "A₂" => (!![10001, 0, 0; 0, 11, -10; 0, -10, 11] : Matrix (Fin 3) (Fin 3) ℂ)
local notation "B₂" => (!![11, -10, 0; -10, 11, 0; 0, 0, 10001] : Matrix (Fin 3) (Fin 3) ℂ)

/-- $A_{1/1000} = 10^{-3} A_1$ with the integer matrix $A_1$. -/
theorem chaLeeA_eq_smul : chaLeeA (1 / 1000) = (1 / 1000 : ℂ) • A₁ := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [chaLeeA]

/-- $B_{1/1000} = 10^{-3} B_1$ with the integer matrix $B_1$. -/
theorem chaLeeB_eq_smul : chaLeeB (1 / 1000) = (1 / 1000 : ℂ) • B₁ := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [chaLeeB]

/-- $A_{1/1000} + 10^{-4} = 10^{-4} A_2$ with the integer matrix $A_2$. -/
theorem chaLeeA_add_eq_smul :
    chaLeeA (1 / 1000) + ((1 / 10000 : ℝ) : ℂ) • 1 = (1 / 10000 : ℂ) • A₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [chaLeeA]

/-- $B_{1/1000} + 10^{-4} = 10^{-4} B_2$ with the integer matrix $B_2$. -/
theorem chaLeeB_add_eq_smul :
    chaLeeB (1 / 1000) + ((1 / 10000 : ℝ) : ℂ) • 1 = (1 / 10000 : ℂ) • B₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [chaLeeB]

/-- The exact values for the scaled pair $A_1, B_1$, computed with Pascal's recursion:
$\operatorname{Tr}(A_1^5 B_1^5)$ and $\operatorname{Tr}$ of the sum of the 252 words. -/
theorem values_one :
    (A₁ ^ 5 * B₁ ^ 5).trace = 32000000000000256
      ∧ (wordSum A₁ B₁ 10 5).trace = 12847356269761869762 := by
  have h0_0 : wordSum A₁ B₁ 0 0 = !![1, 0, 0; 0, 1, 0; 0, 0, 1] := by
    rw [wordSum_zero_zero, Matrix.one_fin_three]
  have h1_0 : wordSum A₁ B₁ 1 0 =
      !![1, -1, 0;
         -1, 1, 0;
         0, 0, 1000] := by
    rw [wordSum_succ_zero A₁ B₁ 0, h0_0]
    norm_num [Matrix.mul_fin_three]
  have h1_1 : wordSum A₁ B₁ 1 1 =
      !![1000, 0, 0;
         0, 1, -1;
         0, -1, 1] := by
    rw [wordSum_succ_succ A₁ B₁ 0 0, h0_0,
      wordSum_eq_zero_of_lt A₁ B₁ (by norm_num : 0 < 0 + 1)]
    norm_num [Matrix.mul_fin_three]
  have h2_0 : wordSum A₁ B₁ 2 0 =
      !![2, -2, 0;
         -2, 2, 0;
         0, 0, 1000000] := by
    rw [wordSum_succ_zero A₁ B₁ 1, h1_0]
    norm_num [Matrix.mul_fin_three]
  have h2_1 : wordSum A₁ B₁ 2 1 =
      !![2000, -1001, 1;
         -1001, 2, -1001;
         1, -1001, 2000] := by
    rw [wordSum_succ_succ A₁ B₁ 1 0, h1_0,
      h1_1]
    norm_num [Matrix.mul_fin_three]
  have h2_2 : wordSum A₁ B₁ 2 2 =
      !![1000000, 0, 0;
         0, 2, -2;
         0, -2, 2] := by
    rw [wordSum_succ_succ A₁ B₁ 1 1, h1_1,
      wordSum_eq_zero_of_lt A₁ B₁ (by norm_num : 1 < 1 + 1)]
    norm_num [Matrix.mul_fin_three]
  have h3_0 : wordSum A₁ B₁ 3 0 =
      !![4, -4, 0;
         -4, 4, 0;
         0, 0, 1000000000] := by
    rw [wordSum_succ_zero A₁ B₁ 2, h2_0]
    norm_num [Matrix.mul_fin_three]
  have h3_1 : wordSum A₁ B₁ 3 1 =
      !![5001, -3003, 1002;
         -3003, 1005, -1001002;
         1002, -1001002, 3000000] := by
    rw [wordSum_succ_succ A₁ B₁ 2 0, h2_0,
      h2_1]
    norm_num [Matrix.mul_fin_three]
  have h3_2 : wordSum A₁ B₁ 3 2 =
      !![3000000, -1001002, 1002;
         -1001002, 1005, -3003;
         1002, -3003, 5001] := by
    rw [wordSum_succ_succ A₁ B₁ 2 1, h2_1,
      h2_2]
    norm_num [Matrix.mul_fin_three]
  have h3_3 : wordSum A₁ B₁ 3 3 =
      !![1000000000, 0, 0;
         0, 4, -4;
         0, -4, 4] := by
    rw [wordSum_succ_succ A₁ B₁ 2 2, h2_2,
      wordSum_eq_zero_of_lt A₁ B₁ (by norm_num : 2 < 2 + 1)]
    norm_num [Matrix.mul_fin_three]
  have h4_0 : wordSum A₁ B₁ 4 0 =
      !![8, -8, 0;
         -8, 8, 0;
         0, 0, 1000000000000] := by
    rw [wordSum_succ_zero A₁ B₁ 3, h3_0]
    norm_num [Matrix.mul_fin_three]
  have h4_1 : wordSum A₁ B₁ 4 1 =
      !![12004, -8008, 1002004;
         -8008, 4012, -1001002004;
         1002004, -1001002004, 4000000000] := by
    rw [wordSum_succ_succ A₁ B₁ 3 0, h3_0,
      h3_1]
    norm_num [Matrix.mul_fin_three]
  have h4_2 : wordSum A₁ B₁ 4 2 =
      !![9002002, -4005007, 1006005;
         -4005007, 2004014, -4005007;
         1006005, -4005007, 9002002] := by
    rw [wordSum_succ_succ A₁ B₁ 3 1, h3_1,
      h3_2]
    norm_num [Matrix.mul_fin_three]
  have h4_3 : wordSum A₁ B₁ 4 3 =
      !![4000000000, -1001002004, 1002004;
         -1001002004, 4012, -8008;
         1002004, -8008, 12004] := by
    rw [wordSum_succ_succ A₁ B₁ 3 2, h3_2,
      h3_3]
    norm_num [Matrix.mul_fin_three]
  have h4_4 : wordSum A₁ B₁ 4 4 =
      !![1000000000000, 0, 0;
         0, 8, -8;
         0, -8, 8] := by
    rw [wordSum_succ_succ A₁ B₁ 3 3, h3_3,
      wordSum_eq_zero_of_lt A₁ B₁ (by norm_num : 3 < 3 + 1)]
    norm_num [Matrix.mul_fin_three]
  have h5_0 : wordSum A₁ B₁ 5 0 =
      !![16, -16, 0;
         -16, 16, 0;
         0, 0, 1000000000000000] := by
    rw [wordSum_succ_zero A₁ B₁ 4, h4_0]
    norm_num [Matrix.mul_fin_three]
  have h5_1 : wordSum A₁ B₁ 5 1 =
      !![28012, -20020, 1002004008;
         -20020, 12028, -1001002004008;
         1002004008, -1001002004008, 5000000000000] := by
    rw [wordSum_succ_succ A₁ B₁ 4 0, h4_0,
      h4_1]
    norm_num [Matrix.mul_fin_three]
  have h5_2 : wordSum A₁ B₁ 5 2 =
      !![25011009, -14017021, 1007015012;
         -14017021, 1007015037, -5006013016;
         1007015012, -5006013016, 14003004004] := by
    rw [wordSum_succ_succ A₁ B₁ 4 1, h4_1,
      h4_2]
    norm_num [Matrix.mul_fin_three]
  have h5_3 : wordSum A₁ B₁ 5 3 =
      !![14003004004, -5006013016, 1007015012;
         -5006013016, 1007015037, -14017021;
         1007015012, -14017021, 25011009] := by
    rw [wordSum_succ_succ A₁ B₁ 4 2, h4_2,
      h4_3]
    norm_num [Matrix.mul_fin_three]
  have h5_4 : wordSum A₁ B₁ 5 4 =
      !![5000000000000, -1001002004008, 1002004008;
         -1001002004008, 12028, -20020;
         1002004008, -20020, 28012] := by
    rw [wordSum_succ_succ A₁ B₁ 4 3, h4_3,
      h4_4]
    norm_num [Matrix.mul_fin_three]
  have h5_5 : wordSum A₁ B₁ 5 5 =
      !![1000000000000000, 0, 0;
         0, 16, -16;
         0, -16, 16] := by
    rw [wordSum_succ_succ A₁ B₁ 4 4, h4_4,
      wordSum_eq_zero_of_lt A₁ B₁ (by norm_num : 4 < 4 + 1)]
    norm_num [Matrix.mul_fin_three]
  have h6_1 : wordSum A₁ B₁ 6 1 =
      !![64032, -48048, 1002004008016;
         -48048, 32064, -1001002004008016;
         1002004008016, -1001002004008016, 6000000000000000] := by
    rw [wordSum_succ_succ A₁ B₁ 5 0, h5_0,
      h5_1]
    norm_num [Matrix.mul_fin_three]
  have h6_2 : wordSum A₁ B₁ 6 2 =
      !![67040030, -1041052058, 1008017036028;
         -1041052058, 1002023048094, -6007015032036;
         1008017036028, -6007015032036, 20004006008008] := by
    rw [wordSum_succ_succ A₁ B₁ 5 1, h5_1,
      h5_2]
    norm_num [Matrix.mul_fin_three]
  have h6_3 : wordSum A₁ B₁ 6 3 =
      !![44020026020, -20030049053, 1008036044033;
         -20030049053, 12026056106, -20030049053;
         1008036044033, -20030049053, 44020026020] := by
    rw [wordSum_succ_succ A₁ B₁ 5 2, h5_2,
      h5_3]
    norm_num [Matrix.mul_fin_three]
  have h6_4 : wordSum A₁ B₁ 6 4 =
      !![20004006008008, -6007015032036, 1008017036028;
         -6007015032036, 1002023048094, -1041052058;
         1008017036028, -1041052058, 67040030] := by
    rw [wordSum_succ_succ A₁ B₁ 5 3, h5_3,
      h5_4]
    norm_num [Matrix.mul_fin_three]
  have h6_5 : wordSum A₁ B₁ 6 5 =
      !![6000000000000000, -1001002004008016, 1002004008016;
         -1001002004008016, 32064, -48048;
         1002004008016, -48048, 64032] := by
    rw [wordSum_succ_succ A₁ B₁ 5 4, h5_4,
      h5_5]
    norm_num [Matrix.mul_fin_three]
  have h7_2 : wordSum A₁ B₁ 7 2 =
      !![1172124088, -1003112148152, 1009019040084064;
         -1003112148152, 1002005068140232, -7008017036076080;
         1009019040084064, -7008017036076080, 27005008012016016] := by
    rw [wordSum_succ_succ A₁ B₁ 6 1, h6_1,
      h6_2]
    norm_num [Matrix.mul_fin_three]
  have h7_3 : wordSum A₁ B₁ 7 3 =
      !![131090105073, -1073108163159, 1009045102121086;
         -1073108163159, 7041094185289, -27039087133130;
         1009045102121086, -27039087133130, 70031047060044] := by
    rw [wordSum_succ_succ A₁ B₁ 6 2, h6_2,
      h6_3]
    norm_num [Matrix.mul_fin_three]
  have h7_4 : wordSum A₁ B₁ 7 4 =
      !![70031047060044, -27039087133130, 1009045102121086;
         -27039087133130, 7041094185289, -1073108163159;
         1009045102121086, -1073108163159, 131090105073] := by
    rw [wordSum_succ_succ A₁ B₁ 6 3, h6_3,
      h6_4]
    norm_num [Matrix.mul_fin_three]
  have h7_5 : wordSum A₁ B₁ 7 5 =
      !![27005008012016016, -7008017036076080, 1009019040084064;
         -7008017036076080, 1002005068140232, -1003112148152;
         1009019040084064, -1003112148152, 1172124088] := by
    rw [wordSum_succ_succ A₁ B₁ 6 4, h6_4,
      h6_5]
    norm_num [Matrix.mul_fin_three]
  have h8_3 : wordSum A₁ B₁ 8 3 =
      !![2376322356232, -1011226350500448, 1010055124273318216;
         -1011226350500448, 8018136306564760, -35049109237346312;
         1010055124273318216, -35049109237346312, 104044072108136096] := by
    rw [wordSum_succ_succ A₁ B₁ 7 2, h7_2,
      h7_3]
    norm_num [Matrix.mul_fin_three]
  have h8_4 : wordSum A₁ B₁ 8 4 =
      !![228160239266174, -1107188344477419, 1010055220331370245;
         -1107188344477419, 68160362636838, -1107188344477419;
         1010055220331370245, -1107188344477419, 228160239266174] := by
    rw [wordSum_succ_succ A₁ B₁ 7 3, h7_3,
      h7_4]
    norm_num [Matrix.mul_fin_three]
  have h8_5 : wordSum A₁ B₁ 8 5 =
      !![104044072108136096, -35049109237346312, 1010055124273318216;
         -35049109237346312, 8018136306564760, -1011226350500448;
         1010055124273318216, -1011226350500448, 2376322356232] := by
    rw [wordSum_succ_succ A₁ B₁ 7 4, h7_4,
      h7_5]
    norm_num [Matrix.mul_fin_three]
  have h9_4 : wordSum A₁ B₁ 9 4 =
      !![3711670939975593, -1012401699207562257, 1011066286681994063664;
         -1012401699207562257, 44242594251025329, -1150255590021330072;
         1011066286681994063664, -1150255590021330072, 367253420611656408] := by
    rw [wordSum_succ_succ A₁ B₁ 8 3, h8_3,
      h8_4]
    norm_num [Matrix.mul_fin_three]
  have h9_5 : wordSum A₁ B₁ 9 5 =
      !![367253420611656408, -1150255590021330072, 1011066286681994063664;
         -1150255590021330072, 44242594251025329, -1012401699207562257;
         1011066286681994063664, -1012401699207562257, 3711670939975593] := by
    rw [wordSum_succ_succ A₁ B₁ 8 4, h8_4,
      h8_5]
    norm_num [Matrix.mul_fin_three]
  have h10_5 : wordSum A₁ B₁ 10 5 =
      !![5229179950608579480, -1013596197391834612401, 1012078365370375265289921;
         -1013596197391834612401, 2388996368544710802, -1013596197391834612401;
         1012078365370375265289921, -1013596197391834612401, 5229179950608579480] := by
    rw [wordSum_succ_succ A₁ B₁ 9 4, h9_4,
      h9_5]
    norm_num [Matrix.mul_fin_three]
  refine ⟨?_, ?_⟩
  · rw [← wordSum_self A₁ B₁ 5, ← wordSum_zero_right A₁ B₁ 5, h5_5, h5_0, Matrix.mul_fin_three,
      trace_fin_three_of]
    norm_num
  · rw [h10_5, trace_fin_three_of]
    norm_num

/-- The exact values for the scaled pair $A_2, B_2$, computed with Pascal's recursion. -/
theorem values_two :
    (A₂ ^ 5 * B₂ ^ 5).trace = 408614445945108476181470703
      ∧ (wordSum A₂ B₂ 10 5).trace = 137861397810707426880478617156 := by
  have h0_0 : wordSum A₂ B₂ 0 0 = !![1, 0, 0; 0, 1, 0; 0, 0, 1] := by
    rw [wordSum_zero_zero, Matrix.one_fin_three]
  have h1_0 : wordSum A₂ B₂ 1 0 =
      !![11, -10, 0;
         -10, 11, 0;
         0, 0, 10001] := by
    rw [wordSum_succ_zero A₂ B₂ 0, h0_0]
    norm_num [Matrix.mul_fin_three]
  have h1_1 : wordSum A₂ B₂ 1 1 =
      !![10001, 0, 0;
         0, 11, -10;
         0, -10, 11] := by
    rw [wordSum_succ_succ A₂ B₂ 0 0, h0_0,
      wordSum_eq_zero_of_lt A₂ B₂ (by norm_num : 0 < 0 + 1)]
    norm_num [Matrix.mul_fin_three]
  have h2_0 : wordSum A₂ B₂ 2 0 =
      !![221, -220, 0;
         -220, 221, 0;
         0, 0, 100020001] := by
    rw [wordSum_succ_zero A₂ B₂ 1, h1_0]
    norm_num [Matrix.mul_fin_three]
  have h2_1 : wordSum A₂ B₂ 2 1 =
      !![220022, -100120, 100;
         -100120, 242, -100120;
         100, -100120, 220022] := by
    rw [wordSum_succ_succ A₂ B₂ 1 0, h1_0,
      h1_1]
    norm_num [Matrix.mul_fin_three]
  have h2_2 : wordSum A₂ B₂ 2 2 =
      !![100020001, 0, 0;
         0, 221, -220;
         0, -220, 221] := by
    rw [wordSum_succ_succ A₂ B₂ 1 1, h1_1,
      wordSum_eq_zero_of_lt A₂ B₂ (by norm_num : 1 < 1 + 1)]
    norm_num [Matrix.mul_fin_three]
  have h3_0 : wordSum A₂ B₂ 3 0 =
      !![4631, -4630, 0;
         -4630, 4631, 0;
         0, 0, 1000300030001] := by
    rw [wordSum_succ_zero A₂ B₂ 2, h2_0]
    norm_num [Matrix.mul_fin_three]
  have h3_1 : wordSum A₂ B₂ 3 1 =
      !![5631663, -3303960, 1002300;
         -3303960, 1006293, -1001302330;
         1002300, -1001302330, 3300660033] := by
    rw [wordSum_succ_succ A₂ B₂ 2 0, h2_0,
      h2_1]
    norm_num [Matrix.mul_fin_three]
  have h3_2 : wordSum A₂ B₂ 3 2 =
      !![3300660033, -1001302330, 1002300;
         -1001302330, 1006293, -3303960;
         1002300, -3303960, 5631663] := by
    rw [wordSum_succ_succ A₂ B₂ 2 1, h2_1,
      h2_2]
    norm_num [Matrix.mul_fin_three]
  have h3_3 : wordSum A₂ B₂ 3 3 =
      !![1000300030001, 0, 0;
         0, 4631, -4630;
         0, -4630, 4631] := by
    rw [wordSum_succ_succ A₂ B₂ 2 2, h2_2,
      wordSum_eq_zero_of_lt A₂ B₂ (by norm_num : 2 < 2 + 1)]
    norm_num [Matrix.mul_fin_three]
  have h4_0 : wordSum A₂ B₂ 4 0 =
      !![97241, -97240, 0;
         -97240, 97241, 0;
         0, 0, 10004000600040001] := by
    rw [wordSum_succ_zero A₂ B₂ 3, h3_0]
    norm_num [Matrix.mul_fin_three]
  have h4_1 : wordSum A₂ B₂ 4 1 =
      !![141302524, -92711120, 10024048600;
         -92711120, 44159764, -10014024648640;
         10024048600, -10014024648640, 44013201320044] := by
    rw [wordSum_succ_succ A₂ B₂ 3 0, h3_0,
      h3_1]
    norm_num [Matrix.mul_fin_three]
  have h4_2 : wordSum A₂ B₂ 4 2 =
      !![102642545326, -44067292520, 10068067200;
         -44067292520, 20048185046, -44067292520;
         10068067200, -44067292520, 102642545326] := by
    rw [wordSum_succ_succ A₂ B₂ 3 1, h3_1,
      h3_2]
    norm_num [Matrix.mul_fin_three]
  have h4_3 : wordSum A₂ B₂ 4 3 =
      !![44013201320044, -10014024648640, 10024048600;
         -10014024648640, 44159764, -92711120;
         10024048600, -92711120, 141302524] := by
    rw [wordSum_succ_succ A₂ B₂ 3 2, h3_2,
      h3_3]
    norm_num [Matrix.mul_fin_three]
  have h4_4 : wordSum A₂ B₂ 4 4 =
      !![10004000600040001, 0, 0;
         0, 97241, -97240;
         0, -97240, 97241] := by
    rw [wordSum_succ_succ A₂ B₂ 3 3, h3_3,
      wordSum_eq_zero_of_lt A₂ B₂ (by norm_num : 3 < 3 + 1)]
    norm_num [Matrix.mul_fin_three]
  have h5_0 : wordSum A₂ B₂ 5 0 =
      !![2042051, -2042050, 0;
         -2042050, 2042051, 0;
         0, 0, 100050010001000050001] := by
    rw [wordSum_succ_zero A₂ B₂ 4, h4_0]
    norm_num [Matrix.mul_fin_three]
  have h5_1 : wordSum A₂ B₂ 5 1 =
      !![3453946205, -2433917200, 100250511021000;
         -2433917200, 1413938255, -100150260512021050;
         100250511021000, -100150260512021050, 550220033002200055] := by
    rw [wordSum_succ_succ A₂ B₂ 4 0, h4_0,
      h4_1]
    norm_num [Matrix.mul_fin_three]
  have h5_2 : wordSum A₂ B₂ 5 2 =
      !![2982907466310, -1612425979300, 100801931713000;
         -1612425979300, 100801935204510, -550871705225200;
         100801931713000, -550871705225200, 1610813556812210] := by
    rw [wordSum_succ_succ A₂ B₂ 4 1, h4_1,
      h4_2]
    norm_num [Matrix.mul_fin_three]
  have h5_3 : wordSum A₂ B₂ 5 3 =
      !![1610813556812210, -550871705225200, 100801931713000;
         -550871705225200, 100801935204510, -1612425979300;
         100801931713000, -1612425979300, 2982907466310] := by
    rw [wordSum_succ_succ A₂ B₂ 4 2, h4_2,
      h4_3]
    norm_num [Matrix.mul_fin_three]
  have h5_4 : wordSum A₂ B₂ 5 4 =
      !![550220033002200055, -100150260512021050, 100250511021000;
         -100150260512021050, 1413938255, -2433917200;
         100250511021000, -2433917200, 3453946205] := by
    rw [wordSum_succ_succ A₂ B₂ 4 3, h4_3,
      h4_4]
    norm_num [Matrix.mul_fin_three]
  have h5_5 : wordSum A₂ B₂ 5 5 =
      !![100050010001000050001, 0, 0;
         0, 2042051, -2042050;
         0, -2042050, 2042051] := by
    rw [wordSum_succ_succ A₂ B₂ 4 4, h4_4,
      wordSum_eq_zero_of_lt A₂ B₂ (by norm_num : 4 < 4 + 1)]
    norm_num [Matrix.mul_fin_three]
  have h6_1 : wordSum A₂ B₂ 6 1 =
      !![82755132306, -61335013800, 1002605360741441500;
         -61335013800, 39914955366, -1001602755380742941560;
         1002605360741441500, -1001602755380742941560, 6603300660066003300066] := by
    rw [wordSum_succ_succ A₂ B₂ 5 0, h5_0,
      h5_1]
    norm_num [Matrix.mul_fin_three]
  have h6_2 : wordSum A₂ B₂ 6 2 =
      !![83479157918615, -1050097643734600, 1009222899022116000;
         -1050097643734600, 1002627566220573915, -6610920803728839300;
         1009222899022116000, -6610920803728839300, 23163669349823323315] := by
    rw [wordSum_succ_succ A₂ B₂ 5 1, h5_1,
      h5_2]
    norm_num [Matrix.mul_fin_three]
  have h6_3 : wordSum A₂ B₂ 6 3 =
      !![53059723747752620, -23193480328501600, 1009245064570349000;
         -23193480328501600, 13235076679003220, -23193480328501600;
         1009245064570349000, -23193480328501600, 53059723747752620] := by
    rw [wordSum_succ_succ A₂ B₂ 5 2, h5_2,
      h5_3]
    norm_num [Matrix.mul_fin_three]
  have h6_4 : wordSum A₂ B₂ 6 4 =
      !![23163669349823323315, -6610920803728839300, 1009222899022116000;
         -6610920803728839300, 1002627566220573915, -1050097643734600;
         1009222899022116000, -1050097643734600, 83479157918615] := by
    rw [wordSum_succ_succ A₂ B₂ 5 3, h5_3,
      h5_4]
    norm_num [Matrix.mul_fin_three]
  have h6_5 : wordSum A₂ B₂ 6 5 =
      !![6603300660066003300066, -1001602755380742941560, 1002605360741441500;
         -1001602755380742941560, 39914955366, -61335013800;
         1002605360741441500, -61335013800, 82755132306] := by
    rw [wordSum_succ_succ A₂ B₂ 5 4, h5_4,
      h5_5]
    norm_num [Matrix.mul_fin_three]
  have h7_2 : wordSum A₂ B₂ 7 2 =
      !![12246881252643071, -10038440147759833550, 10104266872701688110500;
         -10038440147759833550, 10027066958451357583691, -77133449267679443750120;
         10104266872701688110500, -77133449267679443750120, 314312191982116522189641] := by
    rw [wordSum_succ_succ A₂ B₂ 6 1, h6_1,
      h6_2]
    norm_num [Matrix.mul_fin_three]
  have h7_3 : wordSum A₂ B₂ 7 3 =
      !![1650466822854363435, -10889505585393284400, 10104571843633740971000;
         -10889505585393284400, 77515631912468757485, -314704401268567473050;
         10104571843633740971000, -314704401268567473050, 851559868086618902085] := by
    rw [wordSum_succ_succ A₂ B₂ 6 2, h6_2,
      h6_3]
    norm_num [Matrix.mul_fin_three]
  have h7_4 : wordSum A₂ B₂ 7 4 =
      !![851559868086618902085, -314704401268567473050, 10104571843633740971000;
         -314704401268567473050, 77515631912468757485, -10889505585393284400;
         10104571843633740971000, -10889505585393284400, 1650466822854363435] := by
    rw [wordSum_succ_succ A₂ B₂ 6 3, h6_3,
      h6_4]
    norm_num [Matrix.mul_fin_three]
  have h7_5 : wordSum A₂ B₂ 7 5 =
      !![314312191982116522189641, -77133449267679443750120, 10104266872701688110500;
         -77133449267679443750120, 10027066958451357583691, -10038440147759833550;
         10104266872701688110500, -10038440147759833550, 12246881252643071] := by
    rw [wordSum_succ_succ A₂ B₂ 6 4, h6_4,
      h6_5]
    norm_num [Matrix.mul_fin_three]
  have h8_3 : wordSum A₂ B₂ 8 3 =
      !![249531250313014194856, -101289380798310109036800, 101167070328182239618522000;
         -101289380798310109036800, 882593796226650460098136, -4096097328615930755061280;
         101167070328182239618522000, -4096097328615930755061280, 12745218845214351821339336] := by
    rw [wordSum_succ_succ A₂ B₂ 7 2, h7_2,
      h7_3]
    norm_num [Matrix.mul_fin_three]
  have h8_4 : wordSum A₂ B₂ 8 4 =
      !![29020521257004971366870, -113142850092597167062800, 101167082193516868534496000;
         -113142850092597167062800, 7999431927445662125670, -113142850092597167062800;
         101167082193516868534496000, -113142850092597167062800, 29020521257004971366870] := by
    rw [wordSum_succ_succ A₂ B₂ 7 3, h7_3,
      h7_4]
    norm_num [Matrix.mul_fin_three]
  have h8_5 : wordSum A₂ B₂ 8 5 =
      !![12745218845214351821339336, -4096097328615930755061280, 101167070328182239618522000;
         -4096097328615930755061280, 882593796226650460098136, -101289380798310109036800;
         101167070328182239618522000, -101289380798310109036800, 249531250313014194856] := by
    rw [wordSum_succ_succ A₂ B₂ 7 4, h7_4,
      h7_5]
    norm_num [Matrix.mul_fin_three]
  have h9_4 : wordSum A₂ B₂ 9 4 =
      !![3946216269133481318418426,
         -1014319663034192425935984300,
         1012885839684780189950388606000;
         -1014319663034192425935984300,
         51888927296780336565702666,
         -1185424652353106010701718240;
         1012885839684780189950388606000,
         -1185424652353106010701718240,
         471392613674823896225412366] := by
    rw [wordSum_succ_succ A₂ B₂ 8 3, h8_3,
      h8_4]
    norm_num [Matrix.mul_fin_three]
  have h9_5 : wordSum A₂ B₂ 9 5 =
      !![471392613674823896225412366,
         -1185424652353106010701718240,
         1012885839684780189950388606000;
         -1185424652353106010701718240,
         51888927296780336565702666,
         -1014319663034192425935984300;
         1012885839684780189950388606000,
         -1014319663034192425935984300,
         3946216269133481318418426] := by
    rw [wordSum_succ_succ A₂ B₂ 8 4, h8_4,
      h8_5]
    norm_num [Matrix.mul_fin_three]
  have h10_5 : wordSum A₂ B₂ 10 5 =
      !![56505674181558069630999396852,
         -10157769510453810421269154911600,
         10141023170120649603707550083115000;
         -10157769510453810421269154911600,
         24850049447591287618479823452,
         -10157769510453810421269154911600;
         10141023170120649603707550083115000,
         -10157769510453810421269154911600,
         56505674181558069630999396852] := by
    rw [wordSum_succ_succ A₂ B₂ 9 4, h9_4,
      h9_5]
    norm_num [Matrix.mul_fin_three]
  refine ⟨?_, ?_⟩
  · rw [← wordSum_self A₂ B₂ 5, ← wordSum_zero_right A₂ B₂ 5, h5_5, h5_0, Matrix.mul_fin_three,
      trace_fin_three_of]
    norm_num
  · rw [h10_5, trace_fin_three_of]
    norm_num

/-- $\operatorname{Tr}(A_x^5 B_x^5) = 32x^5 + 256x^{10}$ at $x = 1/1000$ (Cha and Lee). -/
theorem chaLee_trace :
    (chaLeeA (1 / 1000) ^ 5 * chaLeeB (1 / 1000) ^ 5).trace
      = ((32 * (1 / 1000) ^ 5 + 256 * (1 / 1000) ^ 10 : ℝ) : ℂ) := by
  rw [chaLeeA_eq_smul, chaLeeB_eq_smul, smul_pow, smul_pow, smul_mul_smul_comm, trace_smul,
    values_one.1]
  push_cast
  norm_num

/-- $p_{5,5}(A_x, B_x)
= \frac{x^4}{126}(5 + 1422x + 1675x^2 + 3130x^3 + 4875x^4 + 5930x^5 + 4881x^6)$ at $x = 1/1000$
(Cha and Lee). -/
theorem chaLee_wordAverage :
    wordAverage 5 5 (chaLeeA (1 / 1000)) (chaLeeB (1 / 1000))
      = (((1 / 1000) ^ 4 / 126 * (5 + 1422 * (1 / 1000) + 1675 * (1 / 1000) ^ 2
          + 3130 * (1 / 1000) ^ 3 + 4875 * (1 / 1000) ^ 4 + 5930 * (1 / 1000) ^ 5
          + 4881 * (1 / 1000) ^ 6) : ℝ) : ℂ) := by
  rw [chaLeeA_eq_smul, chaLeeB_eq_smul, wordAverage_smul, wordAverage_eq, values_one.2,
    show Nat.choose (5 + 5) 5 = 252 by decide]
  push_cast
  norm_num

/-- **The Cha-Lee counterexample to the upper half**: for $x = 1/1000$ and $n = m = 5$,
$\operatorname{Tr}(A_x^5 B_x^5) < p_{5,5}(A_x, B_x)$. -/
theorem chaLee_counterexample :
    (chaLeeA (1 / 1000) ^ 5 * chaLeeB (1 / 1000) ^ 5).trace.re
      < (wordAverage 5 5 (chaLeeA (1 / 1000)) (chaLeeB (1 / 1000))).re := by
  rw [chaLee_trace, chaLee_wordAverage, Complex.ofReal_re, Complex.ofReal_re]
  norm_num

/-- **The upper half of OQP 40 is false** for positive semidefinite matrices. -/
theorem not_upperHalf : ¬ UpperHalf := fun h =>
  absurd (h 3 _ _ (chaLeeA_posSemidef (by norm_num)) (chaLeeB_posSemidef (by norm_num)) 5 5)
    (not_le.2 chaLee_counterexample)

/-- **The counterexample for positive definite matrices**: with $A = A_x + 10^{-4}$,
$B = B_x + 10^{-4}$, $x = 1/1000$ and $n = m = 5$,
$\operatorname{Tr}(A^5 B^5) < p_{5,5}(A, B)$. -/
theorem chaLee_perturbed_counterexample :
    ((chaLeeA (1 / 1000) + ((1 / 10000 : ℝ) : ℂ) • 1) ^ 5
        * (chaLeeB (1 / 1000) + ((1 / 10000 : ℝ) : ℂ) • 1) ^ 5).trace.re
      < (wordAverage 5 5 (chaLeeA (1 / 1000) + ((1 / 10000 : ℝ) : ℂ) • 1)
          (chaLeeB (1 / 1000) + ((1 / 10000 : ℝ) : ℂ) • 1)).re := by
  rw [chaLeeA_add_eq_smul, chaLeeB_add_eq_smul, wordAverage_smul, wordAverage_eq, values_two.2,
    smul_pow, smul_pow, smul_mul_smul_comm, trace_smul, values_two.1,
    show Nat.choose (5 + 5) 5 = 252 by decide]
  have e1 : ((1 / 10000 : ℂ) ^ 5 * (1 / 10000) ^ 5) • (408614445945108476181470703 : ℂ)
      = (((1 / 10000) ^ 10 * 408614445945108476181470703 : ℝ) : ℂ) := by
    push_cast
    ring
  have e2 : (1 / 10000 : ℂ) ^ (5 + 5) * (((252 : ℕ) : ℂ)⁻¹ * 137861397810707426880478617156)
      = (((1 / 10000) ^ 10 * ((252 : ℝ)⁻¹ * 137861397810707426880478617156) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [e1, e2, Complex.ofReal_re, Complex.ofReal_re]
  norm_num

/-- **The chain of OQP 40 is false** for positive definite matrices. -/
theorem not_refinedBMV : ¬ RefinedBMV := fun h =>
  absurd (h 3 _ _ (chaLeeA_add_posDef (by norm_num) (by norm_num))
      (chaLeeB_add_posDef (by norm_num) (by norm_num)) 5 5).2
    (not_le.2 chaLee_perturbed_counterexample)

/-- **Open Quantum Problem 40 has a negative answer**: the chain
$\operatorname{Tr}\exp(n \log A + m \log B) \le p_{n,m}(A,B) \le \operatorname{Tr}(A^n B^m)$ fails
for some positive definite $A, B$ (Cha and Lee). -/
theorem refinedBMV : False ↔ RefinedBMV :=
  ⟨False.elim, not_refinedBMV⟩

end ChaLee

end OpenQuantumProblem40
