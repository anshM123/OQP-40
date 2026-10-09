# Theorem 1 of the lower-half note in Lean (the case n = m = 3)

Authors: Ansh Mishra, Aryan Senthilkumar. License: MIT.

## What is formalized

Theorem 1 of [`../math/04-lower-half-new-cases.md`](../math/04-lower-half-new-cases.md): for positive semidefinite
complex matrices A, B of every size,

- **(core)** 3 Re Tr((AB)³) ≤ Re Tr(A³B³) + 2 Re Tr(A²BAB²);
- **(main)** Re Tr((AB)³) ≤ Re p₃,₃(A, B), where p₃,₃ is `wordAverage 3 3` of `OQP40/Statement.lean` (the average of
  the traces of the 20 words with three letters A and three letters B);
- the link between them, valid for all square matrices: 20 p₃,₃ = 6 Tr(A³B³) + 6 Tr(A²BAB²) + 6 Tr(A²B²AB) +
  2 Tr((AB)³), where for Hermitian A, B the middle two traces are complex conjugates.

The proofs are complete and kernel-checked. They use no `sorry`, `admit`, new axioms or `native_decide`, and the
definitions and theorems of `OQP40/Statement.lean` are unchanged.

**Not formalized.**
- The classical last step Tr((AB)³) ≥ Tr exp(3 log A + 3 log B) (Araki–Lieb–Thirring and Lie–Trotter; Section 2.6 of
  the note). So the (3,3) case of `LowerHalf` is not proved in Lean, only Conjecture F at (3,3).
- Theorem 2 of the note (the sum-of-squares certificates) and Theorem 5 of
  [`../math/05-lower-half-m3.md`](../math/05-lower-half-m3.md) (the cases (n, 3)).

## Exact statements

Main theorems (namespace `OpenQuantumProblem40`, file `OQP40/Thm33.lean`):

```lean
theorem three_mul_trace_mul_cube_le {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    3 * ((A * B) ^ 3).trace.re
      ≤ (A ^ 3 * B ^ 3).trace.re + 2 * (A ^ 2 * B * A * B ^ 2).trace.re

theorem trace_mul_cube_le_wordAverage {d : ℕ} {A B : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    ((A * B) ^ 3).trace.re ≤ (wordAverage 3 3 A B).re

theorem wordAverage_three_three {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℂ) :
    20 * wordAverage 3 3 A B = 6 * (A ^ 3 * B ^ 3).trace + 6 * (A ^ 2 * B * A * B ^ 2).trace
      + 6 * (A ^ 2 * B ^ 2 * A * B).trace + 2 * ((A * B) ^ 3).trace

theorem trace_sq_sq_mul_re {n : Type*} [Fintype n] [DecidableEq n] {A B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (A ^ 2 * B ^ 2 * A * B).trace.re = (A ^ 2 * B * A * B ^ 2).trace.re
```

The main intermediate results (namespace `OpenQuantumProblem40.Thm33`), with
`kappa x y z = (x + y + z) * (x ^ 2 + y ^ 2 + z ^ 2) - 9 * x * y * z` and the kernel of Lemma 3 at the apex 1,
`kerE X Y = kappa 1 X Y - (Y - 1) * (Y - X) * √((Y + 4) * (Y + 4 * X))`:

```lean
-- the finite inequality (Theorem 1 in an eigenbasis of A)
theorem kernel_sum_nonneg {n : Type*} [Fintype n] {b : Matrix n n ℂ} (hb : b.PosSemidef)
    (α : n → ℝ) (hα : ∀ i, 0 ≤ α i) :
    0 ≤ ∑ i, ∑ j, ∑ k, (b i j * b j k * b k i).re * kappa (α i) (α j) (α k)

-- Lemma 3 at the apex 1
theorem kerE_psd {ι : Type*} [Fintype ι] (q : ι → ℝ) (hq : ∀ a, 1 < q a) (R : ι → ι → ℝ)
    (hR : PSDForm R) :
    0 ≤ ∑ a, ∑ b, R a b * kerE (min (q a) (q b)) (max (q a) (q b))

-- Lemma 4 (interval mixtures)
theorem interval_mixture {ι : Type*} [Fintype ι] {S : Set ℝ} {F : ℝ → ℝ → ℝ}
    (hF : IntervalHyp S F) (p : ι → ℝ) (hp : ∀ a, p a ∈ S) (R : ι → ι → ℝ) (hR : PSDForm R) :
    0 ≤ ∑ a, ∑ b, R a b * F (min (p a) (p b)) (max (p a) (p b))
```

`PSDForm R` means `∑ a, ∑ b, c a * c b * R a b ≥ 0` for every real vector `c`. `IntervalHyp S F` collects the
hypotheses of Lemma 4 on S: F ≥ 0, F nondecreasing in the first and nonincreasing in the second variable, and
F(s′,t) + F(s,t′) ≤ F(s′,t′) + F(s,t) for s′ ≤ s ≤ t ≤ t′.

## How the Lean proof follows the note

The Lean proof follows Sections 2.1–2.6 of the note. It differs in these technical points; no step of the written
proof was found to be wrong.

1. **Eigenbasis.** A = U diag(α) U* (`Matrix.IsHermitian.spectral_theorem`) and b = U* B U ≥ 0. With
   T(i,j,k) = b_ij b_jk b_ki the three traces are sums of T times α_iα_jα_k, α_i³ and α_i²α_j, and Re T is invariant
   under all permutations of (i, j, k). So the difference of the two sides of (core) is one third of
   Σ_{i,j,k} Re T(i,j,k) κ(α_i, α_j, α_k) (`core_diag`, `sum_kappa_eq`).
2. **Indices instead of distinct eigenvalues.** The sum runs over all indices, and the eigenvalues may repeat. The
   certificate (`share`) is defined on the values: the largest value of a triple gets cap, the smallest gets
   E = κ − cap, the middle one gets 0, and a point whose value equals the apex value gets 0. The share identity holds
   for every triple, also with repeated values (`share_add_share_add_share`). Lemma 2 then follows from the rotation
   invariance of T alone (`sum_kappa_eq_three_mul_sum_share`).
3. **Lemma 3.** The weight is w(X) = (X − 1)^{3/2}, so F = E/(w(X)w(Y)) is the function √(B/C)·G of Section 2.4 of the
   note. The conditions F ≥ 0, F_X ≥ 0, F_Y ≤ 0, F_XY ≤ 0 (the note's (I)–(III)) are proved by the method of
   Sections 3–4 of `05-lower-half-m3.md`: multiplied by a power of r = √((Y+4)(Y+4X)), each has the form α + βr;
   squaring reduces it to polynomials that have only nonnegative coefficients after X = 1 + u, Y = 1 + u + v
   (`OQP40/Thm33Signs.lean`; the largest has 42 terms and degree 10). The polynomials were computed for this weight;
   the rational parametrization and the discriminant of the note are not used.
4. **Lemma 4** is proved by induction on the set of values (removing the smallest one), which amounts to the
   telescoping decomposition of the note. Its hypotheses come from the derivative signs by the mean value theorem
   (`monotoneOn_of_hasDerivWithinAt_nonneg`, `antitoneOn_of_hasDerivWithinAt_nonpos`); the rectangle inequality uses
   it twice, through F_XY ≤ 0.
5. **Semidefinite matrices.** The finite inequality is proved for eigenvalues α_i > 0 (where the apex can be scaled
   to 1, `above_eq`) and extended to α_i ≥ 0 by letting α_i + ε → α_i; the sum is a polynomial in ε.

## Files

All in `OQP40/`, in dependency order (they import only Mathlib and, for `Thm33.lean`, `OQP40.Statement`):

| File | Lines | Content |
|---|---|---|
| `Thm33Interval.lean` | 197 | Lemma 4 (interval mixtures) |
| `Thm33Signs.lean` | 275 | the kernel E, the closed forms of its derivatives, the four sign conditions |
| `Thm33Kernel.lean` | 337 | the derivatives of F, the mean value theorem, the hypotheses of Lemma 4, Lemma 3 |
| `Thm33Reduction.lean` | 332 | the certificate, the share identity, homogeneity, Lemma 2, positivity of R^(l), the finite inequality |
| `Thm33.lean` | 334 | the eigenbasis, the symmetrization, the word identity, (core) and (main) |
| `AxiomsThm33.lean` | 40 | `#print axioms` for the results above |

They are listed in the `OQP40` library of `lakefile.toml` (except `AxiomsThm33.lean`, like `Axioms.lean`) and in
`BUILD_ORDER.txt`, and `check.sh` prints the axioms from `logs_check/OQP40.AxiomsThm33.log`.

## Axioms

Output of `lake env lean OQP40/AxiomsThm33.lean`:

```
'OpenQuantumProblem40.three_mul_trace_mul_cube_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenQuantumProblem40.trace_mul_cube_le_wordAverage' depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenQuantumProblem40.wordAverage_three_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenQuantumProblem40.trace_sq_sq_mul_re' depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenQuantumProblem40.Thm33.core_diag' depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenQuantumProblem40.Thm33.sum_kappa_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenQuantumProblem40.Thm33.kernel_sum_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenQuantumProblem40.Thm33.kernel_sum_nonneg_of_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenQuantumProblem40.Thm33.share_add_share_add_share' depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenQuantumProblem40.Thm33.sum_kappa_eq_three_mul_sum_share' depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenQuantumProblem40.Thm33.psdForm_reT' depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenQuantumProblem40.Thm33.sum_mul_share_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenQuantumProblem40.Thm33.above_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenQuantumProblem40.Thm33.kerE_psd' depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenQuantumProblem40.Thm33.intervalHyp_kerF' depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenQuantumProblem40.Thm33.kerE_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenQuantumProblem40.Thm33.cond1' depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenQuantumProblem40.Thm33.cond2' depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenQuantumProblem40.Thm33.cond3' depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenQuantumProblem40.Thm33.interval_mixture' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Check

Lean `v4.33.1`, Mathlib at the pinned revision (`lake-manifest.json`). The full check was rerun on a fresh copy of
this folder, with `packagesDir` pointed to an existing checkout of the pinned packages, by `bash check.sh`:
- the keyword scan for `sorry`, `admit`, `axiom` and `native_decide` found nothing;
- all 50 files of `BUILD_ORDER.txt` were elaborated and kernel-checked with exit code 0, in 762 s in total; each of the
  six new files took about 20 s and produced no warnings;
- there are no nonstandard axiom lines.

The output is in [`logs/check_thm33.log`](logs/check_thm33.log), and the axioms output above in
[`logs/OQP40.AxiomsThm33.log`](logs/OQP40.AxiomsThm33.log).
