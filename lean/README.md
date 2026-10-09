# Lean 4 formalization

Lean `v4.33.1` with Mathlib at the pinned revision (`lake-manifest.json`). Three libraries:
- `OQP40`: the statement of Open Quantum Problem 40, its negative answer, the pinching inequality for all word
  lengths, and Theorem 1 of the lower-half note, p₃,₃(A, B) ≥ Tr((AB)³) for positive semidefinite A, B (files
  `OQP40/Thm33*.lean` and `OQP40/AxiomsThm33.lean`; see below and `THM33_NOTES.md`).
- `HarmonicMajorization`: Theorem A (the pinched two-variable BMV identity) for Hermitian P with spectrum in [0, 1],
  with the density ρ and its properties. These 18 files are the part of our harmonic-majorization formalization that
  `OQP40/Pinching.lean` imports.
- `OQP27`: the 23 files of our OQP 27 formalization (github.com/anshM123/IQOQI-OQP-27) that Theorem A imports.

`OQP40/Statement.lean` is the standalone version of the file we wrote for Formal Conjectures (issue #3457). It imports
only Mathlib, and it states the answer as `False ↔ RefinedBMV` instead of `answer(False) ↔ RefinedBMV`. All
definitions (`wordAverage`, `pinching`, `RefinedBMV`, `UpperHalf`, `LowerHalf`, `PinchingInequality`) are written from
scratch with Mathlib.

## Check

```bash
lake exe cache get    # prebuilt Mathlib
bash check.sh         # every file in BUILD_ORDER.txt, then #print axioms; about 13 minutes
```

`check.sh` elaborates and kernel-checks each file with `lake env lean`, in dependency order. It scans for `sorry`,
`admit`, `axiom` and `native_decide`, and finally prints the axioms of the main theorems.

## Main declarations (namespace `OpenQuantumProblem40`)

| Declaration | Statement |
|---|---|
| `refinedBMV : False ↔ RefinedBMV` | OQP 40 as posed has a negative answer |
| `not_refinedBMV`, `not_upperHalf` | the chain fails for positive definite A, B; its upper half fails for positive semidefinite A, B |
| `chaLee_counterexample`, `chaLee_perturbed_counterexample` | Tr(A⁵B⁵) < p₅,₅(A, B) for the Cha–Lee pair at x = 1/1000, and for the positive definite pair obtained by adding 10⁻⁴ |
| `chaLee_trace`, `chaLee_wordAverage` | the exact values of both sides, computed by Lean in exact arithmetic |
| `pinchingInequality : PinchingInequality` | Tr(Aⁿ E_A(B)ᵐ) ≤ p_{n,m}(A, B) for positive semidefinite A, B and all n, m (Dinh's Conjecture 5.1) |
| `wordAverage_eq_trace_pinching_add` | p_{n,m}(A, B) = Tr(Aⁿ E_A(B)ᵐ) + r with an explicit r ≥ 0 |
| `gap_identity` | the exact gap formula: Σ_W Tr W(P, g) − C(n+m, n) Tr(Pⁿ g_dᵐ) = C(n+m, n) m(m−1) ∬ τⁿ s^{m−2} ρ(s, τ) ds dτ, for P with spectrum in [0, 1] |
| `moment_identity`, `coeff_identity` | the moment form of Theorem A and its coefficients |

`LowerHalf` is stated as a `Prop` and is not proved; it is open (see `math/03-lower-half.md`).

## Theorem 1 of the lower-half note (n = m = 3)

Theorem 1 of `math/04-lower-half-new-cases.md` is formalized for positive semidefinite A, B of every size. The last,
classical step from it to the (3,3) case of `LowerHalf` (Tr((AB)³) ≥ Tr exp(3 log A + 3 log B), by the
Araki–Lieb–Thirring inequality) is not formalized; Mathlib does not have it.

| Declaration | Statement |
|---|---|
| `three_mul_trace_mul_cube_le` | 3 Re Tr((AB)³) ≤ Re Tr(A³B³) + 2 Re Tr(A²BAB²) for positive semidefinite A, B indexed by any finite type |
| `trace_mul_cube_le_wordAverage` | Re Tr((AB)³) ≤ Re p₃,₃(A, B) (`wordAverage 3 3`) for positive semidefinite A, B |
| `wordAverage_three_three` | 20 p₃,₃(A, B) = 6 Tr(A³B³) + 6 Tr(A²BAB²) + 6 Tr(A²B²AB) + 2 Tr((AB)³) for all A, B |
| `trace_sq_sq_mul_re` | Re Tr(A²B²AB) = Re Tr(A²BAB²) for Hermitian A, B |
| `Thm33.kernel_sum_nonneg` | Σ_{i,j,k} Re(b_ij b_jk b_ki) κ(α_i, α_j, α_k) ≥ 0 for b ≥ 0 and α_i ≥ 0, with κ(x,y,z) = (x+y+z)(x²+y²+z²) − 9xyz |
| `Thm33.share_add_share_add_share`, `Thm33.sum_kappa_eq_three_mul_sum_share` | the certificate (apex shares) and Lemma 2 |
| `Thm33.kerE_psd` | Lemma 3: the kernel E(X, Y) = κ(1, X, Y) − (Y−1)(Y−X)√((Y+4)(Y+4X)) is positive semidefinite on (1, ∞) |
| `Thm33.kerE_nonneg`, `Thm33.cond1`, `Thm33.cond2`, `Thm33.cond3` | the four sign conditions on F = E/(w(X)w(Y)), w(X) = (X−1)^{3/2} |
| `Thm33.interval_mixture` | Lemma 4 (interval mixtures) |

Files, in dependency order: `Thm33Interval.lean` (Lemma 4), `Thm33Signs.lean` (the kernel and the four conditions, by
squaring and polynomials with nonnegative coefficients), `Thm33Kernel.lean` (derivatives, mean value theorem, Lemma 3),
`Thm33Reduction.lean` (certificate, Lemma 2, finite inequality), `Thm33.lean` (eigenbasis, word identity, main
theorems), `AxiomsThm33.lean` (`#print axioms`).

Every declaration listed in `OQP40/Axioms.lean` and `OQP40/AxiomsThm33.lean` depends only on
`[propext, Classical.choice, Quot.sound]`. The output of a full check is in `logs/` (`check_thm33.log` for the check
that includes the files above).

## Numbering and internal references

Some docstrings cite our working notes, which are not part of this repository:
- the `OQP27` files cite paths under `iqoqi/programs/oqp27B_all/`; the corresponding public statements and proofs are in
  github.com/anshM123/IQOQI-OQP-27 (`papers/math/main.tex`);
- the `HarmonicMajorization` files cite `THEOREMS.md`. The theorem names are the same in `math/02-theorem-A.md`, but
  the lemma numbers differ:

| working notes | `math/02-theorem-A.md` |
|---|---|
| Lemma 2.2 (pencil), incl. (6) | Lemma 1 (6) |
| Lemma 2.3 (Jensen identity) | Lemma 2 |
| Lemma 2.4 (real slices) | Lemma 3 |
| Lemma 2.5 (high-frequency averaging) | Lemma 4 |
| Lemma 2.6 (exponential polynomials) | Lemma 5 |

The Lean proof of Theorem A goes through a multi-line Radon identity, not through the distributional proof of the notes.
