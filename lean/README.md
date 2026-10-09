# Lean 4 formalization

Lean `v4.33.1` with Mathlib at the pinned revision (`lake-manifest.json`). Three libraries:
- `OQP40`: the statement of Open Quantum Problem 40, its negative answer, and the pinching inequality for all word
  lengths.
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
bash check.sh         # every file in BUILD_ORDER.txt, then #print axioms; about 12 minutes
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

Every declaration listed in `OQP40/Axioms.lean` depends only on `[propext, Classical.choice, Quot.sound]`. The output
of a full check is in `logs/`.

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
