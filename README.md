# Open Quantum Problem 40: the refined BMV inequality

**Authors:** Ansh Mishra, Aryan Senthilkumar. **License:** MIT. **Started:** 2026-10-08; **updated:** 2026-10-09.

This repository concerns **IQOQI Vienna Open Quantum Problem 40**, "Refinement of the Bessis–Moussa–Villani
conjecture". The problem is due to D. Hägele, communicated by R. F. Werner, and is also listed as
google-deepmind/formal-conjectures issue #3457.

For positive (semi)definite d × d matrices A, B and integers n, m ≥ 0, let $p_{n,m}(A,B)$ be the average of
$\operatorname{Tr}W$ over all words W with n letters A and m letters B. Equivalently, $p_{n,m}$ is the coefficient of
$t^m$ in $\operatorname{Tr}(A+tB)^{n+m}$, divided by $\binom{n+m}{n}$. The problem asks whether

$$\operatorname{Tr}(A^nB^m)\ \ge\ p_{n,m}(A,B)\ \ge\ \operatorname{Tr}\exp(n\log A+m\log B).$$

## Summary

- **The answer to OQP 40 is no.** The upper half fails (Cha and Lee); we machine-checked the counterexample in Lean,
  also for positive definite matrices.
- **The pinching inequality** that repairs the upper half (Dinh's conjecture) holds for all word lengths, with an
  exact formula for the gap; machine-checked in Lean.
- **The lower half is open in general.** We prove it in every dimension **whenever min(n, m) ≤ 3**, for all n (computer-assisted
  and independently checked for n ≥ 37; the key (3,3) inequality machine-checked in Lean), and at (n, 4) and (4, n) for
  n ≤ 16 and n = 18, 20, 22, and (4, 6), (6, 4). The open case with the fewest letters is (5, 5), exactly where
  the upper half fails.
  Extensive searches found no counterexample. [Coverage map](lower-half/coverage.svg).
- Nothing here has been refereed externally. The Lean proofs use only the standard axioms; the other new proofs
  were checked internally with independent code.

## Results

| Statement | Status | Where |
|---|---|---|
| **Upper half:** $\operatorname{Tr}(A^nB^m)\ge p_{n,m}(A,B)$ | **False.** Counterexample of H. Cha and J. Lee (arXiv:2603.19927): 3 × 3, n = m = 5. Not ours. We machine-checked it in Lean in exact arithmetic, also for a positive definite perturbation, so **OQP 40 as posed has a negative answer** (`refinedBMV : False ↔ RefinedBMV`). | [`lean/OQP40/Statement.lean`](lean/OQP40/Statement.lean) |
| **Pinching inequality** (T. H. Dinh's Conjecture 5.1, arXiv:2605.17782): $p_{n,m}(A,B)\ge\operatorname{Tr}(A^nE_A(B)^m)$ for A, B ≥ 0 and **all** n, m, where $E_A(B)$ is the pinching of B onto the eigenspaces of A. Strict iff AB ≠ BA (m ≥ 2). | **True for all n, m.** Dinh had proved m = 2. The inequality follows in a few lines from O. Heinävaara's Corollary 1.2 (arXiv:2310.03227v1, 2023; Invent. Math. 2025) on higher derivatives of trace functions; see §4.0 of the note. We found no place where this consequence is stated, and we give the first written proof. **Machine-checked in Lean** (`pinchingInequality`). | [`math/01-pinching-theorem.md`](math/01-pinching-theorem.md), Theorems 1–2, §4.0; [`lean/OQP40/Pinching.lean`](lean/OQP40/Pinching.lean) |
| **Exact gap identity:** $p_{n,m}(A,B)-\operatorname{Tr}(A^nE_A(B)^m)=m(m-1)\iint s^{m-2}\tau^n\rho(s,\tau)\,ds\,d\tau$, with an explicit density ρ ≥ 0 | **Proved here; machine-checked in Lean** (`gap_identity`, `wordAverage_eq_trace_pinching_add`) | same note, Theorem 1 |
| **Corrected upper bound:** $p_{n,m}\le\operatorname{Tr}(A^nE_A(B)^m)+m(m-1)\|B\|^{m-2}S_n$, with a matching lower bound (equality for m = 2) | **Proved here** | same note, Theorem 3 |
| Variants: indefinite letters under sign conditions; a Jensen form for functions convex in the B-variable; for fixed m, $n\mapsto p_{n,m}$ is the moment sequence of an explicit positive measure | **Proved here** | same note, Theorems 4–6 |
| The identity behind all of this: the pinched two-variable BMV identity (Theorem A) | **Proved** (full proof); **machine-checked in Lean** for P with spectrum in [0, 1], which is all that the results above need. The generic case is Heinävaara's explicit BMV measure; the general-multiplicity form was stated in our OQP 27 paper | [`math/02-theorem-A.md`](math/02-theorem-A.md), [`lean/`](lean/) |
| **Lower half:** $p_{n,m}(A,B)\ge\operatorname{Tr}\exp(n\log A+m\log B)$ | **Open in general.** Proved whenever min(n, m) ≤ 3, in every dimension (for n ≥ 37 computer-assisted and independently checked, [`math/07-lower-half-m3-all-n.md`](math/07-lower-half-m3-all-n.md)); when (n, m) is (4,4), (4,6) or (6,4), in every dimension; at (n, 4) and (4, n) for n = 3, …, 16 and n = 18, 20, 22, in every dimension (computer-assisted, exact); when A or B has at most two distinct eigenvalues (any dimension; this uses Stahl's theorem); and when B is entrywise nonnegative in some eigenbasis of A, which covers all d = 2. The (3,3) case, $\operatorname{Tr}(A^3B^3)+2\operatorname{Re}\operatorname{Tr}(A^2BAB^2)\ge3\operatorname{Tr}((AB)^3)$, has an elementary proof, machine-checked in Lean for positive semidefinite A, B of every size (`lean/OQP40/Thm33.lean`; the classical Araki–Lieb–Thirring step to the lower bound is not formalized); its single-word version is false. The cases (3,4), (4,3), (4,4), (4,6) and (6,4) rest on exact rational sum-of-squares certificates; the cases (n,3), (3,n) on an exact computation for each n; and the cases (n,4), (4,n) on an exact polynomial certificate rule for each n, whose positivity is proved with exact univariate root counting (for (4,4) also by hand). In all these cases a stronger form also holds: $p_{n,m}\ge\operatorname{Tr}(A^{n/m}B)^m$, or its version with the letters exchanged. The new cases were checked internally with independent code; they have not been refereed externally. No counterexample in extensive searches. | [`math/03-lower-half.md`](math/03-lower-half.md), [`math/04-lower-half-new-cases.md`](math/04-lower-half-new-cases.md), [`math/05-lower-half-m3.md`](math/05-lower-half-m3.md), [`math/06-lower-half-m4.md`](math/06-lower-half-m4.md), [`lower-half/`](lower-half/README.md) |

### In words

- **The upper half.** The upper half of OQP 40 is false, but its natural repair holds for every word length.
  - The commuting part of the word average is not the clustered word $A^nB^m$. It is the pinched term
    $\operatorname{Tr}(A^nE_A(B)^m)$.
  - The excess over it is an explicit integral of a nonnegative density.
  - The excess is bounded above and below by explicit multiples of the two-letter excess.
- **The lower half.** It is still open in general.
  - It now holds in every dimension **whenever min(n, m) ≤ 3**: at (n, 3) and (3, n) for n ≤ 36 by an exact computation
    for each n ([`math/05-lower-half-m3.md`](math/05-lower-half-m3.md)), and for all n ≥ 37 at once by a computer-assisted
    proof, independently checked ([`math/07-lower-half-m3-all-n.md`](math/07-lower-half-m3-all-n.md)). It also holds at
    (n, m) = (4,4), (4,6) and (6,4); and at (n, 4) and (4, n) for n = 3, …, 16 and n = 18, 20, 22
    (an exact polynomial certificate for each n, [`math/06-lower-half-m4.md`](math/06-lower-half-m4.md)).
  - The (3,3) case has an elementary proof: an explicit certificate, plus the positivity of three explicit functions
    of two variables. The other five cases follow from exact sum-of-squares identities. Identities of that kind
    provably do not exist at (3,3) and (6,3), for the substitutions we tried.
  - Any proof of the general case must be at least as strong as Stahl's theorem (the former BMV conjecture), because
    the lower half implies $p_{n,m}>0$.

## Verification

**Lean.** The negative answer to OQP 40, the pinching inequality for all n, m with its exact gap identity, and the
(3,3) inequality $\operatorname{Tr}(A^3B^3)+2\operatorname{Re}\operatorname{Tr}(A^2BAB^2)\ge3\operatorname{Tr}((AB)^3)$
(hence $p_{3,3}\ge\operatorname{Tr}((AB)^3)$) are machine-checked in Lean 4 with Mathlib. They use only the standard axioms `propext`, `Classical.choice` and `Quot.sound`,
and nothing is assumed: no `sorry`, no new axioms, no `native_decide`. See [`lean/README.md`](lean/README.md).

```bash
cd lean
lake exe cache get    # prebuilt Mathlib at the pinned revision
bash check.sh         # checks every file from source and prints the axioms; about 12 minutes
```

**Independent check.** An independent check of the pinching theorem, with code written from scratch in exact rational
and ball arithmetic, found **no errors**. See [`independent-check/REPORT.md`](independent-check/REPORT.md); its scripts
and logs are in `independent-check/scripts/`. Its results:
- Theorem 1 is confirmed exactly for d = 2.
- It is confirmed to 28–39 significant digits for d = 3, 4.
- It is confirmed to 26 digits on the Cha–Lee pair.
- About 27,000 exact cases of Theorems 2–5 and an adversarial search found no violation.

**Our own checks.**

```bash
pip install numpy scipy mpmath sympy python-flint
python code/verify_pinching.py          # Theorems 1-4: 40,500 + 7,500 cases, and quadrature of the gap identity
python code/chalee_family.py            # Cha-Lee family: lower half, doubling counterexample, pinched bound
python code/oqp40_second_order.py       # near-commuting expansion of the lower half
```

The GPU searches (`code/oqp40_torch.py`, `code/negword_search.py`, `code/oqp40_aux.py`) need PyTorch. The logs of the
runs quoted in the notes are in `logs/`, and [`logs/COMMANDS.md`](logs/COMMANDS.md) records the command behind each
one.

**Lower half, new cases.** The certificates, the scripts behind the (3,3) proof, and two independent checks written
with new code are in [`lower-half/`](lower-half/README.md), with one command per log. These checks are internal, not
external referee reports. For example:

```bash
cd lower-half/sos && python verify_certificate.py certs/*.json   # all 25 certificate files, exact; about 2 minutes
cd ../thm33/independent-check && python r3_interval.py           # (I)-(III) of the (3,3) proof, interval arithmetic
cd ../../m3 && python verify_n.py 12                               # Conjecture F at (12,3), exact; under a second
cd ../m4 && python verify_rule_independent.py rules/n8.json        # Conjecture F at (8,4), exact; a few seconds
```

## Credits

- **The problem:** D. Hägele (communicated by R. F. Werner), IQOQI Vienna Open Quantum Problems, Problem 40.
- **The counterexample to the upper half:** H. Cha and J. Lee, arXiv:2603.19927 (2026).
- **The pinching conjecture and its m = 2 case:** T. H. Dinh, arXiv:2605.17782 (2026).
- **Stahl's theorem and its explicit atoms/density structure:** H. R. Stahl, Acta Math. 211 (2013) 255–290.
- **Higher derivatives of trace functions:** O. Heinävaara, *Tracial joint spectral measures*, arXiv:2310.03227v1 (2023),
  Invent. Math. 239 (2025), Corollary 1.2. If f⁽ᵏ⁾ ≥ 0, then t ↦ tr f(tA + B) has a nonnegative k-th derivative, with
  A ≥ 0 needed for odd k. The pinching inequality follows from it by the short argument in §4.0 of the note.
- **The explicit |Im|-density for simple spectrum:** O. Heinävaara, *Tracial joint spectral measures*, PhD thesis,
  Princeton (2024).
- **The high-frequency averaging lemma** is a special case of D. Burgarth, P. Facchi, H. Nakazato, S. Pascazio,
  K. Yuasa, Quantum 3, 152 (2019).
- **Equivalent forms of BMV:** E. H. Lieb and R. Seiringer, J. Stat. Phys. 115 (2004).
- **Words with negative trace:** C. R. Johnson and C. J. Hillar, SIAM J. Matrix Anal. Appl. 23 (2002); F. Garbe and
  F. Wei, arXiv:2605.02314.
- **Single-word bounds for 2 × 2 matrices:** S. Furuichi, K. Kuriyama and K. Yanagi, *Trace inequalities for products
  of matrices*, Linear Algebra Appl. 430 (2009) 2271–2276, arXiv:1001.1384. Their Theorem 2.2 gives the d = 2 case of
  the (3,3) inequality; with a limit in the exponents it gives every single-word bound
  $\operatorname{Tr}W\ge\operatorname{Tr}(A^{n/m}B)^m$ for d = 2, hence the d = 2 case of the lower half. Their
  Conjecture 2.8(i) would imply the (3,3) inequality in every dimension, but it fails for 3 × 3 matrices: see our
  single-word example in [`math/04-lower-half-new-cases.md`](math/04-lower-half-new-cases.md), Section 3.
- **A related single-word question:** T. Ando, F. Hiai and K. Okubo, Math. Inequal. Appl. 3 (2000) 307–318, (1.7);
  negative answers by A. Plevnik (2016) and by E. A. Carlen and E. H. Lieb, J. Math. Phys. 63 (2022) 062203.
- **The Araki–Lieb–Thirring inequality and the Lie–Trotter formula,** used for the last step of the lower half: see,
  for example, R. Bhatia, *Matrix Analysis*, Springer, 1997, Chapter IX.

## Citation

See [`CITATION.cff`](CITATION.cff).
