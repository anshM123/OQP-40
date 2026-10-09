# Open Quantum Problem 40: the refined BMV inequality

**Authors:** Ansh Mishra, Aryan Senthilkumar. **License:** MIT. **Date:** 2026-10-08.

This repository concerns **IQOQI Vienna Open Quantum Problem 40**, "Refinement of the Bessis–Moussa–Villani
conjecture". The problem is due to D. Hägele, communicated by R. F. Werner, and is also listed as
google-deepmind/formal-conjectures issue #3457.

For positive (semi)definite d × d matrices A, B and integers n, m ≥ 0, let $p_{n,m}(A,B)$ be the average of
$\operatorname{Tr}W$ over all words W with n letters A and m letters B. Equivalently, $p_{n,m}$ is the coefficient of
$t^m$ in $\operatorname{Tr}(A+tB)^{n+m}$, divided by $\binom{n+m}{n}$. The problem asks whether

$$\operatorname{Tr}(A^nB^m)\ \ge\ p_{n,m}(A,B)\ \ge\ \operatorname{Tr}\exp(n\log A+m\log B).$$

## Results

| Statement | Status | Where |
|---|---|---|
| **Upper half:** $\operatorname{Tr}(A^nB^m)\ge p_{n,m}(A,B)$ | **False.** Counterexample of H. Cha and J. Lee (arXiv:2603.19927): 3 × 3, n = m = 5. | not ours |
| **Pinching inequality** (T. H. Dinh's Conjecture 5.1, arXiv:2605.17782): $p_{n,m}(A,B)\ge\operatorname{Tr}(A^nE_A(B)^m)$ for A, B ≥ 0 and **all** n, m, where $E_A(B)$ is the pinching of B onto the eigenspaces of A. Strict iff AB ≠ BA (m ≥ 2). | **Proved here.** Dinh had proved m = 2. | [`math/01-pinching-theorem.md`](math/01-pinching-theorem.md), Theorems 1–2 |
| **Exact gap identity:** $p_{n,m}(A,B)-\operatorname{Tr}(A^nE_A(B)^m)=m(m-1)\iint s^{m-2}\tau^n\rho(s,\tau)\,ds\,d\tau$, with an explicit density ρ ≥ 0 | **Proved here** | same note, Theorem 1 |
| **Corrected upper bound:** $p_{n,m}\le\operatorname{Tr}(A^nE_A(B)^m)+m(m-1)\|B\|^{m-2}S_n$, with a matching lower bound (equality for m = 2) | **Proved here** | same note, Theorem 3 |
| Variants: indefinite letters under sign conditions; a Jensen form for functions convex in the B-variable; for fixed m, $n\mapsto p_{n,m}$ is the moment sequence of an explicit positive measure | **Proved here** | same note, Theorems 4–6 |
| The identity behind all of this: the pinched two-variable BMV identity (Theorem A) | **Proved** (full proof). The generic case is Heinävaara's explicit BMV measure; the general-multiplicity form was stated in our OQP 27 paper | [`math/02-theorem-A.md`](math/02-theorem-A.md) |
| **Lower half:** $p_{n,m}(A,B)\ge\operatorname{Tr}\exp(n\log A+m\log B)$ | **Open.** Proved when min(n, m) ≤ 2. A stronger form, $p_{n,m}\ge\operatorname{Tr}(A^{n/m}B)^m$, is proved for rank-one B. No counterexample in extensive searches. | [`math/03-lower-half.md`](math/03-lower-half.md) |

### In words

- **The upper half.** The upper half of OQP 40 is false, but its natural repair holds for every word length.
  - The commuting part of the word average is not the clustered word $A^nB^m$. It is the pinched term
    $\operatorname{Tr}(A^nE_A(B)^m)$.
  - The excess over it is an explicit integral of a nonnegative density.
  - The excess is bounded above and below by explicit multiples of the two-letter excess.
- **The lower half.** It is still open. Any proof must be at least as strong as Stahl's theorem (the former BMV
  conjecture), because the lower half implies $p_{n,m}>0$.

## Verification

**Independent check.** An independent check of the pinching theorem, with code written from scratch in exact rational
and ball arithmetic, found **no errors**. See [`independent-check/REPORT.md`](independent-check/REPORT.md); its scripts
and logs are in `independent-check/scripts/`. Its results:
- Theorem 1 is confirmed exactly for d = 2.
- It is confirmed to 28–39 significant digits for d = 3, 4.
- It is confirmed to 26 digits on the Cha–Lee pair.
- About 27,000 exact cases and an adversarial search found no violation.

**Our own checks.**

```bash
pip install numpy scipy mpmath sympy python-flint
python code/verify_pinching.py          # Theorems 1-4: 40,500 + 7,500 cases, and quadrature of the gap identity
python code/chalee_family.py            # Cha-Lee family: lower half, doubling counterexample, pinched bound
python code/oqp40_second_order.py       # near-commuting expansion of the lower half
```

The GPU searches (`code/oqp40_torch.py`, `code/negword_search.py`, `code/oqp40_aux.py`) need PyTorch. All logs of our
runs are in `logs/`.

## Credits

- **The problem:** D. Hägele (communicated by R. F. Werner), IQOQI Vienna Open Quantum Problems, Problem 40.
- **The counterexample to the upper half:** H. Cha and J. Lee, arXiv:2603.19927 (2026).
- **The pinching conjecture and its m = 2 case:** T. H. Dinh, arXiv:2605.17782 (2026).
- **Stahl's theorem and its explicit atoms/density structure:** H. R. Stahl, Acta Math. 211 (2013) 255–290.
- **The explicit |Im|-density for simple spectrum:** O. Heinävaara, *Tracial joint spectral measures*, PhD thesis,
  Princeton (2024); see also Invent. Math. 239 (2025).
- **The high-frequency averaging lemma** is a special case of D. Burgarth, P. Facchi, H. Nakazato, S. Pascazio,
  K. Yuasa, Quantum 3, 152 (2019).
- **Equivalent forms of BMV:** E. H. Lieb and R. Seiringer, J. Stat. Phys. 115 (2004).
- **Words with negative trace:** C. R. Johnson and C. J. Hillar, SIAM J. Matrix Anal. Appl. 23 (2002); F. Garbe and
  F. Wei, arXiv:2605.02314.

## Citation

See [`CITATION.cff`](CITATION.cff).
