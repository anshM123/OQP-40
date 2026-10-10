# The lower half of OQP 40 whenever min(n, m) ≤ 3

Ansh Mishra, Aryan Senthilkumar. Status 2026-10-10: proved, computer-assisted and independently checked; not yet
reviewed by outside experts.

**Theorem 7.** For every n ≥ 1 and all positive definite matrices A, B of any size,
$$\mathcal A_{n,3}(A,B)\ \ge\ \operatorname{Tr}\big((A^{n/3}B)^3\big)\qquad\text{(Conjecture F at }(n,3)).$$
Hence the lower half of OQP 40, $p_{n,m}(A,B)\ge\operatorname{Tr}\exp(n\log A+m\log B)$, holds at (n, 3) and (3, n) for
every n. Together with the earlier case min(n, m) ≤ 2, **the lower half holds whenever min(n, m) ≤ 3.**

**Proof outline.**
- **n ≤ 36:** Theorem 5 of [`05-lower-half-m3.md`](05-lower-half-m3.md), an exact computation over the rationals for
  each n.
- **n ≥ 37:** Theorem B of [`../lower-half/m3-all-n/THEOREM.md`](../lower-half/m3-all-n/THEOREM.md).
  1. *A family of certificates* (Proposition 6'). In the apex-share certificate of
     [`04-lower-half-new-cases.md`](04-lower-half-new-cases.md), the largest point of each triple may take its cap times
     any positive semidefinite correlation R. This keeps every certificate matrix positive semidefinite except one
     kernel E^R(s, t) on (1, ∞).
  2. *Why a new R is needed.* For R = 1 (the certificate of note 05), the conditions that make E^R positive
     semidefinite hold as n → ∞ with a margin of only 1.35·10⁻⁴. That is too small for any proof that is uniform in n.
  3. *A Gaussian design.* With R(u, v) = exp(−(Φ(u) − Φ(v))²) for an explicit Φ (λ = 7/100, η = 7/10), the asymptotic
     margins become healthy: at least 0.06, 0.06 and 0.0034.
  4. *Verification.* E^R is positive semidefinite by Lemma 4 of note 04 (interval mixtures) as soon as F = E^R/(w w)
     satisfies F > 0, F_s ≥ 0, F_t ≤ 0 and F_st ≤ 0 on 1 < s < t.
     - These four conditions are verified in ball arithmetic (python-flint, Arb) for all n ≥ 37 at once, with
       eps = 1/n treated as an interval variable in [0, 1/37].
     - The verification uses closed forms that are analytic in eps, and charts for the regions s → 1, t → s, t → ∞,
       s → ∞ and the corner where s and t are both near 1.

**Checks.** [`../lower-half/m3-all-n/independent-check/CHECK_REPORT.md`](../lower-half/m3-all-n/independent-check/CHECK_REPORT.md).
- A second implementation, written separately, re-derives the mathematics and the closed forms. It re-verifies every
  region with its own code: 605,334 boxes, 0 failures. A script checks mechanically that the regions cover the whole
  domain.
- It found one real gap in the first implementation: an eps-expansion truncated at first order, which made 10 regions
  unjustified. Those regions were re-run with the correction and verified. The folder README lists which logs count.
- 8,000 random points with n from 37 to 10⁶ were checked against the definitions in high precision, and 966 certified
  bounds were checked against true values. No violation.

**What is not claimed.**
- No external review.
- Both implementations check the same sufficient conditions; the reduction to them was checked by hand.
- The lower half for min(n, m) ≥ 4 remains open, except for the cases (n, 4) and (4, n) of
  [`06-lower-half-m4.md`](06-lower-half-m4.md) and (4, 6), (6, 4). The open case with the fewest letters is (5, 5).
- The general lower half is at least as strong as Stahl's theorem (the former BMV conjecture).

**Priority.** As far as we found, before our work the lower half of OQP 40 was known only in special cases: n = m = 1,
commuting pairs, and 2 × 2 matrices (Furuichi, Kuriyama and Yanagi 2009). We found no earlier result for (n, 3) at
general n.
