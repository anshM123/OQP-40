> **How to read this report (added for publication).** This is the independent check written against our working
> draft, before the draft was turned into the documents of this repository. Names used below:
> - `DINH.md` is the draft of [`../math/01-pinching-theorem.md`](../math/01-pinching-theorem.md). Its results
>   D1–D6 are Theorems 1–6 there.
> - `THEOREMS.md` ("Theorem A") is the working note now published as
>   [`../math/02-theorem-A.md`](../math/02-theorem-A.md).
> - `CHECK_REPORT.md` (an earlier independent check of Theorem A) and `LIT.md` (a literature survey) are internal working
>   notes, not included here.
> - `verify_dinh.py` is [`../code/verify_pinching.py`](../code/verify_pinching.py), and `check/` is the folder
>   [`scripts/`](scripts/).
>
> All suggested edits in Section 7 were made before publication.

# Independent check of DINH.md: Dinh's pinching conjecture for all word lengths

Checked 2026-10-08 against `DINH.md` as it stood on that date, together with `../THEOREMS.md` (Theorem A),
`../CHECK_REPORT.md` and `../LIT.md`.

Method:
- every step of Section 3 of DINH.md re-derived by hand;
- the statement compared with the arXiv text of Dinh's paper and of Cha–Lee;
- new numerical code written from scratch in `check/` (`verify_dinh.py` was read only for comparison), with exact
  rational arithmetic (python-flint) and 160-bit ball arithmetic (arb);
- a priority search on 2026-10-08.

Logs are next to the scripts in `check/`.

## 1. Verdict

**NO ERRORS FOUND.**

- Every step of Section 3 is correct as written, given Theorem A of `../THEOREMS.md`. No GAP affects any stated result.
- The statement of Conjecture 5.1 in DINH.md matches Dinh's paper exactly (Section 3 below).
- The exact gap identity D1 was confirmed independently of the authors' code:
  - **exactly** (rational arithmetic) for d = 2, against a closed form of rho derived for this check (in s, rho is a
    semicircle density); 14,400 identities over two seeds, 0 mismatches;
  - to **28–39 significant digits** for d = 3 and d = 4 by arbitrary-precision quadrature of rho, in 8 configurations:
    repeated and zero eigenvalues of A, a projection A, rank-one B, complex Hermitian B, indefinite A and B;
  - on the Cha–Lee pair at x = 1/1000 to 26 digits (at (n,m) = (5,5) the agreement is 9.8e-33 relative), and at
    x = 1/10^6 to 19 digits.
- D2 (the conjecture), the strictness clause, D3 (including the m = 2 equality with Dinh's Prop. 6.1), D4 and D5 were
  tested in exact arithmetic on about 27,000 (pair, n, m) cases and by adversarial optimisation; nothing failed.
- On the whole Cha–Lee family, every gap polynomial gap_{n,m}(x), 0 <= n, m <= 12, has positive lowest coefficient
  and no root in (0, oo) (rigorous root isolation). This proves the conjecture on the family for these (n, m) and all
  x > 0, x != 1/2. At x = 1/2, A_x has a double eigenvalue and the pinching is coarser; that point was checked
  separately for n, m <= 10.

**Most serious issue: MINOR (wording, issue 1 below).** The "measure language" reading of D5 speaks of a "convex
order" between joint moment functionals. For a non-commuting pair the word-average functional is not a positive
functional, so it has no representing measure. An exact certificate is in issue 1. D5 itself is correct.

**Priority.** No earlier or later proof of Dinh's Conjecture 5.1 for m >= 3 was found.
- The result is not stated in Stahl (2013), in Heinävaara's thesis (2024) or Inventiones paper (arXiv v1), or in
  Cha–Lee v1–v6.
- It is a short corollary (about one page) of the explicit BMV density written in the proof of Theorem 24(1) of
  Heinävaara's 2024 PhD thesis. This is exactly DINH.md's "alternative route". I checked it against the thesis text
  (Section 5).
- It is not an immediate consequence of Stahl's theorem alone. It does not follow from convexity either: B ->
  A_{n,m}(A,B) is not convex on PSD matrices (exact witnesses in Section 6).

## 2. Issues, most severe first

| # | Severity | Where in DINH.md | Issue |
|---|---|---|---|
| 1 | MINOR (wording) | D5, "How to read D5", "In measure language ..." | the word-average functional is not a positive functional, so "convex order" is used for linear functionals, not measures |
| 2 | MINOR (scope) | D5, second special case | f = e^{as - t tau} is not a polynomial, and D5 is stated for polynomials |
| 3 | MINOR (removable caveat) | Section 3, "Alternative route" | "the thesis formula ... was not available to us": it is, and it matches |
| 4 | COSMETIC | Sections 2–3 | the letter m is overloaded; rho on the lines tau in spec A is left undefined in Section 2 |
| 5 | REMARK | D3 | a shorter proof exists; the lower bound is 0 whenever B is singular |
| 6 | REMARK | Section 4, "honest framing" | accurate; could add that a convexity argument cannot replace the BMV density |

**1. MINOR. D5 "measure language".**
- DINH.md says: "the symmetrised (tracial) joint moment functional of (A,B) dominates that of (A, E_A(B)) in the convex
  order along the B-axis". Here the functional is L_{A,B}(tau^n s^m) := A_{n,m}(A,B).
- For a commuting pair, L is integration against the joint spectral measure. For a non-commuting pair it is not even
  positive on squares.
- Exact certificate (`check/c6_moment_matrix.log`): A = [[2,-1],[-1,1]], B = [[1,1],[1,5]], and p(tau,s) with the
  rational coefficients listed in the log, of bidegree (2,2). Then L_{A,B}(p^2) = -2.9165 < 0.
- So "convex order" can only mean L_{A,B}(f) >= L_{A,E_A(B)}(f) for f convex in s on the rectangle. That is exactly D5
  and it is correct.
- Suggested wording: "the linear functional f -> T_f(A,B) dominates f -> Tr f(A, E_A(B)) on functions convex in s;
  note that T_f(A,B) is not given by a positive measure when AB != BA."
- Theorem A says the same thing structurally: L_{A,B} = nu + d^2/ds^2 rho, where nu is the positive pinched joint
  spectral measure. The second term is a signed distribution.
- This does not contradict Heinävaara. His positive measure mu_{A,B} has moments
  s_{n,m}/((n+m)(n+m+1)) (thesis Sec. 1.3), that is, the word averages reweighted by total degree. L itself is not
  positive.

**2. MINOR. D5, special case f = e^{as - t tau}.**
- D5 is stated for polynomials. The exponential case is Theorem A itself; it does not follow from the polynomial case
  as stated.
- Fix: either say "by (*) directly", or extend D5 to power series converging on a neighbourhood of
  K = [l_min, l_max] x [alpha_1, alpha_r]. The extension uses the same termwise argument as Step 1.

**3. MINOR. "Alternative route": the thesis formula is available.**
- I read the thesis: O. Heinaevaara, *Tracial joint spectral measures*, Princeton 2024, author's copy at
  its.caltech.edu/~oeh/thesis_final.pdf, Section 1.4, Theorem 24 (p. 40) and the proof of part 1 (pp. 40–43; the
  formula is on p. 42).
- **Assumption.** The formula is derived for B (= DINH's A) with pairwise distinct eigenvalues ("by approximation").
- **The pencil-roots condition.** The proof's extra assumption that "the roots of (A,B) are pairwise distinct" is shown
  there to be equivalent to that, after the reduction to positive definite A. The words "and the pencil roots are
  distinct" in DINH.md are therefore redundant.
- **The formula** is
  tr exp(A - tB) = sum_{v in E(B)} exp(<Av,v>/<v,v> - t<Bv,v>/<v,v>)
                   + (1/2pi) int int e^{a - bt} sum_i |Im lambda_i((aI - A)(bI - B)^{-1})| da db,
  for Hermitian A after the thesis's scaling and translation step. This is exactly what `../LIT.md` §1.1 transcribes.
- **Agreement with rho.** The eigenvalues of (s - g)(tau - P)^{-1} are the roots xi of det(g - s - xi(P - tau)), so this
  is rho_{g,P} with (g, P) = (B, A).
- So the caveat "which was not available to us beyond what ../LIT.md reports" can be dropped. The alternative route is
  complete for the inequality D2.

**4. COSMETIC.**
- The letter m means the exponent and also the step function m(tau). In THEOREMS.md it also means the number of
  distinct eigenvalues of P. Suggest M(tau) or mu(tau) for the marginal.
- Section 2 defines rho through the roots of det(B - s - xi(A - tau)) without saying "for tau not in spec A, and
  rho := 0 on that null set". This is inherited from Theorem A and harmless.

**5. REMARK (D3).**
- D3 does not need the slice formula. D1 at m = 2 together with Dinh's (6.4) gives int int tau^n rho = S_n directly.
- For singular B the lower bound is 0, so D3 says nothing more than D2 there. This is correct as stated.

**6. REMARK (framing).** Section 4 of DINH.md describes novelty accurately. It could add one point: the inequality is
not a soft consequence of convexity, since B -> A_{n,m}(A,B) is not convex on PSD matrices (Section 6, `c7`). The
positivity of the explicit BMV density is really used.

## 3. Statement check against the paper (task item 1)

Source: arXiv:2605.17782v1 (18 May 2026; still the only version on 2026-10-08), HTML and abstract pages.

| Item | Dinh | DINH.md | Match |
|---|---|---|---|
| Word average | eq. (1.1): A_{n,m}(A,B) = C(n+m,n)^{-1} sum_{W in W_{n,m}} Tr W(A,B), unnormalised Tr; C(n+m,n) A_{n,m} = [t^m] Tr(A+tB)^{n+m} | same | yes |
| Pinching | eq. (1.3): A = sum_lambda lambda P_lambda, E_A(B) = sum_lambda P_lambda B P_lambda; A_{n,m}(A,E_A(B)) = Tr(A^n E_A(B)^m) (eq. 2.3) | same | yes |
| Conjecture 5.1 | A, B >= 0 (PSD), all n, m >= 0, non-strict: (5.1) A_{n,m}(A,B) >= A_{n,m}(A,E_A(B)), (5.2) A_{n,m}(A,B) >= Tr(A^n E_A(B)^m) | same; (5.1) and (5.2) are one statement | yes |
| What Dinh proves | Prop. 6.1, m = 2 only: A_{n,2}(A,E_A(B)) <= A_{n,2}(A,B) <= Tr(A^n B^2), gap (6.4) = (1/(n+1)) sum_{a_i != a_j} h_n(a_i,a_j) abs(b_ij)^2 with h_n(x,y) = sum_{r=0}^n x^r y^{n-r} | "only m = 2" | yes |
| m >= 3 | Sec. 7: "closed cycles" b_ij b_jl b_li; general case needs control of "cyclic phase contributions"; no proof | same | yes |
| Refined BMV | eq. (1.2); OQP 40 = formal-conjectures #3457 (statement due to D. Hägele, communicated by R. F. Werner; open, no comments) | same | yes |

- D3 at m = 2 equals Dinh's (6.4). With w_jk = ||Q_j B Q_k||_F^2, the ordered sum over a_i != a_j counts each block pair
  twice and h_n = (n+1) hbar_n, so the gap is 2 S_n. This was confirmed in exact arithmetic ([E2], 0 failures).
- Dinh's Section 4 was reproduced exactly ([C1], [C2]). Its formulas are (4.1) A_x = 1 (+) xC, B_x = xC (+) 1 (also
  Cha–Lee Sec. II), (4.2), (4.3), (4.5) and (4.7) = Cha–Lee's R(x), and the decimals (4.4) and (4.8) at x = 1e-3.

## 4. Re-derivation of Section 3 (task item 2)

**Step 0 (any Hermitian P).** Write P = cP' + beta with c = p_r - p_1 > 0 and beta = p_1, so spec P' is in [0,1].
- Theorem A for (g, P') gives Tr e^{ag - t'P'} - Tr e^{a g_d - t'P'} = a^2 int int e^{as - t' tau'} rho_{g,P'}.
- Put t' = ct and multiply by e^{-t beta}. The left side becomes the identity for P, because the pinching is unchanged.
- On the right, substitute tau = c tau' + beta, so dtau' = dtau / c.
- The roots scale correctly: det(g - s - xi(P - tau)) = det(g - s - (c xi)(P' - tau')), so
  rho_{g,P}(s,tau) = rho_{g,P'}(s,tau')/c.
- Hence (*) holds, and so do the support statement, the slice formula m(tau) = sum_{j<k} w_jk/(p_k - p_j)
  1[p_j < tau < p_k], and the total mass sum_{j<k} w_jk = ||g - g_d||_F^2 / 2.
- The scalar case is trivial: all roots (mu - s)/(p - tau) are real.
- **Correct.**

**Support.** Suppose Im xi != 0, with (g - s)v = xi(P - tau)v.
- Both <v,(g-s)v> and <v,(P-tau)v> are real, so both vanish.
- If s <= l_min or s >= l_max, then g - s is semidefinite, so (g - s)v = 0 and then (P - tau)v = 0, which is impossible
  for tau not in spec P.
- If tau < p_1 or tau > p_r, then P - tau is definite, which is impossible.
- **Correct.**

**Step 1 (coefficients).**
- (aB - tA)^N = sum over words. The coefficient of a^m (-t)^n is (n+m)!^{-1} sum_{W in W_{n,m}} Tr W(A,B)
  = C(n+m,n) A_{n,m} / (n+m)! = A_{n,m}/(n! m!).
- The pinched side gives Tr(A^n E^m)/(n! m!).
- On the right, a^2 e^{as - t tau} contributes s^{m-2} tau^n / ((m-2)! n!).
- Multiplying by n! m! gives the factor m!/(m-2)! = m(m-1).
- **Correct.**

**Termwise integration.**
- On K, the series sum |a s|^j |t tau|^k/(j! k!) = e^{|a||s| + |t||tau|} is bounded, and rho is in L^1.
- Dominated convergence therefore gives an entire right-hand side and the termwise Taylor coefficients.
- **Correct.**

**Positivity and strictness.**
- The total mass ||B - E_A(B)||_F^2 / 2 is exactly what Theorem A states, with g = B and g_d = E_A(B).
- My quadrature reproduces the slice formula int rho ds = m(tau) at every tau node, to 1e-26 ... 1e-38.
- B = E_A(B) iff B is block diagonal for the eigenspaces of A, iff AB = BA.
- On supp rho, the weight s^{m-2} tau^n (0^0 = 1) vanishes only on {s = 0} or {tau = 0}. These are Lebesgue-null.
  rho is an L^1 function (Theorem A, Step 4: no singular part on the lines).
- So the integral is > 0 iff rho is not 0 a.e., iff AB != BA. This holds for every n >= 0 and m >= 2, including
  singular A, singular B and rank-one B.
- Example: A = diag(0,1), B = [[1,1],[1,1]]. The d = 2 formula below gives gap(n,3) = 6/(n+1) > 0.
- Exact test [E2]: strictness iff non-commuting held in all 8,190 cases, including singular A, rank-one B, both
  singular, and scalar A (gap = 0 exactly).
- **Correct.**

**A closed form for d = 2 (derived for this check).** Work in the eigenbasis of A = diag(a1, a2), a1 < a2, with
B = [[b11, b],[conj b, b22]], and fix a1 < tau < a2.
- Put u = tau - a1 and v = a2 - tau. Then det(B - s - xi(A - tau)) = (b11 - s + xi u)(b22 - s - xi v) - |b|^2.
- Its discriminant in xi is (u+v)^2 (c - s)^2 - 4uv|b|^2, with c(tau) = (b11 (a2 - tau) + b22 (tau - a1))/(a2 - a1).
- Hence rho(., tau) is |b|^2/(a2 - a1) times the semicircle probability density with centre c(tau) and radius
  R(tau) = 2 sqrt(uv)|b|/(a2 - a1).
- So int int s^k tau^n rho = |b|^2/(a2-a1) int tau^n sum_j C(k,2j) Cat_j c(tau)^{k-2j} (R^2/4)^j dtau, a rational
  number for rational data.
- D1 then becomes an exact rational identity. It held in all 7,200 tested instances ([E1]: real and complex, PSD and
  indefinite, singular A, rank-one B).

**D3.**
- On supp rho, 0 <= l_min <= s <= l_max, so l_min^{m-2} <= s^{m-2} <= l_max^{m-2}.
- int int tau^n rho = int tau^n m(tau) dtau = sum_{j<k} w_jk hbar_n(alpha_j, alpha_k) = S_n.
- **Correct.** At m = 2 it is Dinh's (6.4); see issue 5.

**D4.**
- If n and m are both even, s^{m-2} >= 0 and tau^n >= 0 everywhere.
- If A >= 0, then tau >= 0 on the support; if B >= 0, then s >= 0 on the support.
- **Correct.**
- The sign conditions are needed: (n,m) = (1,3) with both letters indefinite fails in 19/40 exact cases.
  A >= 0 with B indefinite and m odd >= 3 fails in 419/800 ([E3]).

**D5.** Linearity in f together with d^2/ds^2 (tau^n s^m) = m(m-1) tau^n s^{m-2} gives the identity. The inequality
follows from rho >= 0 and the support. **Correct.** See issues 1 and 2 for the wording.

**Swapping the letters.** A_{m,n}(B,A) = A_{n,m}(A,B). Apply D1 to (B, A, m, n). **Correct.**

**Alternative route.**
- Rescaling g -> a g: the roots of det(ag - as - xi(P - tau)) are a times those for g. So rho_{ag,P}(as,tau) =
  |a| rho_{g,P}(s,tau), and ds' = |a| ds, which gives the factor a^2.
- E_{A_eps}(B) = E_A(B) is **true**:
  - In ran Q_k, take an orthonormal eigenbasis (v_{k,i}) of Q_k B Q_k and distinct d_{k,i} > 0. Put
    D = sum d_{k,i} v_{k,i} v_{k,i}^*.
  - For 0 < eps < min_{j != k} |alpha_j - alpha_k| / (2 max d), the eigenvalues alpha_k + eps d_{k,i} of A + eps D are
    pairwise distinct. So E_{A_eps}(B) = sum_{k,i} <v_{k,i}, B v_{k,i}> v_{k,i} v_{k,i}^*.
  - Since Q_k B Q_k is diagonal in (v_{k,i}), this sum equals sum_k Q_k B Q_k = E_A(B).
  - If Q_k B Q_k has a repeated eigenvalue, any eigenbasis works.
  - A + eps D >= 0 when A >= 0.
- Both sides of D2 are polynomials in eps, so the inequality passes to the limit.
- **Correct.** The route gives D2 (non-strict) for all A, B >= 0 from the thesis alone, independently of Theorem A.

**Dependence on Theorem A.**
- D1, D3, D5 and the strictness clause need Theorem A for general multiplicities. D2 alone does not: the alternative
  route gives it from the thesis.
- Theorem A was not re-proved here; `../CHECK_REPORT.md` covers it. Independently of that report, the quadrature runs
  confirm its full moment content to about 30 digits in cases with repeated eigenvalues of A (cases 1, 2, 4, 6). These
  are the cases the thesis does not cover.
- Extra singular mass on the lines tau in spec A, beyond the pinching, would have to have all 66 tested moments equal
  to 0 to go unnoticed. So Step 4 of Theorem A ("no singular part on the lines") is supported numerically as well.

## 5. Priority (task item 4)

**Searches, 2026-10-08:**
- arXiv API, all abstracts with "BMV" or "Bessis-Moussa-Villani", newest first. The only 2026 matrix papers are
  Cha–Lee (2603.19927, v1–v6), Garbe–Wei 2605.02314 (positivity of individual words) and Dinh 2605.17782.
  Pradhan–Skripka 2512.05587 (infinite-dimensional BMV) is from 2025. None addresses pinching.
- arXiv author listings: Heinävaara (latest: 2602.10373, *Convolution comparison measures*) and H. Cha (latest
  2609.22176, unrelated). Nothing on Dinh's conjecture.
- Citations:
  - Semantic Scholar lists **0 citations** of 2605.17782.
  - Google Scholar returns only the paper itself.
  - The Pith page has no follow-ups.
  - formal-conjectures #3457 has no comments, and there is no OQP-40 Lean file in the repository.
- The 12 Semantic Scholar citers of Heinävaara's Inventiones paper were screened. Cha–Lee cite it only as a reference
  for the trace-exponential form of BMV, with no pinching or lower bound. The abstracts of the other citers do not
  touch word averages or pinching.
- The `openai/math` CONTENTS.md index (638 kB), searched with grep: no BMV, Stahl, pinching or word-average entries.
  The only hit is "Villani's conjecture", which is optimal transport and unrelated.

**Verdict on novelty and "immediate consequence":**
- **Stahl 2013 (Acta Math.).** Not immediate. Stahl gives, for each fixed a, a positive density in tau. The conjecture
  needs joint positivity in (s, tau), namely that this density is a^2 times the Laplace transform in s of a positive
  function. Stahl's contour-integral density does not display this.
- **Heinävaara, Invent. Math. 239 (2025), arXiv:2310.03227 v1.**
  - Not immediate from what is on arXiv. The tracial joint spectral measure gives word averages as moments,
    s_{k,l}(A,B) = (k+l)(k+l+1) int a^k b^l dmu_{A,B} (thesis Sec. 1.3). With positivity this gives the
    Lieb–Seiringer form of BMV.
  - But the measures of (A,B) and (A,E_A(B)) have different singular parts, and nothing there compares them.
  - The published version is closed access (Springer redirect) and was **not checked**. If it reproduces the thesis's
    Sec. 1.4 formula, the remark below applies to a peer-reviewed source.
- **Heinävaara, PhD thesis (Princeton 2024).**
  - The conjecture is a short corollary of the explicit density in the proof of Thm 24(1), via rescaling, the support
    property, coefficient extraction and perturbation inside eigenspaces. This is DINH.md's alternative route; all of
    it was checked here.
  - The thesis itself does not mention pinching, compressions or the comparison with E_A(B).
- **Conclusion.** The written statement and proof for m >= 3 appear new. As DINH.md says, the mathematical content is a
  direct consequence of the explicit Stahl–Heinävaara density. The "honest framing" paragraph of DINH.md §4 is accurate
  and should be kept.

## 6. Numerical evidence (task item 3)

Run with the project venv, OMP_NUM_THREADS=2, at most 3 processes. All logs are in `check/`.

| Script / log | What it tests | Result |
|---|---|---|
| `c1_exact.py` / `c1_exact.log` (seed 12345), `c1_exact_seed2026.log` | [E0] word recursion vs brute-force enumeration; [E1] D1 for d = 2, exact, against the semicircle closed form; [E2] D2, strictness, D3, m = 2 equality, exact (D3 bounds with 60-digit l_min/l_max); [E3] D4 exact | Per seed, identical for both seeds: [E0] 0 mismatches. [E1] 7,200 identities, 0 mismatches. [E2] 8,190 cases with d = 2..5, real and complex, in the structures generic, singular A, rank-one B, repeated eigenvalue, scalar A, and singular A and B: 0 negative gaps, 0 strictness failures, 0 m = 2 failures, 0 D3 failures. [E3] 0 failures under the sign conditions; without them, failures in 419/800 and 19/40 (seed 2026: 463/800, 20/40) |
| `c2_quad_D1.py` / `c2_quad_D1_part1.log`, `c2_quad_D1_part2.log`, `c2_quad_D1_case5.log` | D1 for d = 3, 4, all 66 pairs (n,m) with 2 <= m, n + m <= 12. Exact rational left side; right side by nested composite Gauss–Legendre in 160-bit arb arithmetic, with breakpoints at the real roots of the xi-discriminant and graded meshes around its complex roots. Also the slice formula at every tau node | Worst relative error over the 66 pairs at N = 48 (N = 24 in brackets) |
| | case 0: d = 3, A = diag(0, 1/2, 1) singular, B PSD | 4.0e-30 (3.7e-17); slice 1.9e-28 |
| | case 1: d = 3, A = diag(0,1,1) (repeated and zero eigenvalue) | 1.9e-30 (8.3e-18) |
| | case 2: d = 3, A = diag(1/4,1/4,1), rank-one B | 3.1e-39 (1.1e-23) |
| | case 3: d = 3, indefinite A and B (Hermitian D1) | 8.7e-29 (2.5e-16) |
| | case 4: d = 4, A = diag(0,1/3,1/3,1), rank-3 B | 1.7e-28 (5.0e-16) |
| | case 5: d = 3, complex Hermitian B (in `c2_quad_D1_case5.log`; the case-5 traceback in part2.log is a rational-conversion bug in the script, fixed before the rerun) | 3.6e-28 (3.7e-16) |
| | case 6: d = 4, projection A = diag(0,0,1,1) | 2.5e-31 (2.8e-20) |
| | case 7: d = 4, A = diag(0,1/4,3/5,1) | 2.9e-29 (2.2e-17) |
| `c3_cha_lee.py` / `c3_cha_lee.log` | Cha–Lee / Dinh Sec. 4 family, exact polynomials in x | [C1] Dinh (4.3), (4.5), (4.7) = Cha–Lee R(x): all exact identities hold. gap_55(x) = 5/126 x^4 + 65/7 x^5 + ... + 1585/42 x^10, all coefficients positive. [C2] at x = 1e-3: A_55 = 5.0981572499e-14, Tr(A^5 E^5) = 2.0050100100e-15, gap = 4.8976562489e-14 (as in Dinh 4.4, 4.8). Also at 1e-6, 1e-9, 1e-12, 1e-15 (gap ~ (5/126) x^4 > 0). [C3] all 169 polynomials gap_{n,m}(x), 0 <= n,m <= 12: positive lowest coefficient, no root in (0, oo) (exact isolation); D3 on 0 < x < 1/2 exact. [C4] x = 1/2, where A_x has a double eigenvalue and the pinching is coarser: min gap 2.19e-3 > 0. [C5] D1 by quadrature at x = 1/1000: 4.0e-26 over 0 <= n <= 8, 2 <= m <= 8; (5,5): 9.8e-33. At x = 1/10^6: 3.4e-19, where gap_55 = 3.969e-26 and the quadrature agrees to 2.6e-19 relative |
| `c4_adversary.py` / `c4_adversary_s1.log` ... `c4_adversary_s4.log` | Adversarial minimisation (Nelder–Mead then Powell) over PSD pairs, d = 2..5, (n,m) in {(1,3),(2,3),(3,3),(0,3),(2,4),(3,5),(5,5),(4,6),(6,3),(1,7),(8,4)}. Modes: generic, near-degenerate A (gap 1e-10 ... 1e-3, fine pinching), exactly degenerate A (coarse pinching), singular A, low-rank B. Objectives: gap/‖B-E‖_F^2, gap/(D3 lower) - 1, 1 - gap/(D3 upper). Best points re-evaluated in 50 digits, with U = expm(H) and B = ZZ* rebuilt in 50 digits | 2,494 rounds over 4 seeds (774, 650, 536, 534), **no violation**. 286 rounds ended with a negative double-precision objective. All of them were near-commuting configurations (‖B-E‖_F^2 ~ 1e-14, gap ~ 1e-15), where double precision is meaningless. Seeds 1–2 re-checked the 15 worst each, and seeds 3–4 re-checked every one (64 + 49). All 143 re-checked are positive in 50 digits (smallest 1.5e-22). Smallest 50-digit values of the best points: gap/‖B-E‖^2 = 6.1e-19 (A nearly singular, so tau^n is tiny on supp rho); gap/(D3 lower) - 1 = 1.7e-6 and 1 - gap/(D3 upper) = 1.4e-6 (B close to a multiple of I, where the two D3 bounds meet). Where E_A jumps, all values stay positive. Exactly degenerate A (coarse pinching): smallest 2.7e-7 (gap_norm), 4.9e-5 (D3 lower), 1.2e-4 (D3 upper). Near-degenerate A (fine pinching, eigenvalue gaps down to 1e-10): smallest 4.5e-17 (gap_norm), 1.7e-5 (D3 lower), 1.2e-4 (D3 upper) |
| `c5_exact_more.py` / `c5_exact_more.log` (seed 777), `c5_exact_more_seed4242.log` | [F1] D5 exact, random polynomials convex in s on a rational rectangle containing K, but not convex outside it; [F2] sharpness; [F3] near-degenerate A, exact; [F4] long words and d = 6 | [F1] 48 + 54 cases (PSD and Hermitian letters, repeated eigenvalues). f was negative somewhere on R in 32 + 38, non-monotone in s on R in 26 + 25, and not convex in s outside R in 45 + 49. 0 violations; min relative excess 2.2e-4. [F2] f = tau^n (s - s*)^5/20 (convex only for s > s*): T_f < Tr f(A,E_A(B)) in 97/200 and 108/200, so the full-range convexity hypothesis is needed. [F3] eigenvalue gaps 1e-2 ... 1e-12 of A: 2 x 1,485 cases, 0 failures of gap > 0 or of D3 (60 digits). [F4] d = 3, all 29 pairs with n + m = 30, m >= 2: all gaps > 0; d = 6 with A multiplicities (3,2,1) and rank-2 B, n + m <= 14: all 91 gaps > 0 (both seeds) |
| `c6_moment_matrix.py` / `c6_moment_matrix.log` | is (n,m) -> A_{n,m}(A,B) a positive moment functional? | No: exact L(p^2) = -2.9165 for A = [[2,-1],[-1,1]], B = [[1,1],[1,5]] (issue 1) |
| `c7_convexity_route.py` / `c7_convexity_route.log` | is B -> A_{n,m}(A,B) convex on PSD matrices (which would give a trivial proof)? | No, for every (n,m) tested: e.g. (1,3), A = [[2,-3],[-3,5]], B = [[1,0],[0,0]], H = [[-6,-5],[-5,-6]] gives the e^2-coefficient -99 (exact). Negative Hessians in 9–27 of 2,000 random triples per (n,m). Along the pinching path E + e(B - E) no negative Hessian was found (0/2,000 per (n,m)); this is an observation, not a claim of DINH.md |

**Comparison with `verify_dinh.py`.**
- The authors' [4] checked D1 by trapezoid/Chebyshev quadrature to 5–6 digits, on 15 cases.
- The present check confirms D1 to 26–39 digits, and exactly for d = 2.
- Their D2/D3/D4 double-precision statistics are consistent with the exact results here.

## 7. Suggested edits to DINH.md (not made)

1. Reword the "measure language" bullet of D5 (issue 1). Optionally cite the certificate in `check/c6_moment_matrix.log`.
2. In D5's special cases, say that the exponential case is (*) itself, or extend D5 to power series (issue 2).
3. In the alternative route, drop "which was not available to us"; cite thesis pp. 40–43 (proof of Thm 24(1), formula
   on p. 42) and the distinct-eigenvalue assumption; drop "and the pencil roots are distinct" (issue 3).
4. Rename the marginal m(tau) (issue 4).
5. Status line: "Independent adversarial check: done (CHECK_DINH.md), no errors found."
