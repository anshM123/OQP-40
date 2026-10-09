# The pinching inequality for word averages, for all word lengths

This note proves, for every number of letters, the "pinching correction" that T. H. Dinh proposed for the refined
Bessis–Moussa–Villani (BMV) conjecture, IQOQI Open Quantum Problem 40. Dinh proved the case m = 2.

**Attribution, up front.**
- The inequality (Theorem 2) follows in a few lines from a published theorem: O. Heinävaara, *Tracial joint spectral
  measures*, arXiv:2310.03227 (2023), Invent. Math. 239 (2025), **Corollary 1.2**. That corollary says the k-th
  derivative of t ↦ tr f(tA + B) is ≥ 0 when f⁽ᵏ⁾ ≥ 0 (A ≥ 0 for odd k).
- This short derivation is in Section 4.0. We did not find the consequence stated anywhere, including in Dinh's paper,
  which does not cite Heinävaara.
- What this note adds:
  - the **exact gap identity** with an explicit nonnegative density (Theorem 1), proved by coefficient comparison in an
    integral identity for traces of exponentials (Theorem A, [`02-theorem-A.md`](02-theorem-A.md));
  - the two-sided bound (Theorem 3), the sign-condition variants (Theorem 4) and the Jensen form (Theorem 5);
  - the explicit form of the fixed-m measure (Theorem 6), whose positivity is equivalent to Heinävaara's
    Corollary 1.2.

See Section 6 for credits.

## 1. Setting

Let A and B be Hermitian d × d matrices.

- **Word average.** For integers n, m ≥ 0, let $\mathcal W_{n,m}$ be the set of the $\binom{n+m}{n}$ words with
  n letters A and m letters B, and put

  $$\mathcal A_{n,m}(A,B)=\binom{n+m}{n}^{-1}\sum_{W\in\mathcal W_{n,m}}\operatorname{Tr}W(A,B).$$

  Equivalently, $\binom{n+m}{n}\mathcal A_{n,m}(A,B)$ is the coefficient of $t^m$ in $\operatorname{Tr}(A+tB)^{n+m}$.
  In OQP 40 this quantity is called $p_{n,m}$.
- **Spectral decomposition.** Write $A=\sum_{k=1}^r\alpha_kQ_k$ with distinct eigenvalues $\alpha_1<\dots<\alpha_r$
  and spectral projections $Q_k$.
- **Pinching.** $E_A(B)=\sum_kQ_kBQ_k$ is the pinching of B onto the eigenspaces of A. It is the part of B that
  commutes with A, so $\mathcal A_{n,m}(A,E_A(B))=\operatorname{Tr}(A^nE_A(B)^m)$.
- **Weights.** $w_{jk}=\|Q_jBQ_k\|_F^2$ for $j<k$, and
  $\bar h_n(x,y)=\frac{x^{n+1}-y^{n+1}}{(n+1)(x-y)}$, the mean of $\tau^n$ over the interval between x and y (with
  $\bar h_n(x,x)=x^n$).
- **The density.** For $s\in\mathbb R$ and $\tau\notin\operatorname{spec}A$, let $\xi_1,\dots,\xi_d$ be the roots
  of the polynomial $\xi\mapsto\det\bigl(B-s-\xi(A-\tau)\bigr)$, and put

  $$\rho(s,\tau)=\rho_{B,A}(s,\tau)=\frac1{2\pi}\sum_{i=1}^d|\operatorname{Im}\xi_i(s,\tau)|\ \ge0,$$

  with $\rho=0$ on the null set $\{\tau\in\operatorname{spec}A\}$. By Theorem A, $\rho$ is integrable and supported in
  $[\lambda_{\min}(B),\lambda_{\max}(B)]\times[\alpha_1,\alpha_r]$. Its $\tau$-marginal is the step function

  $$\int_{\mathbb R}\rho(s,\tau)\,ds=\mu(\tau):=\sum_{j<k}\frac{w_{jk}}{\alpha_k-\alpha_j}\,\mathbf 1[\alpha_j<\tau<\alpha_k].$$

**Dinh's Conjecture 5.1** (arXiv:2605.17782): for A, B ≥ 0 and all n, m ≥ 0,
$\mathcal A_{n,m}(A,B)\ge\mathcal A_{n,m}(A,E_A(B))=\operatorname{Tr}(A^nE_A(B)^m)$.
Dinh proves the case m = 2 (his Prop. 6.1). For m ≥ 3 he notes that "closed cycles appear" and that the general case
needs control of cyclic phase contributions.

## 2. Results

**Theorem 1 (exact gap identity).** For all Hermitian A, B and all n, m ≥ 0,

$$\mathcal A_{n,m}(A,B)-\operatorname{Tr}\bigl(A^nE_A(B)^m\bigr)=m(m-1)\iint s^{m-2}\,\tau^n\,\rho_{B,A}(s,\tau)\,ds\,d\tau .$$

For m ≤ 1 both sides vanish.

**Theorem 2 (Dinh's conjecture, all word lengths).** If A, B ≥ 0, then for all n, m ≥ 0

$$\mathcal A_{n,m}(A,B)\ \ge\ \operatorname{Tr}\bigl(A^nE_A(B)^m\bigr).$$

For m ≥ 2 the inequality is strict if and only if AB ≠ BA.

**Theorem 3 (two-sided bound).** If A, B ≥ 0 and m ≥ 2, then with $S_n=\sum_{j<k}w_{jk}\,\bar h_n(\alpha_j,\alpha_k)$,

$$m(m-1)\,\lambda_{\min}(B)^{m-2}\,S_n\ \le\ \mathcal A_{n,m}(A,B)-\operatorname{Tr}\bigl(A^nE_A(B)^m\bigr)\ \le\ m(m-1)\,\lambda_{\max}(B)^{m-2}\,S_n .$$

- For m = 2 both bounds are equalities. The common value 2S_n is Dinh's gap formula (his Prop. 6.1).
- In particular,
  $\mathcal A_{n,m}(A,B)\le\operatorname{Tr}(A^nE_A(B)^m)+m(m-1)\|B\|^{m-2}S_n$. This is a valid two-sided replacement
  for the upper half of OQP 40, which is false in general (Cha–Lee, arXiv:2603.19927).

**Theorem 4 (indefinite letters).** For Hermitian A, B the inequality of Theorem 2 holds:
- whenever n and m are both even;
- whenever A ≥ 0 and m is even;
- whenever B ≥ 0 and n is even.

Some sign condition is needed. For (n, m) = (1, 3) and random indefinite 3 × 3 pairs the inequality fails in about
half of the cases.

**Theorem 5 (Jensen form).** For a polynomial $f(\tau,s)=\sum c_{nm}\tau^ns^m$ put
$T_f(A,B)=\sum c_{nm}\mathcal A_{n,m}(A,B)$. Then

$$T_f(A,B)-\operatorname{Tr}f\bigl(A,E_A(B)\bigr)=\iint\frac{\partial^2f}{\partial s^2}(\tau,s)\,\rho_{B,A}(s,\tau)\,ds\,d\tau .$$

So $T_f(A,B)\ge\operatorname{Tr}f(A,E_A(B))$ whenever f is convex in s on
$[\alpha_1,\alpha_r]\times[\lambda_{\min}(B),\lambda_{\max}(B)]$. The same holds for power series converging near
that rectangle.

How to read Theorem 5:
- It is a noncommutative Jensen inequality with an explicit positive Peano kernel ρ.
- It is an order between **linear functionals**, not between measures. For AB ≠ BA the word-average functional
  $\tau^ns^m\mapsto\mathcal A_{n,m}(A,B)$ is not positive on squares, so no measure represents it.
  - Exact witness: A = [[2,−1],[−1,1]] and B = [[1,1],[1,5]], with a polynomial of bidegree (2,2) whose square has
    functional value −2.9165.

**Theorem 6 (fixed number of B's: a positive measure).** Let B ≥ 0 and fix m. Then $n\mapsto\mathcal A_{n,m}(A,B)$
is the moment sequence of the positive measure

$$\pi_m=\sum_{k=1}^r\operatorname{Tr}_{Q_k}(Q_kBQ_k)^m\,\delta_{\alpha_k}+m(m-1)\Bigl(\int s^{m-2}\rho_{B,A}(s,\tau)\,ds\Bigr)d\tau .$$

It has total mass $\operatorname{Tr}B^m$ and is supported in $[\alpha_1,\alpha_r]$. Equivalently, in an eigenbasis of A,

$$\pi_m=\sum_{i\in[d]^m}b_{i_1i_2}b_{i_2i_3}\cdots b_{i_mi_1}\,\mathrm{Law}\Bigl(\sum_ju_j\alpha_{i_j}\Bigr),\qquad u\sim\mathrm{Dirichlet}(1,\dots,1).$$

This "cycle expansion" has terms of both signs. Its positivity is not visible term by term.

The positivity of $\pi_m$ is equivalent to Heinävaara's Corollary 1.2 (see Section 4.0): for smooth G,
$\frac{d^m}{dy^m}\operatorname{Tr}G(A+yB)\big|_{y=0}=\int G^{(m)}\,d\pi_m$. What Theorem 6 adds is the explicit
decomposition into the pinched atoms and the density $m(m-1)\int s^{m-2}\rho\,ds$.

**Swapping the letters.** Pinching A onto the eigenspaces of B gives
$\mathcal A_{n,m}(A,B)-\operatorname{Tr}(E_B(A)^nB^m)=n(n-1)\iint s^{n-2}\tau^m\rho_{A,B}$. So for A, B ≥ 0 both pinched
quantities are lower bounds.

## 3. Proofs

**Step 0 (Theorem A for every Hermitian A).** [`02-theorem-A.md`](02-theorem-A.md) proves, for Hermitian g and P
and all $(a,t)\in\mathbb C^2$,

$$\operatorname{Tr}e^{ag-tP}-\operatorname{Tr}e^{ag_d-tP}=a^2\iint e^{as-t\tau}\rho_{g,P}(s,\tau)\,ds\,d\tau,\qquad g_d=E_P(g),\tag{$*$}$$

with $\rho_{g,P}\ge0$ integrable and supported in $[\lambda_{\min}(g),\lambda_{\max}(g)]\times[\min\operatorname{spec}P,\max\operatorname{spec}P]$.
The support statement has a one-line reason: if s lies outside $[\lambda_{\min}(g),\lambda_{\max}(g)]$, then g − s is
definite, and the pencil (g − s) − ξ(P − τ) has only real roots. The same holds when τ lies outside the spectral
interval of P.

**Step 1 (proof of Theorem 1: coefficient extraction).** Apply (∗) with (g, P) = (B, A).
- **Left side.** $\operatorname{Tr}e^{aB-tA}=\sum_N\frac1{N!}\operatorname{Tr}(aB-tA)^N$. Expanding $(aB-tA)^{n+m}$
  into words, the coefficient of $a^m(-t)^n$ is $\frac1{(n+m)!}\sum_{W\in\mathcal W_{n,m}}\operatorname{Tr}W(A,B)=\mathcal A_{n,m}(A,B)/(n!\,m!)$.
- **Pinched term.** The same computation with $E_A(B)$ gives $\operatorname{Tr}(A^nE_A(B)^m)/(n!\,m!)$.
- **Right side.**
  - ρ is integrable with compact support K. So $e^{as-t\tau}=\sum_{j,k}a^js^j(-t)^k\tau^k/(j!\,k!)$ converges
    absolutely and uniformly on K for $|a|,|t|\le R$.
  - The right side is therefore entire, and its Taylor coefficients may be computed term by term.
  - The coefficient of $a^m(-t)^n$ is $\iint s^{m-2}\tau^n\rho\,/((m-2)!\,n!)$ for m ≥ 2, and 0 for m ≤ 1.
- **Comparison.** Both sides are entire in (a, t). Comparing Taylor coefficients and multiplying by n! m! gives
  Theorem 1, since m!/(m − 2)! = m(m − 1).

**Step 2 (proof of Theorem 2).** Let A, B ≥ 0.
- On supp ρ we have $s\ge\lambda_{\min}(B)\ge0$ and $\tau\ge\alpha_1\ge0$. So $s^{m-2}\tau^n\ge0$ there (with
  $0^0=1$), and ρ ≥ 0. Hence the right side of Theorem 1 is ≥ 0.
- **Strictness for m ≥ 2.**
  - The total mass of ρ is $\sum_{j<k}w_{jk}=\|B-E_A(B)\|_F^2/2$ (Theorem A). It is positive iff B ≠ E_A(B), that
    is, iff AB ≠ BA.
  - $s^{m-2}\tau^n$ vanishes only on the null set $\{s=0\}\cup\{\tau=0\}$.
  - So the integral is positive iff AB ≠ BA.
- For m ≤ 1 both sides are equal.

**Step 3 (proof of Theorem 3).**
- On supp ρ, $\lambda_{\min}(B)^{m-2}\le s^{m-2}\le\lambda_{\max}(B)^{m-2}$.
- Integrate first in s, using $\int\rho(s,\tau)ds=\mu(\tau)$:

  $$\int\tau^n\mu(\tau)\,d\tau=\sum_{j<k}\frac{w_{jk}}{\alpha_k-\alpha_j}\int_{\alpha_j}^{\alpha_k}\tau^n\,d\tau=S_n .$$

- For m = 2, $s^0=1$, so the gap is exactly 2S_n.

**Step 4 (proof of Theorem 4).**
- If n and m are both even, $s^{m-2}\ge0$ and $\tau^n\ge0$ everywhere.
- Otherwise, use the support of ρ: if A ≥ 0 then τ ≥ 0 on it, and if B ≥ 0 then s ≥ 0 on it.

**Step 5 (proof of Theorem 5).** The statement is linear in f. The monomial case is Theorem 1, because
$\partial_s^2(\tau^ns^m)=m(m-1)\tau^ns^{m-2}$. For power series, use the term-by-term argument of Step 1.

**Step 6 (proof of Theorem 6).**
- Theorem 1 says $\mathcal A_{n,m}(A,B)=\int\tau^n\,d\pi_m$. The density of $\pi_m$ is ≥ 0 because s ≥ 0 on supp ρ.
- **Mass.** At n = 0, $\mathcal A_{0,m}=\operatorname{Tr}B^m$.
- **Cycle expansion.** Write each word, read cyclically from a B, as $BA^{N_1}\cdots BA^{N_m}$ with
  $N_1+\dots+N_m=n$. A uniformly random word gives a uniformly random composition N. Expanding in the eigenbasis of A,
  and averaging $\prod_jx_j^{N_j}$ over compositions, gives $h_n(x)/\binom{n+m-1}{n}=\mathbb E_u(\sum_ju_jx_j)^n$
  (Dirichlet(1,…,1)).

## 4. Theorem 2 from published results

### 4.0 Shortest route: Heinävaara's Corollary 1.2

1. **Derivatives as a measure.** In an eigenbasis of A, the Daleckii–Krein formula and the Hermite–Genocchi formula
   for divided differences give, for every smooth G,

   $$\frac{d^m}{dy^m}\operatorname{Tr}G(A+yB)\Big|_{y=0}=\int G^{(m)}\,d\pi_m,\qquad \pi_m=\sum_{i\in[d]^m}b_{i_1i_2}\cdots b_{i_mi_1}\,\mathrm{Law}\Bigl(\sum_ju_j\alpha_{i_j}\Bigr),$$

   with $u\sim\mathrm{Dirichlet}(1,\dots,1)$.
2. **The measure is positive.** By Heinävaara's Corollary 1.2 (B ≥ 0 is needed for odd m), the left side is ≥ 0
   whenever $G^{(m)}\ge0$. So $\pi_m$ is a positive measure.
3. **The word averages are its moments.** The cycle expansion gives $\mathcal A_{n,m}(A,B)=\int\tau^n\,d\pi_m$
   (Theorem 6).
4. **Atoms versus density.**
   - A term of $\pi_m$ is an atom exactly when all $\alpha_{i_j}$ are equal. Otherwise it is the push-forward of
     the Dirichlet density by a non-constant linear map, hence absolutely continuous.
   - So the atomic part of $\pi_m$ is $\sum_k\operatorname{Tr}_{Q_k}(Q_kBQ_k)^m\,\delta_{\alpha_k}$.
   - Atoms and absolutely continuous parts are mutually singular, so positivity of $\pi_m$ forces its absolutely
     continuous part to be ≥ 0.
5. **Conclusion.** For A ≥ 0,
   $\mathcal A_{n,m}(A,B)-\operatorname{Tr}(A^nE_A(B)^m)=\int\tau^n\,d\pi_m^{\rm ac}\ge0$. ∎

Theorem 1 identifies $\pi_m^{\rm ac}$ exactly, as $m(m-1)\bigl(\int s^{m-2}\rho_{B,A}\,ds\bigr)d\tau$.

### 4.1 Via the explicit density in Heinävaara's thesis

The inequality of Theorem 2 can also be derived directly from the explicit BMV measure in O. Heinävaara's PhD thesis
(*Tracial joint spectral measures*, Princeton 2024, Section 1.4, Theorem 24 and the proof of part 1, pp. 40–43).

1. **The thesis formula.** For Hermitian A and Hermitian B with simple spectrum:

   $$\operatorname{Tr}e^{A-tB}=\sum_{v\in E(B)}e^{\langle Av,v\rangle-t\langle Bv,v\rangle}+\frac1{2\pi}\iint e^{a-bt}\sum_i\bigl|\operatorname{Im}\lambda_i\bigl((aI-A)(bI-B)^{-1}\bigr)\bigr|\,da\,db,$$

   where E(B) is a set of normalized eigenvectors of B. The eigenvalues of $(aI-A)(bI-B)^{-1}$ are the roots of
   $\det(A-a-\xi(B-b))$, so the density is $\rho_{A,B}$.
2. **Rescaling.** Replacing A by aA (real a ≠ 0) and changing variables gives (∗) when the second matrix has simple
   spectrum. Both sides are entire.
3. **Coefficient extraction.** Step 1 then gives Theorems 1 and 2 when A has simple spectrum.
4. **Repeated eigenvalues of A.**
   - Inside each eigenspace of A, perturb A along an eigenbasis of $Q_kBQ_k$: $A_\varepsilon=A+\varepsilon D$, with D
     diagonal in that basis and distinct positive entries.
   - Then $E_{A_\varepsilon}(B)=E_A(B)$ for all small ε > 0: the off-diagonal entries of B inside each block vanish
     in that basis.
   - Both sides of Theorem 2 are continuous in A, so letting ε → 0 proves Theorem 2 for every A ≥ 0.

The exact identity of Theorem 1 for repeated eigenvalues, and Theorems 3–6, use Theorem A in its general form, which
is not in the thesis.

## 5. Verification

- **Our checks** (`code/verify_pinching.py`, log `logs/verify_pinching.log`):
  - The coefficient recursion agrees with explicit listing of all words to 6e-16.
  - Theorem 2: 40,500 cases (d = 2..6; repeated and zero eigenvalues of A; B of every rank; 0 ≤ n, m ≤ 8). The most
    negative relative gap is −1.1e-14 (rounding).
  - Theorem 3: worst relative violation 1.1e-14; equality at m = 2 to 1e-14.
  - Theorem 4: 7,500 indefinite cases with n, m even, no violation. At (n, m) = (1, 3), 152 of 300 random indefinite
    cases violate, which shows a sign condition is needed.
  - Theorem 1 against direct quadrature of the integral: 15 cases, agreement to 5–6 digits.
- **Independent check** (`independent-check/`), written from scratch with exact rational and ball arithmetic:
  - Verdict: **no errors**.
  - Theorem 1 holds **exactly** (rational arithmetic) for d = 2, in 14,400 identities. For d = 2, ρ is a semicircle
    density in s.
  - Theorem 1 holds to 28–39 significant digits for d = 3, 4, in 8 configurations: repeated and zero eigenvalues, a
    projection A, rank-one B, complex B, indefinite letters.
  - On the Cha–Lee pair it holds to 26 digits at x = 1/1000 and to 19 digits at x = 10⁻⁶.
  - Theorems 2–6 hold in about 27,000 exact cases, with an adversarial search on top.
  - On the whole Cha–Lee family, for 0 ≤ n, m ≤ 12, every gap polynomial has no root in (0, ∞), except at x = 1/2,
    where the pinching changes. That point was checked separately.

## 6. Credits and scope

- **Not new:**
  - The inequality of Theorem 2 as a mathematical fact. It follows from Heinävaara's Corollary 1.2 (arXiv:2310.03227,
    2023; Invent. Math. 239 (2025)) by the short argument of Section 4.0.
  - The positivity of the fixed-m measure in Theorem 6, which is equivalent to that corollary.
  - The deep input: positivity of the explicit two-variable BMV density. The atoms and density are due to H. Stahl
    (Acta Math. 211 (2013)); the explicit |Im| form for simple spectrum to O. Heinävaara (thesis, 2024).
  - The identity (∗) for general Hermitian P is also stated in our earlier paper on OQP 27
    (github.com/anshM123/IQOQI-OQP-27, `papers/math/main.tex`, Remark RIgeneralB). It is proved in full in
    [`02-theorem-A.md`](02-theorem-A.md).
- **New, as far as our searches show (arXiv, Semantic Scholar, Google Scholar, the Heinävaara and Cha author pages,
  2026-10-08):**
  - The observation that Dinh's Conjecture 5.1 holds for all word lengths. Dinh did not cite Heinävaara, and we found
    no place where this consequence is stated.
  - The exact gap identity, its strictness clause, the two-sided bound, the sign-condition variants, the Jensen form,
    and the explicit form of the fixed-m measure.
- **How hard it is.** Theorem 2 is short once Heinävaara's Corollary 1.2 (or the explicit density) is available.
  - It is not a soft consequence of convexity: $B\mapsto\mathcal A_{n,m}(A,B)$ is not convex on positive
    semidefinite matrices (exact witnesses in the independent check).
  - Nor does it follow from Stahl's one-variable theorem alone.
