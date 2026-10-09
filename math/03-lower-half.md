# The lower half of OQP 40: status

**Status (2026-10-09): OPEN in general.** It is proved in these cases:
- min(n, m) ≤ 2;
- (n, m) = (3,3), (3,4), (4,3), (4,4), (4,6) and (6,4), in any dimension
  ([`04-lower-half-new-cases.md`](04-lower-half-new-cases.md));
- A or B has at most two distinct eigenvalues, in any dimension (Proposition 2.5);
- B has nonnegative entries in some eigenbasis of A (Proposition 2.4). This includes every pair with d = 2; for d = 2
  even every single word satisfies $\operatorname{Tr}W\ge\operatorname{Tr}(A^{n/m}B)^m$, by Theorem 2.2 of Furuichi,
  Kuriyama and Yanagi (Linear Algebra Appl. 430 (2009)), so the case d = 2 was known.

This note records:
- what is proved (Sections 2–3);
- the numerical evidence (Section 4);
- a stronger conjecture (Section 5);
- the routes that do **not** work (Section 6).

## 1. The statement

For positive definite A, B and integers n, m ≥ 0 (notation of [`01-pinching-theorem.md`](01-pinching-theorem.md)):

$$\mathcal A_{n,m}(A,B)\ \ge\ L_{n,m}(A,B):=\operatorname{Tr}\exp(n\log A+m\log B).\tag{LH}$$

**Facts about (LH):**
- It holds with equality when AB = BA.
- For n = m = 1 it is the Golden–Thompson inequality.
- It **implies Stahl's theorem** (the BMV conjecture, in the Lieb–Seiringer form $\mathcal A_{n,m}\ge0$), since
  $L_{n,m}>0$. So any proof of (LH) must contain an argument of BMV strength.
- The upper half of OQP 40, $\mathcal A_{n,m}\le\operatorname{Tr}(A^nB^m)$, is false (Cha–Lee, arXiv:2603.19927).
  [`01-pinching-theorem.md`](01-pinching-theorem.md), Theorem 3, gives a correct two-sided substitute.

**The OQP page itself:**
- It notes that the per-word statement ("fragmenting a product lowers its trace") is false: single words can have
  negative trace (Johnson–Hillar, SIAM J. Matrix Anal. Appl. 23 (2002)).
- (LH) is about the **average** over all words, which is always positive.

## 2. Proved cases (elementary)

Put $F_{n,m}(A,B)=\operatorname{Tr}(A^{n/m}B)^m=\operatorname{Tr}(A^{n/2m}BA^{n/2m})^m$ for m ≥ 1.

**Lemma 2.1 (ALT step).** $F_{n,m}(A,B)\ge L_{n,m}(A,B)$, and symmetrically
$\operatorname{Tr}(AB^{m/n})^n\ge L_{n,m}(A,B)$ for n ≥ 1.

*Proof.* Put $A'=A^{n/m}$. The Araki–Lieb–Thirring inequality and the Lie–Trotter formula give
$\operatorname{Tr}\exp(m\log A'+m\log B)\le\operatorname{Tr}(B^{1/2}A'B^{1/2})^m$. ∎

**Proposition 2.2.** (LH) holds when $\min(n,m)\le2$.

*Proof.*
- **Zero letters.** If n = 0 or m = 0, both sides equal $\operatorname{Tr}B^m$ or $\operatorname{Tr}A^n$.
- **One letter.** If m = 1, $\mathcal A_{n,1}=\operatorname{Tr}(A^nB)\ge\operatorname{Tr}e^{n\log A+\log B}$ by
  Golden–Thompson.
- **Two letters.** If m = 2, $\mathcal A_{n,2}=\frac1{n+1}\sum_{r=0}^n f(r)$ with $f(r)=\operatorname{Tr}(A^rBA^{n-r}B)$.
  - In an eigenbasis of A, $f(r)=\sum_{i,j}|b_{ij}|^2\alpha_i^r\alpha_j^{n-r}$, a positive combination of
    exponentials in r. So f is log-convex on [0, n].
  - f is symmetric under r ↦ n − r, so $f(r)\ge f(n/2)=F_{n,2}(A,B)$ for every r.
  - Lemma 2.1 finishes.
- **The letters swapped.** The cases n ≤ 2 follow by exchanging the roles of A and B:
  $\mathcal A_{n,m}(A,B)=\mathcal A_{m,n}(B,A)$. ∎

**Proposition 2.3.** If B = bb* has rank one, then $\mathcal A_{n,m}(A,B)\ge F_{n,m}(A,B)$ for every A ≥ 0. The same
holds with the letters exchanged.

*Proof.*
- **Reduction to scalars.** Every word, read cyclically from a B, is $BA^{N_1}BA^{N_2}\cdots BA^{N_m}$ with
  $N_1+\dots+N_m=n$. A uniformly random word, read from a uniformly chosen letter B, gives a uniformly random
  composition N. For rank-one B its trace is
  $\prod_j\psi(N_j)$, with $\psi(t)=\langle b,A^tb\rangle$.
- **Log-convexity.** ψ is log-convex, so $\frac1m\sum_j\log\psi(N_j)\ge\log\psi(n/m)$ for **every** composition.
- **Conclusion.** Hence every word trace is $\ge\psi(n/m)^m=F_{n,m}(A,B)$. ∎

### 2.4 Two further proved cases

**Cycle expansion.** Fix an orthonormal eigenbasis $(e_i)$ of A, with $Ae_i=\alpha_ie_i$ and $b_{ij}=\langle e_i,Be_j\rangle$.
For $i\in[d]^m$ put $\beta(i)=b_{i_1i_2}b_{i_2i_3}\cdots b_{i_mi_1}$. For a symmetric function φ on $(0,\infty)^m$ put
$\Phi_B(\varphi)=\sum_i\beta(i)\,\varphi(\alpha_{i_1},\dots,\alpha_{i_m})$. Then

$$\mathcal A_{n,m}(A,B)=\Phi_B(M_n),\qquad p^{\rm mult}_{n,m}(A,B):=\Phi_B(\bar x^{\,n}),\qquad F_{n,m}(A,B)=\Phi_B(G^n),$$

where:
- $M_n(x)=h_n(x)/\binom{n+m-1}{n}=\mathbb E_u(\sum_ju_jx_j)^n$, with $u\sim\mathrm{Dirichlet}(1,\dots,1)$;
- $\bar x$ is the arithmetic mean and $G(x)=(x_1\cdots x_m)^{1/m}$ the geometric mean.

The first identity holds because a uniformly random word, read from a uniformly chosen letter B, gives a uniformly
random composition $(N_1,\dots,N_m)$ of n, and averaging $\prod_jx_j^{N_j}$ over compositions gives $M_n$. Pointwise,
$M_n\ge\bar x^{\,n}\ge G^n$ (Jensen, then AM–GM).

**Proposition 2.4.** Suppose some orthonormal eigenbasis of A has $\langle e_i,Be_j\rangle\ge0$ for all i, j. Then

$$\mathcal A_{n,m}(A,B)\ \ge\ p^{\rm mult}_{n,m}(A,B)\ \ge\ F_{n,m}(A,B)\ \ge\ L_{n,m}(A,B).$$

The hypothesis holds in the following cases:
- d = 2;
- B = D + ww* with [D, A] = 0;
- the off-diagonal pattern of B in some eigenbasis of A is a forest (for example, tridiagonal).

The same holds with the letters exchanged.

*Proof.*
- **The chain.** All β(i) ≥ 0, so $\Phi_B$ preserves pointwise inequalities between kernels, and the last step is
  Lemma 2.1.
- **When the hypothesis holds.** Rotating eigenvectors by phases, $e_j\mapsto e^{i\phi_j}e_j$, changes $b_{jk}$ into
  $e^{-i\phi_j}b_{jk}e^{i\phi_k}$.
  - On a forest, the equations $\phi_k-\phi_j=-\arg b_{jk}$ (one per edge) are solvable.
  - For B = D + ww*, first diagonalize D inside each eigenspace of A. Then $b_{jk}=w_j\bar w_k$ for j ≠ k, and
    $\phi_j=\arg w_j$ works. ∎

**Proposition 2.5 (two distinct eigenvalues).** If A or B has at most two distinct eigenvalues, then (LH) holds, in
every dimension. If A is the one, the chain of Proposition 2.4 holds.

*Proof.*
- **Reduction to types.** Let $A=\alpha_1Q_1+\alpha_2Q_2$, and let k(i) be the number of indices $i_j$ in the range
  of $Q_1$. For symmetric φ, $\varphi(\alpha_i)$ depends only on k(i), say $\varphi[k]$, and so
  $\Phi_B(\varphi)=\sum_{k=0}^mc_k\varphi[k]$ with $c_k=\sum_{k(i)=k}\beta(i)$.
- **The type weights are nonnegative.** With $D_s=sQ_1+Q_2$, we have
  $\sum_kc_ks^k=\operatorname{Tr}(D_sB)^m=\operatorname{Tr}(Z+sY)^m$, where $Z=B^{1/2}Q_2B^{1/2}\ge0$ and
  $Y=B^{1/2}Q_1B^{1/2}\ge0$. By Stahl's theorem in the Lieb–Seiringer form, every coefficient of
  $s\mapsto\operatorname{Tr}(Z+sY)^m$ is nonnegative. So $c_k\ge0$.
- **The chain.** Since $c_k\ge0$, the pointwise kernel inequalities give
  $\mathcal A_{n,m}\ge p^{\rm mult}_{n,m}\ge F_{n,m}$. Lemma 2.1 finishes.
- **B with two eigenvalues.** Use $\mathcal A_{n,m}(A,B)=\mathcal A_{m,n}(B,A)$. ∎

For three or more distinct eigenvalues the type weights are the coefficients of
$\operatorname{Tr}(s_1W_1+s_2W_2+s_3W_3)^m$, which can be negative. This is where a new idea is needed.

## 3. Structural facts proved here

- **Fixed-m measure.** By [`01-pinching-theorem.md`](01-pinching-theorem.md), Theorem 6, for fixed m the numbers
  $\mathcal A_{n,m}(A,B)$ are the moments of an explicit positive measure $\pi_m$ on the spectral interval of A. Its
  mass is $\operatorname{Tr}B^m$; it has atoms $\operatorname{Tr}_{Q_k}(Q_kBQ_k)^m$ at the eigenvalues of A, plus a
  density $m(m-1)\int s^{m-2}\rho_{B,A}\,ds$.
- **The other side.** By Stahl's theorem in the explicit form of [`02-theorem-A.md`](02-theorem-A.md), applied to
  $(\log B,\log A)$:
  - $L_{n,m}=\int\sigma^n\,d\nu_m(\sigma)$, where $\nu_m$ is a positive measure with the same mass, supported on the
    same interval.
  - Its atoms at the eigenvalues of A are $\operatorname{Tr}_{Q_k}e^{mQ_k\log B\,Q_k}$. These are at most the atoms of
    $\pi_m$, by Choi's inequality $Q\log B\,Q\le\log(QBQ)$ applied eigenvalue by eigenvalue.
- **Reformulation.** (LH) is therefore equivalent to: **the n-th moments of $\pi_m$ dominate those of $\nu_m$ for all
  n ≥ 1.** Equality holds at n = 0.
  - Numerically the domination holds for all real exponents x ≥ 0.25 tested, not only integers (Section 4).
  - First-order stochastic dominance is impossible in general (the excess atom at the smallest eigenvalue).

## 4. Numerical evidence

All scripts are in `code/`, with logs in `logs/`.

| Search | Scope | Result |
|---|---|---|
| Gradient (Adam, GPU), `oqp40_torch.py` | d = 2..5; (n,m) up to (6,6), (3,7), (2,9); command `oqp40_torch.py d n m 384 2000 7` (384 starts, seed 7) | min log(𝒜/L) ≥ −2e-12, i.e. nothing below rounding; the optimizer drifts to large-scale, nearly commuting configurations |
| Nelder–Mead, `oqp40_lower.py` | d = 2, 3; (3,3), (4,4), (3,5); three seeds, each run stopped by a time limit after these cases (logs end with `exit 124`) | min log-ratio ≈ −2e-13 (rounding) |
| Near-commuting expansion, `oqp40_second_order.py` | coefficient of ε² is a sum of 2 × 2 pair terms; formula checked against a direct computation to 5–7 digits | every pair term ≥ 0. This is in fact a theorem: each pair term is the ε² coefficient of a 2 × 2 problem, and (LH) holds for d = 2 (Proposition 2.4). The (8,8) entry `-inf` in the log is a floating-point overflow; all endpoints are positive at 60 digits |
| Large d, Haar position, `freeregime.py` | d up to 120, spread spectra, 60 trials | min 𝒜/L = 1.086 |
| Cha–Lee family, `chalee_family.py` | x down to 1e-3 | 𝒜/L up to 3.4·10⁷ (with L regularised at δ = 1e-30), so the bound is very loose there |
| Singular / near-rank-one families, `chalee_frac.py` | 60 random families | min 𝒜/F = 1.26 |
| Negative-word region, `negword_search.py` | pairs where the necklace AABABB has negative trace | min log(𝒜/L) ≈ −3e-10, consistent with float64 matrix-exponential error at norm 10 (not re-evaluated in high precision) |
| Real exponents, `icx_test.py` | m = 3, x ∈ [0.25, 6]; p_{x,3} by Monte Carlo over the Dirichlet weights | min ratio > 1.00005 (exact Hermite–Genocchi values reproduce the minima to 6 digits) |

No counterexample was found.

## 5. A stronger conjecture

**Conjecture F.** For A, B ≥ 0 and m ≥ 1, $\mathcal A_{n,m}(A,B)\ge\operatorname{Tr}(A^{n/m}B)^m$.

- **Relation to (LH).** By Lemma 2.1, Conjecture F implies (LH).
- **Proved cases.** It holds:
  - for m ≤ 2 (Proposition 2.2);
  - for rank-one B (Proposition 2.3);
  - when B is entrywise ≥ 0 in some eigenbasis of A, including every pair with d = 2 (Proposition 2.4; for d = 2 this
    already follows from Furuichi–Kuriyama–Yanagi 2009, Theorem 2.2);
  - when A has at most two distinct eigenvalues (Proposition 2.5);
  - at (n, m) = (3,3), (3,4), (4,4) and (6,4), in every dimension
    ([`04-lower-half-new-cases.md`](04-lower-half-new-cases.md), Theorems 1 and 2).

  The version with the letters exchanged holds in the exchanged cases. At (4,3) and (4,6) only the version with the
  letters exchanged is proved ([`04-lower-half-new-cases.md`](04-lower-half-new-cases.md), Corollary 3).
- **Numerics.** It held in every test above, including the Cha–Lee family (min ratio 1.25) and large-d Haar position
  (min ratio 1.06).
- **For n = m** it reads $\mathcal A_{n,n}(A,B)\ge\operatorname{Tr}(AB)^n$: the average over all words dominates the
  most alternating word.

## 6. Routes that fail (do not retry)

- **Refinement monotonicity:** $\mathcal A_{2n,2m}(A,B)\le\mathcal A_{n,m}(A^2,B^2)$. If true, (LH) would follow
  through the Trotter limit. It is **false**: in the Cha–Lee family the ratio reaches 1.7·10⁸ at x = 1e-3,
  (n,m) = (5,5) (`logs/chalee_family.log`).
- **Pinched bounds alone.** $\max(\operatorname{Tr}A^nE_A(B)^m,\operatorname{Tr}E_B(A)^nB^m)$ can be far below
  $L_{n,m}$: log-ratio −1.38, `logs/oqp40_aux.log`, mode `pinch2`.
- **An increasing-convex-order strengthening.** Natural candidates are $\pi_m\ge_{\rm icx}\nu_m$, or the same on the
  log scale.
  - They hold for generic random pairs.
  - Both fail on PD shifts of the Cha–Lee family: A_x + δ, B_x + δ with x = 0.1 and δ = 1e-3, at m = 3.
  - The Laplace order for real exponents x ≥ 0 still holds there. So this order is not the mechanism.
- **Comparing only the continuous parts** of $\pi_m$ and $\nu_m$ fails near commuting pairs. The atomic surplus is
  essential.
- **Per-composition (Schur-convexity) arguments** fail because single words can have negative trace.
- **A continuous-Dirichlet intermediate.** $P_{\rm cont}=\frac{d^m}{ds^m}\operatorname{Tr}e^{n\log A+sB}\big|_{s=0}$
  is not below $\mathcal A_{n,m}$ in general (Cha–Lee family, ratio 0.80).
