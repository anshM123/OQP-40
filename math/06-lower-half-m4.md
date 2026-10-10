# The lower half of OQP 40 at (n, 4) and (4, n)

**Status (2026-10-09).** Let

$$\mathcal N_4=\{3,4,\dots,14\}\cup\{16,18,20,22\}.$$

For every n ∈ 𝒩₄ and all positive definite A, B of any size, $\mathcal A_{n,4}(A,B)\ge\operatorname{Tr}((A^{n/4}B)^4)$.
This is Conjecture F at (n, 4). Hence the lower half (LH) of OQP 40 holds at (n, 4) and, by exchanging the letters, at
(4, n), for every n ∈ 𝒩₄.
- **New cases of (LH):** (n, 4) and (4, n) for n ∈ 𝒩₄ ∖ {3, 4, 6}. The cases (3,4), (4,3), (4,4), (6,4) and (4,6) were
  proved in [`04-lower-half-new-cases.md`](04-lower-half-new-cases.md) by sum-of-squares certificates. The method here
  re-proves them by a different route.
- **Method.** A certificate of a new type (diagonal shares, Section 2). For each n it is given by a polynomial rule in
  fractional powers of the eigenvalues. The rule is valid if one univariate polynomial matrix C(s) is positive
  semidefinite on (0, 1]. We prove this exactly, with leading principal minors, for each n.
- **Status.** Computer-assisted, checked internally with three separately written verifiers (Section 5), not refereed
  externally. The statement for all n is open (Section 6).

Notation as in [`03-lower-half.md`](03-lower-half.md), [`04-lower-half-new-cases.md`](04-lower-half-new-cases.md) and
[`05-lower-half-m3.md`](05-lower-half-m3.md):
- $\mathcal A_{n,m}$ is the word average ($p_{n,m}$ in OQP 40);
- (LH) is $\mathcal A_{n,m}\ge\operatorname{Tr}\exp(n\log A+m\log B)$;
- Conjecture F is $\mathcal A_{n,m}\ge\operatorname{Tr}(A^{n/m}B)^m$. It implies (LH) by Lemma 2.1 of
  03-lower-half.md.

## 1. Result

**Theorem 6.** For every n ∈ 𝒩₄ and all positive definite A, B of any size d,

$$\mathcal A_{n,4}(A,B)\ \ge\ \operatorname{Tr}\bigl((A^{n/4}B)^4\bigr)\ \ge\ \operatorname{Tr}\exp(n\log A+4\log B),$$

and, exchanging the letters, $\mathcal A_{4,n}(A,B)=\mathcal A_{n,4}(B,A)\ge\operatorname{Tr}\exp(4\log A+n\log B)$.

## 2. Diagonal shares

**Reduction.** Let $A=\sum_k\alpha_kQ_k$ (distinct eigenvalues, any multiplicities), $W_k=B^{1/2}Q_kB^{1/2}\ge0$ and
$T(i)=\operatorname{Tr}(W_{i_1}W_{i_2}W_{i_3}W_{i_4})$ for $i\in[r]^4$. Put

$$K_n(x_1,x_2,x_3,x_4)=\frac{h_n(x_1,x_2,x_3,x_4)}{\binom{n+3}3}-(x_1x_2x_3x_4)^{n/4}.$$

As in Section 2 of the m = 3 note (read each word cyclically from a letter B and average over the weak compositions
of n into four parts),

$$\mathcal A_{n,4}(A,B)-\operatorname{Tr}\bigl((A^{n/4}B)^4\bigr)=\Phi(K_n):=\sum_{i\in[r]^4}T(i)\,K_n(\alpha_{i_1},\alpha_{i_2},\alpha_{i_3},\alpha_{i_4}).$$

$K_n$ is symmetric, homogeneous of degree n, and vanishes on the diagonal.

**The Gram matrices.** For a, b ∈ [r] put $X_c=W_a^{1/2}W_cW_b^{1/2}$. Then

$$S^{ab}_{cd}:=T(a,c,b,d)=\operatorname{Tr}(W_aW_cW_bW_d)=\operatorname{Tr}(X_d^\ast X_c),$$

so for fixed (a, b) the matrix $S^{ab}=[S^{ab}_{cd}]_{c,d}$ is a Gram matrix, hence positive semidefinite. The letters
a, b sit at opposite positions of the 4-cycle. That is why we call the certificate below a *diagonal share*.

**Lemma 10 (diagonal shares).** Let k(x, y; e, f) be a real function on $(0,\infty)^4$, symmetric in x ↔ y and in
e ↔ f, such that
- (S) $k(x,y;e,f)+k(e,f;x,y)=2K_n(x,e,y,f)$ for all x, y, e, f > 0;
- (P) for all x, y > 0 the kernel $(e,f)\mapsto k(x,y;e,f)$ is positive semidefinite on (0, ∞).

Then $\Phi(K_n)\ge0$, that is, Conjecture F holds at (n, 4).

*Proof.*
- **Using (S).** By (S) and the symmetry of $K_n$,
  $T(i)K_n(\alpha_i)=\frac12T(i)[k(\alpha_{i_1},\alpha_{i_3};\alpha_{i_2},\alpha_{i_4})+k(\alpha_{i_2},\alpha_{i_4};\alpha_{i_1},\alpha_{i_3})]$.
- **The second term.** Sum it over i and substitute the rotation $j=(i_2,i_3,i_4,i_1)$. Then T(j) = T(i), and
  $k(\alpha_{i_2},\alpha_{i_4};\alpha_{i_1},\alpha_{i_3})=k(\alpha_{j_1},\alpha_{j_3};\alpha_{j_2},\alpha_{j_4})$ by
  the symmetry in the last two arguments. So it gives the same sum as the first term, and

  $$\Phi(K_n)=\sum_{a,b}\sum_{c,d}k(\alpha_a,\alpha_b;\alpha_c,\alpha_d)\,S^{ab}_{cd}=\sum_{a,b}\operatorname{Tr}\bigl(S^{ab}G^{ab}\bigr),
  \qquad G^{ab}=[k(\alpha_a,\alpha_b;\alpha_c,\alpha_d)]_{c,d}.$$

- **Signs.** $G^{ab}$ is real symmetric and positive semidefinite by (P), and $S^{ab}$ is positive semidefinite. So
  every trace is ≥ 0. ∎

Lemma 10 uses no input from Stahl's theorem. Diagonal shares are the 4-cycle analogue of the apex shares of Lemma 2 of
04-lower-half-new-cases.md. They were found numerically to exist for every spectrum we tried; the point is to find a
single function k that works for all spectra.

## 3. Polynomial rules

**Root variables.** Fix an integer q ≥ 1 such that 4 divides N := nq. We used q = 2 for even n and q = 4 for odd
n. Write $X=x^{1/q}$, $Y=y^{1/q}$, $U=e^{1/q}$, $V=f^{1/q}$. Then $K_n$ is a polynomial in X, Y, U, V, homogeneous of
degree N, with coefficients κ: $\binom{n+3}3^{-1}$ on each monomial whose exponents are all divisible by q, minus 1
on $(XYUV)^{N/4}$.

**Rules.** A polynomial rule is

$$k(x,y;e,f)=\sum_{a+b+i+j=N}\gamma(\{a,b\},\{i,j\})\,X^aY^bU^iV^j$$

with rational coefficients γ that depend only on the unordered pairs {a, b} and {i, j}. So k has the symmetries of
Lemma 10.
- **(S)** is the linear identity $\gamma(p,q)+\gamma(q,p)=2\kappa(p,q)$ for all pairs p, q.
- **(P)** concerns the kernel matrix $C(X,Y)=[C_{ij}]$, $C_{ij}=\sum_{a+b=N-i-j}\gamma(\{a,b\},\{i,j\})X^aY^b$, indexed
  by $i,j\in\{0,\dots,N\}$. Then $k(x,y;e,f)=\sum_{i,j}C_{ij}U^iV^j$. The functions $U^i$ are linearly independent on
  every infinite subset of (0, ∞), so (P) holds if and only if C(X, Y) is positive semidefinite for all X, Y > 0.
  - By homogeneity, $C(X,Y)=D\,C(1,Y/X)\,D$ with $D=\operatorname{diag}(X^{N/2-i})$.
  - By the symmetry X ↔ Y it suffices that **C(1, s) is positive semidefinite for 0 < s ≤ 1**, where
    $s=(y/x)^{1/q}$.
- Rows i of C with i > N/2 vanish identically: their diagonal entry would need negative degree in X, Y.

**The kernel condition.** C(1, s) is a symmetric matrix of polynomials in s with rational coefficients. Remove its
identically zero rows. If every leading principal minor of the remaining block is positive on the open interval (0, 1),
then C(1, s) is positive definite there, and by continuity positive semidefinite at s = 1. This is what we prove for
each n ∈ 𝒩₄.

**Structure that every rule must have.**
- At s = 1 (x = y) and at s = 0 the matrix C(1, s) is forced to be singular in known directions: some combinations of
  the rules' coefficients are fixed by (S) and positivity. For example, k(x,x;x,x) = K_n(x,x,x,x) = 0 forces
  C(1,1)v = 0 for v = (1, …, 1).
- These equalities are imposed exactly when the rule is constructed.
- A parity reduction lets us take γ = 0 whenever a + b is odd. Then C splits into two blocks (even and odd i), which
  halves the size of the computation.
- **Local structure.** Near a point where all four eigenvalues coincide,
  $K_n\approx\frac\lambda2\sum_i(\sigma_i-\bar\sigma)^2$ in logarithmic variables σ = log(eigenvalue), with
  λ = n(n+4)/20. The only quadratic solution of (S) that satisfies (P) is
  $\frac\lambda8[(2\sigma_e-\sigma_x-\sigma_y)(2\sigma_f-\sigma_x-\sigma_y)+5(\sigma_x-\sigma_y)^2]$: rank one plus a
  constant. Our rules reproduce it near the diagonal (checked numerically for n = 4, 5, 6). The obvious global extension
  $K_n+\frac34[K_n(x,x,y,y)-K_n(e,e,f,f)]$ fails at third order, and integer exponents (q = 1) are already impossible
  at n = 4.

## 4. Construction and the exact proof

**Construction (numerical, not part of the proof).**
1. A semidefinite program finds γ such that C(1, s) is positive definite, with a margin, at many sample points of
   (0, 1). Near s = 0 and s = 1 the samples are taken in scaled coordinates, and the forced singular directions are
   eliminated by a null-space parametrisation.
2. The solution is rounded to rationals and projected exactly onto the linear identity (S) and the endpoint
   equalities.

**The proof for one n.**
- (S) holds as an exact identity of rational coefficients.
- Every leading principal minor of the nonzero block of C(1, s) is computed exactly over ℚ[s] (fraction-free
  elimination). Each minor is shown to have no root in (0, 1) and to be positive at s = 1/2.

| n | q | size of C(1, s): even ⊕ odd block | largest degree of a minor (per block) | margin of the search | |
|---|---|---|---|---|---|
| 3 | 4 | 7 = 4 ⊕ 3 | 22 | 2.4e-2 | |
| 4 | 2 | 5 = 3 ⊕ 2 | 12 | 3.9e-2 | (also by hand, Section 4.1) |
| 5 | 4 | 11 = 6 ⊕ 5 | 52 | 1.8e-3 | new |
| 6 | 2 | 7 = 4 ⊕ 3 | 22 | 1.3e-2 | |
| 7 | 4 | 15 = 8 ⊕ 7 | 94 | 1.0e-4 | new |
| 8 | 2 | 9 = 5 ⊕ 4 | 36 | 3.8e-3 | new |
| 9 | 4 | 19 = 10 ⊕ 9 | 148 | 4.7e-6 | new |
| 10 | 2 | 11 = 6 ⊕ 5 | 52 | 1.0e-3 | new |
| 11 | 4 | 23 = 12 ⊕ 11 | 214 | 9.7e-8 | new |
| 12 | 2 | 13 = 7 ⊕ 6 | 72 | 2.3e-4 | new |
| 13 | 4 | 27 = 14 ⊕ 13 | 292 | 3.4e-9 | new |
| 14 | 2 | 15 = 8 ⊕ 7 | 94 | 5.3e-5 | new |
| 16 | 2 | 17 = 9 ⊕ 8 | 120 | 1.1e-5 | new |
| 18 | 2 | 19 = 10 ⊕ 9 | 148 | 2.3e-6 | new |
| 20 | 2 | 21 = 11 ⊕ 10 | 180 | 2.3e-7 | new |
| 22 | 2 | 23 = 12 ⊕ 11 | 214 | 4.8e-8 | new |

The margins are the optimal values of the scaled search problems. They only indicate how much room the search had; the
proof does not use them. They fall by a factor of about 4 from n to n + 2 for even n, and of about 20 for odd n.

### 4.1 The case (4, 4) by hand

For n = 4 (q = 2) one rule has small integer coefficients ([`../lower-half/m4/rules/n4_simple.json`](../lower-half/m4/rules/n4_simple.json)).
With X = x^{1/2}, Y = y^{1/2} and $v(e)=(1,e,e^2;\,e^{1/2},e^{3/2})$, it is
$k(x,y;e,f)=v(e)^{\mathsf T}C(x,y)\,v(f)$ with $C=C_{\rm even}\oplus C_{\rm odd}$, where

$$35\,C_{\rm even}=\begin{pmatrix}
2(X^8+X^6Y^2-X^4Y^4+X^2Y^6+Y^8) & 2(X^6+Y^6)-X^4Y^2-X^2Y^4-5X^3Y^3 & X^4-5X^2Y^2+Y^4\\
\cdot & 7(X^4+Y^4)+12(X^3Y+XY^3)-34X^2Y^2 & 3(X^2+Y^2)-7XY\\
\cdot & \cdot & 4\end{pmatrix},$$

$$35\,C_{\rm odd}=\begin{pmatrix}7(X^4Y^2+X^2Y^4)-2X^3Y^3 & -12X^2Y^2\\ -12X^2Y^2 & 5(X^2+Y^2)+2XY\end{pmatrix}.$$

- (S) is the polynomial identity $k(x,y;e,f)+k(e,f;x,y)=2\bigl(h_4(x,y,e,f)/35-xyef\bigr)$.
- With X = 1 and Y = s, the leading principal minors are, up to powers of 35:
  - for $C_{\rm odd}$: $s^2(7s^2-2s+7)$ and $s^2(1-s)^2(5s+7)(7s+5)$;
  - for $C_{\rm even}$: $2(s^8+s^6-s^4+s^2+1)$, positive because $s^6+s^2\ge2s^4$; a palindromic polynomial of degree
    12, which divided by $s^6$ is a polynomial in u = s + 1/s − 2 ≥ 0 with only positive coefficients (from the top
    down: 10, 144, 730, 1628, 1593, 502, 15); and
    $(1-s)^2(27s^{10}+194s^9+59s^8+596s^7+243s^6-318s^5+243s^4+596s^3+59s^2+194s+27)$, positive because
    $243(s^6+s^4)\ge486s^5$.

So the (4,4) case of Conjecture F can be checked by hand. It was known (Theorem 2 of 04-lower-half-new-cases.md); this
certificate is shorter.

## 5. Checks

All checks are internal; none is an external referee report. Scripts, certificates and logs are in
[`../lower-half/m4/`](../lower-half/m4/README.md).

1. **The exact check that comes with the construction** (`exact_rule.py`, `exactcheck.py`; python-flint). Bareiss
   elimination over ℚ[s]; positivity on (0, 1) by Descartes' rule of signs with bisection (Vincent–Collins–Akritas).
2. **A second exact verifier** (`verify_independent.py`, sympy only). It rebuilds $K_n$ from its definition, checks (S)
   as a polynomial identity and the parity splitting, and proves the minors positive with sympy's fraction-free
   elimination over ℤ[s] and sympy's real-root isolation. For n ≥ 11 the sympy elimination is too slow, so
   `verify_independent_fast.py` keeps the sympy construction, the identity check and the root isolation and replaces
   only the elimination by a separately written integer Bareiss loop.
3. **A third exact verifier** (`verify_rule_independent.py`), written separately from the first two, with its own code
   for the elimination.
   - It checks (S) coefficientwise against $K_n$ rebuilt from its definition.
   - It certifies each minor by one of two tests. The first is a Descartes sign test after the substitution
     s = t/(1 + t). When that test is inconclusive, it isolates all complex roots with Arb ball arithmetic.
   - It runs an end-to-end test in 60-digit arithmetic. For random A and B with d = 3, 4 it checks three things: the
     certificate value $\sum_{a,b}\operatorname{Tr}(S^{ab}G^{ab})$ equals the cycle sum $\Phi(K_n)$; that equals
     $\mathcal A_{n,4}-\operatorname{Tr}((A^{n/4}B)^4)$ computed directly from the words; and every $G^{ab}$ is
     positive semidefinite.
4. **End to end** (`check_rule.py`, 50 digits): the same identities and positivity on random positive definite A, B.

All three exact verifiers pass for every n ∈ 𝒩₄ (logs in `lower-half/m4/logs/`).

## 6. What is not claimed

- Conjecture F at (n, 4) for n ∉ 𝒩₄, and in particular for all n. Each n is a separate computation; the rules differ
  from n to n. The SDP margins decrease as n grows. As for m = 3, an all-n proof would need a uniform argument that
  we do not have.
- Even m ≥ 6. Diagonal shares generalise: cut the m-cycle through two opposite letters a, b. The Gram matrices
  $\operatorname{Tr}(W_aYW_bY'^\ast)$ are then indexed by the products Y, Y′ of the m/2 − 1 letters in between. For
  m = 6 such certificates exist numerically for the spectra we tried (n = 4, 5, 6; three distinct eigenvalues).
  Explicit rules have not yet been constructed.
- Odd m ≥ 5, and in particular (5, 5). For odd m the only Gram matrices of this kind cut each cycle through one
  letter (an apex, as in Lemma 2 of 04-lower-half-new-cases.md). After scaling, a polynomial rule for an apex is then a
  single constant matrix instead of a family C(s).
  - In our numerical experiments such polynomial apex rules were infeasible at (3,3), for q ∈ {1, 2, 3, 4, 6}, and at
    (5,5) with integer exponents.
  - Apex certificates for m = 5 do exist numerically for every spectrum we tried: n = 4, 5, 6, 7, 10, with up to five
    distinct eigenvalues.
  - So a proof at (5,5) will probably need a rule with square roots, like the one for (3,3) in Theorem 1. We have not
    found one.
