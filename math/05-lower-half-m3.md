# The lower half of OQP 40 at (n, 3) and (3, n)

**Status (2026-10-09).** Let

$$\mathcal N=\{1,2,\dots,36\}\cup\{39,42,\dots,66\}.$$

For every n ∈ 𝒩 and all positive definite A, B of any size, $\mathcal A_{n,3}(A,B)\ge\operatorname{Tr}((A^{n/3}B)^3)$.
This is Conjecture F at (n, 3). Hence the lower half (LH) of OQP 40 holds at (n, 3) and, by exchanging the letters, at
(3, n), for every n ∈ 𝒩.
- **New cases of (LH):** (n, 3) and (3, n) for n = 5, …, 36 and n = 39, 42, …, 66. The cases (3, 3), (3, 4) and (4, 3)
  were already proved in [`04-lower-half-new-cases.md`](04-lower-half-new-cases.md); for (4, 3) Conjecture F itself is
  new here (that note has only the version with the letters exchanged). The case (6, 3) is out of reach of the
  sum-of-squares certificates of that note (its Section 4.4).
- **Method.** The certificate of Theorem 1 of the previous note, with a different weight, and a reduction of its
  conditions to polynomials that have only nonnegative coefficients after a shift. For each n this is a finite exact
  computation over the rationals, which takes from a fraction of a second to 13 minutes.
- **Status.** Computer-assisted, checked internally (Section 6), not refereed externally. The statement for all n is
  open (Section 7).

Notation as in [`03-lower-half.md`](03-lower-half.md) and [`04-lower-half-new-cases.md`](04-lower-half-new-cases.md):
$\mathcal A_{n,m}$ is the word average ($p_{n,m}$ in OQP 40), (LH) is $\mathcal A_{n,m}\ge\operatorname{Tr}\exp(n\log
A+m\log B)$, and Conjecture F is $\mathcal A_{n,m}\ge\operatorname{Tr}(A^{n/m}B)^m$, which implies (LH) (Lemma 2.1 of
03-lower-half.md).

## 1. Result

**Theorem 5.** For every n ∈ 𝒩 and all positive definite A, B of any size d,

$$\mathcal A_{n,3}(A,B)\ \ge\ \operatorname{Tr}\bigl((A^{n/3}B)^3\bigr)\ \ge\ \operatorname{Tr}\exp(n\log A+3\log B),$$

and, exchanging the letters, $\mathcal A_{3,n}(A,B)=\mathcal A_{n,3}(B,A)\ge\operatorname{Tr}\exp(3\log A+n\log B)$.

For n = 1 the first inequality is classical (Araki–Lieb–Thirring), and for n = 3 it is Theorem 1 of the previous note;
the method below re-proves both.

## 2. The certificate for general n

**The kernel.** Put

$$K_n(x,y,z)=\frac{h_n(x,y,z)}{\binom{n+2}2}-(xyz)^{n/3},$$

where $h_n$ is the complete homogeneous symmetric polynomial of degree n. $K_n$ is symmetric and homogeneous of degree
n, and $K_n(x,x,x)=0$. By the arithmetic–geometric mean inequality, $K_n\ge0$ with equality only if x = y = z: the
average of the monomials $x^{c_1}y^{c_2}z^{c_3}$ over the weak compositions c of n into three parts is at least their
geometric mean $(xyz)^{n/3}$.

**Reduction.** Let $A=\sum_k\alpha_kQ_k$ (distinct eigenvalues, any multiplicities) and $T(i,j,k)=
\operatorname{Tr}(BQ_iBQ_jBQ_k)$, as in Section 2.1 of the previous note. Read cyclically from a letter B, a word is
$BA^{c_1}BA^{c_2}BA^{c_3}$ with c a weak composition of n. Each of the $\binom{n+2}2$ compositions arises from exactly
n + 3 pairs (word, chosen letter B), so

$$\mathcal A_{n,3}=\binom{n+2}2^{-1}\sum_{i,j,k}T(i,j,k)\,h_n(\alpha_i,\alpha_j,\alpha_k),\qquad
\operatorname{Tr}\bigl((A^{n/3}B)^3\bigr)=\sum_{i,j,k}T(i,j,k)\,(\alpha_i\alpha_j\alpha_k)^{n/3},$$

and $\mathcal A_{n,3}-\operatorname{Tr}((A^{n/3}B)^3)=\Phi(K_n)$ in the notation of Lemma 2 of the previous note.

**The certificate (min-apex rule).** For 0 < x < y < z put

$$\operatorname{cap}_z(x,y)=\sqrt{K_n(z,x,x)\,K_n(z,y,y)},\qquad E_x(y,z)=E_x(z,y)=K_n(x,y,z)-\operatorname{cap}_z(x,y),$$

and $E_x(y,y)=K_n(x,y,y)$. Split $K_n$ on each triple $\alpha_i<\alpha_j<\alpha_k$ as in Section 2.3 of the previous
note: the largest point gets $\operatorname{cap}_{\alpha_k}(\alpha_i,\alpha_j)$, the smallest gets
$E_{\alpha_i}(\alpha_j,\alpha_k)$, the middle point gets 0. Each matrix $G^{(l)}$ is then block diagonal, with a rank-one
block $uu^T$, $u(a)=\sqrt{K_n(\alpha_l,\alpha_a,\alpha_a)}$, for the indices below l, a zero cross block, and the block
$[E_{\alpha_l}(\alpha_b,\alpha_{b'})]$ for the indices above l. By Lemma 2 of the previous note:

**Proposition 6.** If for every x > 0 the kernel $(y,z)\mapsto E_x(y,z)$ is positive semidefinite on (x, ∞), then
$\mathcal A_{n,3}(A,B)\ge\operatorname{Tr}((A^{n/3}B)^3)$ for all positive definite A, B of any size. No input from
Stahl's theorem is used.

$K_n$ and cap are homogeneous of degree n, so $E_x(y,z)=x^nE_1(y/x,z/x)$, and the hypothesis is equivalent to:

**Lemma 7(n).** $E:=E_1$ is a positive semidefinite kernel on (1, ∞).

## 3. Lemma 7(n): one square root, four conditions, squaring

**Variables.** Let e = 1 if 3 divides n and e = 3 otherwise, and write $s=X^e$, $t=Y^e$ with 1 < X < Y. Then
$K_w(a,b,c):=K_n(a^e,b^e,c^e)$ is a polynomial with rational coefficients. Define the polynomials (the divisions are
exact)

$$K_1=K_w(1,X,Y),\quad q_1=\frac{K_w(Y,1,1)}{(Y-1)^2},\quad q_2=\frac{K_w(Y,X,X)}{(Y-X)^2},\quad p_t(Z)=\frac{K_w(1,Z,Z)}{(Z-1)^2}.$$

Then, for 1 < s < t,

$$E(s,t)=K_1-(Y-1)(Y-X)\,r,\qquad r=\sqrt{q_1q_2},$$

and the same formula at X = Y gives the diagonal value $E(s,s)=K_n(1,s,s)$. So the kernel contains a single square
root.

**Weight.** Take $w(s)=\sqrt{E(s,s)}=(X-1)\sqrt{p_t(X)}$ and $F(s,t)=E(s,t)/(w(s)w(t))$ for s ≤ t, so that F(s, s) = 1.
Its logarithmic derivative is rational:
$\frac{d}{dX}\log w=N_w/D_w$ with $N_w=2p_t+(X-1)p_t'$ and $D_w=2(X-1)p_t$.

By Lemma 4 of the previous note it suffices to show, on 1 < X < Y (s = X^e is increasing in X),

$$F\ge0,\qquad F_X\ge0,\qquad F_Y\le0,\qquad F_{XY}\le0,$$

together with the continuity of F up to the diagonal, which holds because $q_1,q_2,p_t>0$ on 1 ≤ X ≤ Y (obligation P0
below).

**Lemma 8 (the conditions in the form α + βr).** A function α + βr with polynomials α, β is written as the pair
(α, β). Since $q_1$ depends only on Y, $r_X=r\,q_{2,X}/(2q_2)$ and $r_Y=r\,(q_1q_2)_Y/(2q_1q_2)$. So the operators

$$D_X(a,b)=\bigl(2q_2a_X,\;2q_2b_X+b\,q_{2,X}\bigr)=2q_2\,\partial_X(a+br),\qquad
D_Y(a,b)=\bigl(2q_1q_2a_Y,\;2q_1q_2b_Y+b\,(q_1q_2)_Y\bigr)=2q_1q_2\,\partial_Y(a+br)$$

map pairs to pairs, and $4q_1q_2^2\,\partial_X\partial_Y=D_YD_X-2q_1q_{2,Y}D_X$. With $E=(K_1,\,-(Y-1)(Y-X))$ and the
quotient rule for F, the four conditions are equivalent to $C_0,C_1,C_2,C_3\ge0$, where

$$\begin{aligned}
C_0&=E=w(X)w(Y)\,F,\\
C_1&=D_w(X)\,D_XE-2q_2N_w(X)\,E=2q_2D_w(X)\,w(X)w(Y)\,F_X,\\
C_2&=2q_1q_2N_w(Y)\,E-D_w(Y)\,D_YE=-2q_1q_2D_w(Y)\,w(X)w(Y)\,F_Y,\\
C_3&=-\bigl[D_w(X)D_w(Y)(D_YD_XE-2q_1q_{2,Y}D_XE)-2q_1q_2N_w(Y)D_w(X)D_XE-2q_2N_w(X)D_w(Y)D_YE\\
&\qquad\;+4q_1q_2^2N_w(X)N_w(Y)E\bigr]=-4q_1q_2^2D_w(X)D_w(Y)\,w(X)w(Y)\,F_{XY},
\end{aligned}$$

all of the form α + βr. (The factors $q_1,q_2,D_w,w$ are positive on 1 < X < Y.)

**Lemma 9 (squaring).** Let r > 0 with $r^2=q_1q_2$, and $\Delta=\alpha^2-\beta^2q_1q_2$.
- If α ≥ 0 and Δ ≥ 0, then α ≥ |β| r, so α + βr ≥ 0.
- If β ≥ 0 and −Δ ≥ 0, then βr ≥ |α|, so α + βr ≥ 0.

**Proof obligations for one n.** Call a polynomial P(X, Y) *SP* if it is nonzero and all its coefficients are ≥ 0 after
the substitution X = 1 + u, Y = 1 + u + v. An SP polynomial is > 0 for u, v > 0, that is, on 1 < X < Y. For each
$C_k=(\alpha,\beta)$ let g = gcd(α, β), α′ = α/g, β′ = β/g and $\Delta=\alpha'^2-\beta'^2q_1q_2$.
- (P0) $q_1,q_2,p_t,D_w$ are SP, and $q_1,q_2,p_t$ are > 0 at X = Y = 1, hence > 0 on the closed region.
- (Pg) g has positive content and every irreducible factor of g is SP.
- (P1) For $C_0$ and $C_3$: α′ and Δ are SP.
- (P2) For $C_1$ and $C_2$: β′ and −Δ are SP.

If (P0), (Pg), (P1) and (P2) hold for n, then by Lemma 9 all four conditions hold on 1 < X < Y, so by Lemma 4 of the
previous note E is positive semidefinite on (1, ∞). This is Lemma 7(n), and Proposition 6 gives Theorem 5 for this n.

## 4. The computation

[`../lower-half/m3/verify_n.py`](../lower-half/m3/verify_n.py) rebuilds $K_1,q_1,q_2,p_t$ from the definition of $K_n$
in exact rational arithmetic (python-flint), forms $C_0,\dots,C_3$ by the formulas of Lemma 8, and checks (P0), (Pg),
(P1) and (P2). The choice between (P1) and (P2) is fixed in advance for each condition, not read off from samples. It
prints the degree and the number of terms of every polynomial it proves SP, and a SHA-256 digest of these polynomials.

All obligations hold for every n ∈ 𝒩 (logs `verify_n{n}.log`). The largest polynomial is always the Δ of $C_3$:

| n | variables | largest polynomial: degree, terms | time (s) | n | variables | largest polynomial: degree, terms | time (s) |
|---|---|---|---|---|---|---|---|
| 1 | cube roots | 16, 114 | 0.0 | 24 | s, t | 268, 34064 | 3.3 |
| 2 | cube roots | 48, 1089 | 0.0 | 25 | cube roots | 872, 361608 | 908 |
| 3 | s, t | 16, 114 | 0.0 | 26 | cube roots | 908, 392074 | 1258 |
| 4 | cube roots | 116, 6414 | 0.1 | 27 | s, t | 304, 43842 | 5.8 |
| 5 | cube roots | 152, 11008 | 0.3 | 28 | cube roots | 980, 456702 | 1767 |
| 6 | s, t | 52, 1268 | 0.0 | 29 | cube roots | 1016, 490864 | 1866 |
| 7 | cube roots | 224, 23892 | 1.6 | 30 | s, t | 340, 54852 | 9.1 |
| 8 | cube roots | 260, 32182 | 2.9 | 31 | cube roots | 1088, 562884 | 2986 |
| 9 | s, t | 88, 3654 | 0.0 | 32 | cube roots | 1124, 600742 | 3981 |
| 10 | cube roots | 332, 52458 | 8.3 | 33 | s, t | 376, 67094 | 14 |
| 11 | cube roots | 368, 64444 | 13 | 34 | cube roots | 1196, 680154 | 5323 |
| 12 | s, t | 124, 7272 | 0.2 | 35 | cube roots | 1232, 721708 | 5929 |
| 13 | cube roots | 440, 92112 | 29 | 36 | s, t | 412, 80568 | 22 |
| 14 | cube roots | 476, 107794 | 44 | 39 | s, t | 448, 95274 | 33 |
| 15 | s, t | 160, 12122 | 0.4 | 42 | s, t | 484, 111212 | 50 |
| 16 | cube roots | 548, 142854 | 91 | 45 | s, t | 520, 128382 | 64 |
| 17 | cube roots | 584, 162232 | 128 | 48 | s, t | 556, 146784 | 85 |
| 18 | s, t | 196, 18204 | 1.0 | 51 | s, t | 592, 166418 | 128 |
| 19 | cube roots | 656, 204684 | 298 | 54 | s, t | 628, 187284 | 166 |
| 20 | cube roots | 692, 227758 | 313 | 57 | s, t | 664, 209382 | 231 |
| 21 | s, t | 232, 25518 | 1.8 | 60 | s, t | 700, 232712 | 360 |
| 22 | cube roots | 764, 277602 | 603 | 63 | s, t | 736, 257274 | 466 |
| 23 | cube roots | 800, 304372 | 801 | 66 | s, t | 772, 283068 | 661 |

The cases n > 36 with 3 ∤ n, and n > 66, were not run; the cost grows quickly when 3 does not divide n (about 99 minutes for n = 35).

**n = 3 explicitly.** For n = 3 all polynomials are small, and
[`../lower-half/m3/show_n3.log`](../lower-half/m3/show_n3.log) prints them in full. For example
$q_1=(u+v+5)/10$, $q_2=(5u+v+5)/10$, $p_t=(4u+5)/10$, and the Δ of $C_0$ is
$\tfrac4{25}u^6+\tfrac{12}{25}u^5v+\tfrac{63}{100}u^4v^2+\tfrac25u^3v^3+\tfrac1{10}u^2v^4+\tfrac25u^5+u^4v+\tfrac{11}{10}u^3v^2+\tfrac25u^2v^3+\tfrac14u^4+\tfrac12u^3v+\tfrac12u^2v^2$.
This gives a second proof of Theorem 1 of the previous note, with no rational parametrisation and no discriminant.

## 5. Why the averaging matters, and what the method does not give

- For (3, 3) the single-word version fails (Section 3 of the previous note), so there the averaging over words is
  essential. The certificate uses the average through Lemma 2 of the previous note.
- Each n is a separate computation. The polynomials depend on n in an essential way (degrees about 10n when 3 divides
  n, and about 30n otherwise), so the coefficient argument does not extend to all n by itself.

## 6. Checks

All checks are internal; none is an external referee report. Scripts and logs are in
[`../lower-half/m3/`](../lower-half/m3/README.md).

1. **Reproducibility.** Rerunning `verify_n.py` for n = 4, 9, 30, 63 and 66 reproduced the logs exactly, including the
   SHA-256 digests of the proved polynomials (for n = 63 and 66: `verify_n63_rerun.log`, `verify_n66_rerun.log`).
2. **The conditions against direct differentiation**
   ([`crosscheck_conditions.py`](../lower-half/m3/crosscheck_conditions.py), `crosscheck.log`). For n = 3, …, 9 the
   polynomial conditions $C_0,\dots,C_3$ agree with the stated positive multiples of F, $F_X$, $F_Y$, $F_{XY}$ computed
   by 60-digit numerical differentiation of F built from the definitions with real powers. The largest relative
   mismatch is of order $10^{-56}$.
3. **End to end** ([`endtoend_check.py`](../lower-half/m3/endtoend_check.py), `endtoend.log`, 40 digits). For random A
   with 3 to 6 distinct eigenvalues and random B, the identity $\mathcal A_{n,3}-\operatorname{Tr}((A^{n/3}B)^3)=
   \Phi(K_n)=3\sum_l\langle R^{(l)},G^{(l)}\rangle$ holds to $10^{-37}$, and every certificate matrix $G^{(l)}$ is
   positive semidefinite, for n = 3, …, 8, 10, 12, 15.
4. **A second implementation** ([`second-check/sympy_verify.py`](../lower-half/m3/second-check/sympy_verify.py)),
   written separately and using sympy instead of python-flint. It builds the four conditions directly from the
   quotient rule for F and checks the same obligations. It confirms n = 3 and n = 6, with the same polynomial degrees
   as `verify_n.py`.
5. **The exact polynomials against the definitions**
   ([`second-check/verify_polys_vs_direct.py`](../lower-half/m3/second-check/verify_polys_vs_direct.py),
   `second-check/verify_polys_vs_direct.log`). The pairs $C_0,\dots,C_3$ that `verify_n.py` itself proves SP were
   evaluated at random points and compared with the claimed multiples of F, $F_X$, $F_Y$, $F_{XY}$ computed straight
   from the definitions (real powers, numerical differentiation at 80 digits). They agree to $10^{-74}$ for
   n = 4, 5, 6 and 7, and to at least $10^{-65}$ for every other n ∈ 𝒩 up to 24 and for 27, …, 60, including the cube-root variables. (For
   n = 25, 26, 28, 29, 31, 32, 34, 35, 63 and 66, whose exact checks take 8 to 99 minutes each, this comparison was
   not repeated; for 31, 32, 34, 35, 63 and 66 see item 6.)
   (`second-check/verify_polys_vs_direct_all.log`).
6. **Direct sign checks** ([`second-check/direct_signs.py`](../lower-half/m3/second-check/direct_signs.py)). F and
   its derivatives were evaluated straight from the definitions, with no polynomial algebra, at 60 digits (and at 250
   digits for n ≥ 30, where 60 digits lose the small values of F far from the diagonal). Points were taken
   log-uniformly with 1 < s < t < 10⁴, near the diagonal and near s = 1. No sign violation was found for n = 3, 4, 5,
   7, 11, 17, 24, 36 and 60, nor at 250 digits for n = 31, 32, 34, 35, 63 and 66
   (`second-check/direct_signs_new_250digits.log`, `second-check/direct_signs_35_66_250digits.log`).

## 7. Open, and priority

- **Open.** Conjecture F, and (LH), at (n, 3) for every n (only n ∈ 𝒩 is proved); and every (n, m) with
  min(n, m) ≥ 4 other than (4,6), (6,4) and the cases (n, 4), (4, n) of [`06-lower-half-m4.md`](06-lower-half-m4.md).
- **Priority.** The search of Section 5.2 of the previous note (2026-10-08 and 2026-10-09) found no source that proves
  the lower bound at any (n, m) beyond n = m = 1 and commuting pairs, and no source for $\mathcal A_{n,m}\ge
  \operatorname{Tr}(A^{n/m}B)^m$ at these (n, m). This is not a guarantee of novelty.

## 8. Files

[`../lower-half/m3/`](../lower-half/m3/README.md) contains `verify_n.py` with the logs `verify_n{n}.log` for every
n ∈ 𝒩, the cross-checks of Section 6 with their logs, and the second implementation and direct checks in
`second-check/`.
