# The lower half of OQP 40: the cases (3,3), (3,4), (4,3), (4,4), (4,6) and (6,4)

**Status (2026-10-09).** For positive definite matrices of every size, the lower half of OQP 40 holds at
(n, m) = (3,3), (3,4), (4,3), (4,4), (4,6) and (6,4). It is still open in general.
- **(3,3)** is Theorem 1. The proof is elementary: an explicit certificate, plus the positivity of three explicit
  functions of two variables. It does not use Stahl's theorem.
- **The other five cases** follow from exact rational sum-of-squares certificates (Theorem 2).
- **Checks.** Both parts were checked internally, with independently written code (Section 5.1). They have not been
  refereed externally.

This note continues [`03-lower-half.md`](03-lower-half.md) and uses its notation:
- $\mathcal A_{n,m}(A,B)$ is the average of $\operatorname{Tr}W$ over the $\binom{n+m}{n}$ words W with n letters A
  and m letters B. OQP 40 calls it $p_{n,m}$.
- $L_{n,m}(A,B)=\operatorname{Tr}\exp(n\log A+m\log B)$. The lower half is (LH): $\mathcal A_{n,m}\ge L_{n,m}$.
- $F_{n,m}(A,B)=\operatorname{Tr}(A^{n/m}B)^m$. **Conjecture F** is $\mathcal A_{n,m}\ge F_{n,m}$. By Lemma 2.1 of
  03-lower-half.md (Araki–Lieb–Thirring and the Lie–Trotter formula), Conjecture F implies (LH). The version with the
  letters exchanged, $\mathcal A_{n,m}(A,B)\ge\operatorname{Tr}(AB^{m/n})^n$, implies (LH) too.

## 1. Results

**Theorem 1 ((n, m) = (3, 3) in every dimension).** For all positive definite A, B of any size d,

$$\operatorname{Tr}(A^3B^3)+2\operatorname{Re}\operatorname{Tr}(A^2BAB^2)\ \ge\ 3\operatorname{Tr}\bigl((AB)^3\bigr).\tag{1.1}$$

Equivalently $\mathcal A_{3,3}(A,B)\ge\operatorname{Tr}((AB)^3)$. Hence

$$\mathcal A_{3,3}(A,B)\ \ge\ \operatorname{Tr}\bigl((AB)^3\bigr)\ \ge\ \operatorname{Tr}\exp(3\log A+3\log B),$$

which is the (3,3) case of the lower half.
- (3,3) is the smallest case with min(n, m) ≥ 3.
- By continuity, (1.1) also holds for positive semidefinite A, B (Section 2.6).
- The averaging over words is essential: the single-word inequality
  $\operatorname{Re}\operatorname{Tr}(A^2BAB^2)\ge\operatorname{Tr}((AB)^3)$ is false, even in sign (Section 3).

**Theorem 2 (sum-of-squares certificates).** For all positive semidefinite A, B of any size:
- **(4,4):** $\mathcal A_{4,4}(A,B)\ge p^{\rm mult}_{4,4}(A,B)\ge\operatorname{Tr}((AB)^4)$;
- **(3,4):** $\mathcal A_{3,4}(A,B)\ge p^{\rm mult}_{3,4}(A,B)\ge\operatorname{Tr}((A^{3/4}B)^4)$;
- **(6,4):** $\mathcal A_{6,4}(A,B)\ge\operatorname{Tr}((A^{3/2}B)^4)$.

Here $p^{\rm mult}_{n,m}$ is the intermediate quantity of 03-lower-half.md, §2.4. In terms of words,
$p^{\rm mult}_{n,m}(A,B)=m^{-n}\sum_{J\in[m]^n}\operatorname{Tr}\prod_{j=1}^mBA^{N_j(J)}$, where
$N_j(J)=\#\{l:J_l=j\}$.

**Corollary 3.** For positive definite A, B of every size, (LH) holds at (4,4), (3,4), (4,3), (6,4) and (4,6).

*Proof.*
- **(4,4), (3,4), (6,4).** Theorem 2 gives Conjecture F there. Lemma 2.1 of 03-lower-half.md finishes.
- **(4,3), (4,6).** Exchange the letters: $\mathcal A_{n,m}(A,B)=\mathcal A_{m,n}(B,A)$. So
  $\mathcal A_{4,3}(A,B)=\mathcal A_{3,4}(B,A)\ge\operatorname{Tr}((B^{3/4}A)^4)=\operatorname{Tr}((AB^{3/4})^4)$, and
  $\mathcal A_{4,6}(A,B)\ge\operatorname{Tr}((AB^{3/2})^4)$ in the same way. The second part of Lemma 2.1 of
  03-lower-half.md gives $\operatorname{Tr}(AB^{m/n})^n\ge L_{n,m}$. ∎

**What is not claimed.**
- Conjecture F itself at (4,3) and (4,6), that is, $\mathcal A_{4,3}\ge\operatorname{Tr}(A^{4/3}B)^3$ and
  $\mathcal A_{4,6}\ge\operatorname{Tr}(A^{2/3}B)^6$, is not proved. Only the versions with the letters exchanged are.
- At (6,4) the two intermediate steps through $p^{\rm mult}_{6,4}$ are not proved.
- All other cases with min(n, m) ≥ 3, for example (3,5) and (5,5), remain open.

## 2. Proof of Theorem 1

Let A, B be positive definite and put

$$f(A,B)=\operatorname{Tr}(A^3B^3)+2\operatorname{Re}\operatorname{Tr}(A^2BAB^2)-3\operatorname{Tr}\bigl((AB)^3\bigr).$$

The proof uses linear algebra and the positivity of three explicit functions of two variables (Section 2.5).

### 2.1 Reduction to a kernel

**Word classes.**
- The 20 words with three letters A and three letters B fall into four rotation classes: AAABBB, AABABB, AABBAB and
  ABABAB, of sizes 6, 6, 6 and 2. Rotation does not change the trace.
- For Hermitian A, B the trace of the reversed word is the complex conjugate. AABBAB is a rotation of the reversal of
  AABABB. Hence

$$20\,\mathcal A_{3,3}=6\operatorname{Tr}(A^3B^3)+12\operatorname{Re}\operatorname{Tr}(A^2BAB^2)+2\operatorname{Tr}\bigl((AB)^3\bigr),\qquad
\mathcal A_{3,3}-\operatorname{Tr}\bigl((AB)^3\bigr)=\tfrac3{10}\,f.$$

**Letters.** Let $A=\sum_{k=1}^r\alpha_kQ_k$, with distinct eigenvalues $\alpha_k>0$, spectral projections $Q_k$ and any
multiplicities. Put $W_k=B^{1/2}Q_kB^{1/2}\ge0$ and

$$T(i,j,k)=\operatorname{Tr}(BQ_iBQ_jBQ_k)=\operatorname{Tr}(W_iW_jW_k).$$

T is invariant under rotation of (i, j, k), and reversing (i, j, k) conjugates it.

**Kernel.**
- Read cyclically from a letter B, a word is $BA^{c_1}BA^{c_2}BA^{c_3}$, where $c$ is a weak composition of 3 into
  three parts. Inserting $A^c=\sum_k\alpha_k^cQ_k$ gives

  $$\operatorname{Tr}(BA^{c_1}BA^{c_2}BA^{c_3})=\sum_{i,j,k}T(i,j,k)\,\alpha_i^{c_1}\alpha_j^{c_2}\alpha_k^{c_3}.$$

- Each of the 10 compositions arises from exactly six pairs (word, chosen letter B). So $\mathcal A_{3,3}$ is the
  average of these traces over the 10 compositions. This is the cycle expansion of 03-lower-half.md, §2.4.
- The sum of $x^{c_1}y^{c_2}z^{c_3}$ over all compositions is the complete homogeneous polynomial
  $h_3(x,y,z)=(x+y+z)(x^2+y^2+z^2)+xyz$. Hence
  $\mathcal A_{3,3}=\frac1{10}\sum_{i,j,k}T(i,j,k)\,h_3(\alpha_i,\alpha_j,\alpha_k)$. The composition (1, 1, 1) gives
  $\operatorname{Tr}((AB)^3)=\sum_{i,j,k}T(i,j,k)\,\alpha_i\alpha_j\alpha_k$.
- Subtracting, $\mathcal A_{3,3}-\operatorname{Tr}((AB)^3)=\Phi(\kappa)/10$. With the word classes above, this gives

$$f=\tfrac13\,\Phi(\kappa),\qquad \Phi(\kappa):=\sum_{i,j,k=1}^rT(i,j,k)\,\kappa(\alpha_i,\alpha_j,\alpha_k),\qquad
\kappa(x,y,z)=h_3-10xyz=(x+y+z)(x^2+y^2+z^2)-9xyz.$$

**Facts about κ.**
- κ is symmetric and homogeneous of degree 3, $\kappa(x,x,x)=0$, and $\kappa(x,y,y)=(x-y)^2(x+4y)$.
- **Apex identity.** Direct expansion gives

  $$\kappa(x,y,z)=s_x+s_y+s_z,\qquad s_l=(a-l)(b-l)(l+2a+2b),\tag{2.1}$$

  where {a, b} are the two points other than l. For x < y < z, $s_x>0$, $s_z>0$ and $s_y<0$.

### 2.2 Apex shares

**Lemma 2.** Let K be a real symmetric function on $(0,\infty)^3$ with $K(x,x,x)=0$. Suppose that for every
l ∈ [r] there is a real symmetric matrix $G^{(l)}$, indexed by [r] ∖ {l}, such that
- $G^{(l)}_{aa}=K(\alpha_l,\alpha_a,\alpha_a)$;
- for every 3-element set {i, j, k} ⊂ [r], the **share identity** holds:
  $G^{(i)}_{jk}+G^{(j)}_{ik}+G^{(k)}_{ij}=K(\alpha_i,\alpha_j,\alpha_k)$;
- each $G^{(l)}$ is positive semidefinite.

Put $R^{(l)}_{ab}=\operatorname{Re}T(l,a,b)$ for a, b ≠ l. Then

$$\Phi(K):=\sum_{i,j,k}T(i,j,k)\,K(\alpha_i,\alpha_j,\alpha_k)=3\sum_{l=1}^r\langle R^{(l)},G^{(l)}\rangle\ \ge\ 0.$$

*Proof.*
- **Sorting the index triples.** Triples with three equal entries contribute 0.
  - A multiset {l, a, a} with l ≠ a gives three triples, all with the trace $T(l,a,a)=\operatorname{Tr}(W_lW_a^2)$.
  - A set {i, j, k} of three distinct indices gives six triples: three with trace T(i, j, k) and three with its
    complex conjugate.

  Hence

  $$\Phi(K)=3\sum_{l\ne a}\operatorname{Tr}(W_lW_a^2)\,K(\alpha_l,\alpha_a,\alpha_a)
  +6\sum_{\{i,j,k\}}\operatorname{Re}T(i,j,k)\,K(\alpha_i,\alpha_j,\alpha_k).$$

- **$R^{(l)}$ is positive semidefinite.** For real y, put $Y=\sum_{a\ne l}y_aW_a$, which is Hermitian. Then
  $y^TR^{(l)}y=\operatorname{Re}\operatorname{Tr}(W_lY^2)=\operatorname{Tr}(YW_lY)\ge0$.
- **Pairing.** $R^{(l)}_{aa}=\operatorname{Tr}(W_lW_a^2)$. For distinct i, j, k, rotation and conjugation show that
  $\operatorname{Re}T(i,j,k)$ is the matching off-diagonal entry of each of $R^{(i)}$, $R^{(j)}$ and $R^{(k)}$. In
  $\langle R^{(l)},G^{(l)}\rangle$ each off-diagonal pair is counted twice. With the diagonal condition and the share
  identity, $\sum_l\langle R^{(l)},G^{(l)}\rangle=\Phi(K)/3$.
- **Sign.** The trace inner product of two positive semidefinite matrices is ≥ 0. ∎

With K = κ, Lemma 2 gives $f=\Phi(\kappa)/3=\sum_l\langle R^{(l)},G^{(l)}\rangle$. If r ≤ 2 there are no 3-element
sets, and each $G^{(l)}$ is empty or the 1 × 1 matrix $[\kappa(\alpha_l,\alpha_a,\alpha_a)]$, which is ≥ 0. So
Theorem 1 holds when A has at most two distinct eigenvalues. For r ≥ 3 we now construct the matrices $G^{(l)}$.

### 2.3 The certificate

For x < y < z put

$$\operatorname{cap}_z(x,y)=(z-x)(z-y)\sqrt{(z+4x)(z+4y)},\qquad E_x(y,z)=E_x(z,y)=\kappa(x,y,z)-\operatorname{cap}_z(x,y),$$

and $E_x(y,y)=\kappa(x,y,y)=(y-x)^2(x+4y)$. This diagonal value is the limit of $E_x(y,z)$ as z → y, because
$\operatorname{cap}_y(x,y)=0$.

**Assignment.** Split the value of κ on each triple $\alpha_i<\alpha_j<\alpha_k$ among its three points:
- the largest point gets $G^{(k)}_{ij}=\operatorname{cap}_{\alpha_k}(\alpha_i,\alpha_j)$;
- the smallest point gets $G^{(i)}_{jk}=E_{\alpha_i}(\alpha_j,\alpha_k)$;
- the middle point gets $G^{(j)}_{ik}=0$.

The diagonal entries are $G^{(l)}_{aa}=\kappa(\alpha_l,\alpha_a,\alpha_a)$. The share identity holds by construction.

**Structure of $G^{(l)}$.** Split the indices a ≠ l into those below l ($\alpha_a<\alpha_l$) and those above l
($\alpha_a>\alpha_l$). Then $G^{(l)}$ is block diagonal:
- **Below block.** For a, a' below l, l is the largest point of {a, a', l}. So $G^{(l)}_{aa'}=u(a)u(a')$ with
  $u(a)=(\alpha_l-\alpha_a)\sqrt{\alpha_l+4\alpha_a}$. The diagonal is $(\alpha_l-\alpha_a)^2(\alpha_l+4\alpha_a)=u(a)^2$.
  So this block is $uu^T$, which is positive semidefinite.
- **Cross entries.** For a below l and b above l, l is the middle point, so the entry is 0.
- **Above block.** For b, b' above l, l is the smallest point. So the entries are
  $E_{\alpha_l}(\alpha_b,\alpha_{b'})$, including the diagonal.

By Lemma 2, Theorem 1 follows once every above block is positive semidefinite. This is Lemma 3.

### 2.4 The kernel $E_s$

**Lemma 3.** For every s > 0, $(b,c)\mapsto E_s(b,c)$ is a positive semidefinite kernel on (s, ∞). That is, for any
distinct points $b_1,\dots,b_k>s$, the matrix $[E_s(b_i,b_j)]$ is positive semidefinite.

*Proof.*
- **Scaling.** κ and cap are homogeneous of degree 3, so $E_s(b,c)=s^3E_1(b/s,c/s)$. Take s = 1.
- **Formula.** Write b = 1 + B and c = 1 + C with 0 < B ≤ C, and put $P=\sqrt{C+5}$ and $Q=\sqrt{C+4B+5}$.
  - By (2.1) applied to the points 1, b, c: $s_1+s_b=B^2(B+3C+5)$ and $s_c=C(C-B)(C+2B+5)$.
  - Also $\operatorname{cap}_c(1,b)=C(C-B)PQ$. Since $P^2+Q^2=2(C+2B+5)$ and $Q^2-P^2=4B$,
    $s_c-\operatorname{cap}_c(1,b)=C(C-B)(P-Q)^2/2=8B^2C(C-B)/(P+Q)^2$.
  - Hence

    $$E_1(b,c)=B^2C\,G(B,C),\qquad G(B,C)=3+\frac{B+5}{C}+\frac{8(C-B)}{(P+Q)^2}.$$

  - At B = C this gives $B^3(4+5/B)=B^2(4B+5)=E_1(b,b)$, so the formula also covers the diagonal.
- **Factorisation.** For B ≤ C, $E_1(b,c)=w(B)\,w(C)\,F(B,C)$ with $w(B)=B^{3/2}$ and $F(B,C)=\sqrt{B/C}\;G(B,C)$.
- **Conclusion.** Lemma 4 below, applied on the interval (0, ∞) of the variable B, shows that the kernel is positive
  semidefinite. Its hypotheses are verified in Section 2.5. ∎

### 2.5 Interval mixtures and the conditions (I)–(III)

**Lemma 4 (interval mixtures).** Let I be an interval, w > 0 a function on I, and F a function on
{(s, t) ∈ I² : s ≤ t} such that
- F ≥ 0;
- F is nondecreasing in s and nonincreasing in t;
- $F(s,t)-F(s',t)-F(s,t')+F(s',t')\ge0$ whenever s' ≤ s ≤ t ≤ t' in I.

Then $K(x,y)=w(x)\,w(y)\,F(\min(x,y),\max(x,y))$ is a positive semidefinite kernel on I.

*Proof.* Take $x_1<\dots<x_k$ in I. Set $F(x_0,\cdot)=0$ and $F(\cdot,x_{k+1})=0$, and for 1 ≤ p ≤ q ≤ k put

$$\mu_{pq}=F(x_p,x_q)-F(x_{p-1},x_q)-F(x_p,x_{q+1})+F(x_{p-1},x_{q+1}).$$

- $\mu_{pq}\ge0$. For 1 < p ≤ q < k this is the rectangle inequality. For p = 1 and q < k it is monotonicity in t,
  and for p > 1 and q = k it is monotonicity in s. Finally $\mu_{1k}=F(x_1,x_k)\ge0$.
- Telescoping gives $F(x_i,x_j)=\sum_{p\le i,\ q\ge j}\mu_{pq}$ for i ≤ j.
- Hence $K(x_i,x_j)=\sum_{p\le q}\mu_{pq}\,v_{pq}(i)\,v_{pq}(j)$ with $v_{pq}(i)=w(x_i)\,\mathbf 1[p\le i\le q]$. This is
  a nonnegative combination of rank-one positive semidefinite matrices. ∎

Lemma 4 is elementary, and we do not claim that it is new. Each term is a kernel of the form
$u(\min(x,y))\,v(\max(x,y))$. Kernels of this form are classical; for example, they are the covariances of
Gauss–Markov processes.

**Smooth version.** Suppose F is C² on an open set containing {s ≤ t}. Then the hypotheses of Lemma 4 follow from
F ≥ 0, $F_s\ge0$, $F_t\le0$ and $F_{st}\le0$ on {s ≤ t}:
- monotonicity holds along segments in {s ≤ t};
- $F(s,t)-F(s',t)-F(s,t')+F(s',t')=-\int_{s'}^{s}\int_t^{t'}F_{st}\ge0$, because the rectangle $[s',s]\times[t,t']$
  lies in {s ≤ t}.

Our F is real-analytic on $(0,\infty)^2$, hence C² across the diagonal. Its diagonal values are the ones Lemma 4
uses, since $w(B)^2F(B,B)=E_1(b,b)$.

**The conditions.** For $F=\sqrt{B/C}\;G$,

$$F_B=\tfrac12B^{-1/2}C^{-1/2}\,(G+2BG_B),\qquad F_C=\tfrac12B^{1/2}C^{-3/2}\,(2CG_C-G),$$

$$F_{BC}=\tfrac14B^{-1/2}C^{-3/2}\,(-G-2BG_B+2CG_C+4BCG_{BC}).$$

On {B ≤ C} we have G ≥ 3, so F > 0. It therefore suffices that, for all B, C > 0,

$$\text{(I)}\ \ G+2BG_B\ge0,\qquad \text{(II)}\ \ G-2CG_C\ge0,\qquad \text{(III)}\ \ G+2BG_B-2CG_C-4BCG_{BC}\ge0.$$

**Closed forms.** Put $h=(P+Q)^{-2}$. From $P_B=0$, $P_C=1/(2P)$, $Q_B=2/Q$ and $Q_C=1/(2Q)$:

$$h_B=-\frac{4}{Q(P+Q)^3},\qquad h_C=-\frac{h}{PQ},\qquad h_{BC}=\frac{2P+6Q}{PQ^3(P+Q)^3},$$

$$G_B=\frac1C+8\bigl(-h+(C-B)h_B\bigr),\qquad G_C=-\frac{B+5}{C^2}+8\bigl(h+(C-B)h_C\bigr),\qquad
G_{BC}=-\frac1{C^2}+8\bigl(-h_C+h_B+(C-B)h_{BC}\bigr).$$

Clearing denominators and reducing with $P^2=C+5$ and $Q^2=C+4B+5$ gives

$$\text{(I)}=\frac{4\,(a_1+d_1PQ)}{C\,Q\,(P+Q)^3},\qquad
\text{(II)}=\frac{2\,(a_2+d_2PQ)}{C\,P\,Q\,(P+Q)^2},\qquad
\text{(III)}=\frac{4\,(a_3P+d_3Q)}{C\,P\,Q^3\,(P+Q)^3},$$

where
- $a_1=12B^3+19B^2C+95B^2+4BC^2+100BC+200B+5C^3+45C^2+125C+125$,
- $d_1=9B^2+6BC+30B+5C^2+20C+25$,
- $a_2=12B^2C+60B^2+7BC^2+150BC+375B+11C^3+45C^2+225C+375$,
- $d_2=6B^2+5BC+45B-C^2+30C+75$,
- $a_3=144B^4+232B^3C+1320B^3+121B^2C^2+1370B^2C+3825B^2+18BC^3+420BC^2+2550BC+4500B+5C^4+60C^3+400C^2+1500C+1875$,
- $d_3=108B^3C+540B^3+75B^2C^2+870B^2C+2475B^2-28BC^3+290BC^2+2100BC+3750B+5C^4+60C^3+400C^2+1500C+1875$.

All denominators are positive.

**Positivity.**
- **(I).** Every coefficient of $a_1$ and $d_1$ is positive, so (I) > 0.
- **(II) and (III).** Use the rational parametrisation $C=p^2-5$, $B=(q^2-p^2)/4$, so that P = p and Q = q. Here
  $p>\sqrt5$, and $q=p+v$ with v ≥ 0. Write $x=p^2>5$ and $y=x-5>0$. Then

  $$\text{(II)}=\frac{N_{\rm II}}{4pq(p+q)^2(p^2-5)},\qquad \text{(III)}=\frac{N_{\rm III}}{4pq^3(p+q)^2(p^2-5)},$$

  $$N_{\rm II}=3pv^5+21p^2v^4+2p(29x+20)v^3+40(2x^2+7x-10)v^2+40p(x-2)(x+20)v+80\,c(x),$$

  $$N_{\rm III}=9pv^7+81xv^6+p(301x+40)v^5+35x(17x+8)v^4+2p^3(343x+340)v^3+c_2v^2+c_1v+c_0,$$

  with $c(x)=x^3-8x^2+50x-100=y^3+7y^2+45y+75$, $c_2=40(7x^3+85x^2-290x+400)=40(7y^3+190y^2+1085y+1950)$,
  $c_1=-40p(x^3-86x^2+320x-400)$ and $c_0=80x\,c(x)$.
  - Every coefficient of $N_{\rm II}$ is positive for x > 5; note $2x^2+7x-10=2y^2+27y+75$. So (II) > 0.
  - In $N_{\rm III}$ every coefficient except $c_1$ is positive, and $c_1<0$ for x > 82.16. But $c_2>0$ and

    $$4c_0c_2-c_1^2=1600x\,(55y^6+2054y^5+17729y^4+84580y^3+280425y^2+585750y+489375)>0,$$

    so $c_0+c_1v+c_2v^2>0$ for every v. Hence (III) > 0.
  - The same substitution gives (I) $=N_{\rm I}/(4q(p+q)^2(p^2-5))$ with
    $N_{\rm I}=3v^5+21pv^4+58p^2v^3+80p^3v^2+40(x^2+6x-20)v+80p\bigl((x-3)^2+1\bigr)$, again with positive
    coefficients.
- **A second route for (III).** $a_3$ has positive coefficients. If $d_3\ge0$ there is nothing to prove. If $d_3<0$,
  then $a_3P+d_3Q=(a_3^2P^2-d_3^2Q^2)/(a_3P-d_3Q)$, and $a_3^2(C+5)-d_3^2(C+4B+5)=4B\,H(B,C)$, where H is a polynomial
  of degree 8 with 41 terms, all with positive coefficients.

So (I)–(III) hold for all B, C > 0, Lemma 4 applies, and Lemma 3 and Theorem 1 follow.

These are finite symbolic computations. The scripts in [`../lower-half/thm33/`](../lower-half/thm33/) print
$N_{\rm I}$, $N_{\rm II}$, $N_{\rm III}$ and the discriminant. The closed forms were also derived separately, by direct
differentiation in (B, C), and (I)–(III) were proved a second time by verified interval arithmetic (Section 5.1).

### 2.6 The last step, and semidefinite matrices

- **The exponential bound.** Lemma 2.1 of 03-lower-half.md with n = m = 3 gives
  $\operatorname{Tr}((AB)^3)=F_{3,3}(A,B)\ge L_{3,3}(A,B)$. It uses the Araki–Lieb–Thirring inequality and the
  Lie–Trotter product formula (see, for example, R. Bhatia, *Matrix Analysis*, Springer, 1997, Chapter IX). With
  Theorem 1 this gives the (3,3) case of (LH).
- **Semidefinite A, B.** (1.1) and $\mathcal A_{3,3}\ge\operatorname{Tr}((AB)^3)$ hold by continuity. For the
  exponential bound, define $L_{3,3}(A,B)$ as the limit of $L_{3,3}(A+\varepsilon,B+\varepsilon)$ as ε ↓ 0. The limit
  exists, because log is operator monotone and $\operatorname{Tr}\exp$ is monotone, so the expression decreases as
  ε decreases. The inequality passes to the limit.

## 3. The averaging over words is essential

**A single-word counterexample.** Take

$$A=\operatorname{diag}(1,\ 10^5,\ 9\cdot10^5),\qquad
B=\begin{pmatrix}130001&1400&-100\\ 1400&50&28\\ -100&28&26\end{pmatrix}.$$

Both are positive definite; the leading principal minors of B are 130001, 4540050 and 7780516. Exact integer
arithmetic gives
- $\operatorname{Tr}(A^2BAB^2)=-28461367246374197639999<0$;
- $\operatorname{Tr}((AB)^3)=18951153147665700390001>0$;
- $f(A,B)=1197318687168261817498300000>0$.

So the single-word inequality $\operatorname{Re}\operatorname{Tr}(A^2BAB^2)\ge\operatorname{Tr}((AB)^3)$ fails, even in
sign, while Theorem 1 holds.

- **In terms of gaps.** Put $D=\operatorname{Tr}(A^3B^3)-\operatorname{Tr}((AB)^3)$, which is ≥ 0 by the
  Araki–Lieb–Thirring inequality, and $E=\operatorname{Re}\operatorname{Tr}(A^2BAB^2)-\operatorname{Tr}((AB)^3)$. Then
  f = D + 2E. Theorem 1 says E ≥ −D/2. The single-word inequality would say E ≥ 0.
- **How the example works.** Let A have eigenvalues 0, y, z with spectral projections $ee^\ast$, $Q_y$, $Q_z$, and
  put $u=B^{1/2}e$, $W_y=B^{1/2}Q_yB^{1/2}$, $W_z=B^{1/2}Q_zB^{1/2}$. Then
  $\operatorname{Re}\operatorname{Tr}(A^2BAB^2)=\langle u,Hu\rangle+(\text{terms without }u)$, with
  $H=y^3W_y^2+z^3W_z^2+\tfrac12yz(y+z)(W_yW_z+W_zW_y)$. H is indefinite when, for example, y ≠ z and $W_y$, $W_z$ have
  rank one and make a small angle. A long u in a negative direction of H then makes the trace negative. The example
  above is a positive definite instance of this.

**Relation to the literature.**
- **Furuichi, Kuriyama and Yanagi**, *Trace inequalities for products of matrices*, Linear Algebra Appl. 430 (2009)
  2271–2276, arXiv:1001.1384.
  - Their Theorem 2.2: for 2 × 2 positive semidefinite T, A and positive $p_1,\dots,p_m$ with sum 1,
    $\operatorname{Tr}[(T^{1/m}A)^m]\le\operatorname{Tr}[T^{p_1}AT^{p_2}A\cdots T^{p_m}A]\le\operatorname{Tr}[TA^m]$.
  - Take T = A³, the letter B in place of their A, m = 3, and let $(p_1,p_2,p_3)\to(2/3,1/3,0)$ (continuity, for
    positive definite T). This gives $\operatorname{Tr}((AB)^3)\le\operatorname{Tr}(A^2BAB^2)\le\operatorname{Tr}(A^3B^3)$
    for 2 × 2 matrices, hence Theorem 1 for d = 2. (The case d = 2 also follows from Proposition 2.4 of
    03-lower-half.md.) In the same way, with T = Aⁿ, their Theorem 2.2 gives every single-word bound
    $\operatorname{Tr}W\ge F_{n,m}(A,B)$ for d = 2.
  - Their Conjecture 2.8(i) asks for the left inequality, with Re Tr, for n × n matrices. It would imply Theorem 1 in
    every dimension (add the Araki–Lieb–Thirring inequality $\operatorname{Tr}(A^3B^3)\ge\operatorname{Tr}((AB)^3)$).
    But by the same limit it would also imply the single-word inequality, so the example above shows that Conjecture
    2.8(i) fails for 3 × 3 matrices and three factors (by continuity, also for some positive exponents near
    (2/3, 1/3, 0)). We claim no novelty for this remark; we have not surveyed later work on these conjectures.
- **Ando, Hiai and Okubo**, Math. Inequal. Appl. 3 (2000) 307–318, question (1.7), asked whether
  $\operatorname{Tr}((A^{1/K}B^{1/K})^K)\le|\operatorname{Tr}(A^{p_1}B^{q_1}\cdots A^{p_K}B^{q_K})|$ when
  $\sum p_i=\sum q_i=1$. Applied to A³ and B³, with K = 3 and exponents (2/3, 1/3, 0) and (1/3, 2/3, 0), it would
  give $\operatorname{Tr}((AB)^3)\le|\operatorname{Tr}(A^2BAB^2)|$. The same B with A = diag(89/10⁶, 1, 9) gives
  $\operatorname{Tr}(A^2BAB^2)/\operatorname{Tr}((AB)^3)\approx-0.00135$, so this instance fails, and by continuity
  so do nearby positive exponents. The question was already known to have a negative answer in general (A. Plevnik,
  Indian J. Pure Appl. Math. 47 (2016) 491–500; E. A. Carlen and E. H. Lieb, J. Math. Phys. 63 (2022) 062203,
  arXiv:2203.06136, Example 4.3).
- **The BMV conjecture.** Theorem 1 strengthens the case $\mathcal A_{3,3}\ge0$ of the BMV conjecture (Stahl's
  theorem). That case was known before Stahl's proof, for example from D. Hägele's proof of the cases p ≤ 7
  (arXiv:math/0702217) together with C. J. Hillar's descent theorem (arXiv:math/0507166). We found no earlier
  comparison of $\mathcal A_{3,3}$ with $\operatorname{Tr}((AB)^3)$.

## 4. The sum-of-squares certificates (Theorem 2)

### 4.1 The certificate type

**Polynomial form.** Substitute $A=X^a$ and $B=Y^b$, with $X=A^{1/a}\ge0$ and $Y=B^{1/b}\ge0$. The exponents are
chosen so that both sides become polynomials in X and Y:
- (a, b) = (2, 2) at (4,4) and (6,4), where $A^{3/2}=X^3$;
- (a, b) = (4, 2) at (3,4), where $A^{3/4}=X^3$.

Then f = (left side) − (right side) is a polynomial in the noncommuting letters X, Y with rational coefficients.

**Certificate.** A certificate is an identity

$$f(X,Y)=\sum_kc_k\operatorname{Tr}(g_k^\ast g_k)+\sum_kc'_k\operatorname{Tr}(X\,h_k^\ast X\,h_k)+\sum_kc''_k\operatorname{Tr}(Y\,l_k^\ast Y\,l_k),$$

with positive rationals $c_k,c'_k,c''_k$ and polynomials $g_k,h_k,l_k$ in X, Y with rational coefficients.
- "Identity" means that both sides have the same coefficient on every word, up to cyclic rotation. For Hermitian X, Y
  the adjoint of a word is the reversed word.
- Large certificates are stored as Gram blocks $\sum_{i,j}G_{ij}\operatorname{Tr}(P\,u_i^\ast P\,u_j)$, with
  P ∈ {1, X, Y}, words $u_i$, and $G=TST^T$, where T is an integer matrix and S an exactly positive definite rational
  matrix.

**Why each term is ≥ 0.**
- $\operatorname{Tr}(g^\ast g)=\|g\|_2^2\ge0$.
- $\operatorname{Tr}(X\,h^\ast X\,h)=\|X^{1/2}hX^{1/2}\|_2^2\ge0$, because X ≥ 0. The same holds for Y.
- A Gram block with $S=LDL^T$, D > 0 diagonal, equals $\sum_aD_a\operatorname{Tr}(P\,g_a^\ast P\,g_a)$ with
  $g_a=\sum_i(TL)_{ia}u_i$.

The identity uses only the cyclicity of the trace. So each certified inequality holds for positive semidefinite
matrices of every size, and also for positive elements of any von Neumann algebra with a tracial state.

**A small example** (the known case (4,2)):
$\mathcal A_{4,2}(A,B)-\operatorname{Tr}((A^2B)^2)=\tfrac15\|[A^2,B]\|_2^2+\tfrac15\|A^{1/2}[A,B]A^{1/2}\|_2^2$.

### 4.2 The certified statements

The files are in [`../lower-half/sos/certs/`](../lower-half/sos/certs/). In the file names, F stands for Conjecture F,
D for $\mathcal A_{n,m}\ge p^{\rm mult}_{n,m}$, and M for $p^{\rm mult}_{n,m}\ge F_{n,m}$. Ranks are listed by
localizer: (1,1) | (X,X) | (Y,Y).

| File | Statement (A, B ≥ 0, any size) | Substitution | Form |
|---|---|---|---|
| `F44_11-xx-yy.json` | $\mathcal A_{4,4}\ge\operatorname{Tr}((AB)^4)$ | A = X², B = Y² | 66 explicit terms (42 \| 12 \| 12) |
| `F44_gram.json` | the same | A = X², B = Y² | Gram blocks, ranks 23, 19 \| 6, 6 \| 6, 6 |
| `D44_11-xx-yy.json` | $\mathcal A_{4,4}\ge p^{\rm mult}_{4,4}$ | A = X², B = Y² | Gram blocks, ranks 23, 19 \| 6, 6 \| 6, 6 |
| `M44_11-xx-yy.json` | $p^{\rm mult}_{4,4}\ge\operatorname{Tr}((AB)^4)$ | A = X², B = Y² | Gram blocks, ranks 23, 19 \| 6, 6 \| 6, 6 |
| `F34m_11-xx-yy.json` | $\mathcal A_{3,4}\ge\operatorname{Tr}((A^{3/4}B)^4)$ | A = X⁴, B = Y² | Gram blocks, ranks 44, 38 \| 31, 27 \| 15, 13 |
| `D34m_11-xx-yy.json` | $\mathcal A_{3,4}\ge p^{\rm mult}_{3,4}$ | A = X⁴, B = Y² | Gram blocks, same ranks |
| `M34m_11-xx-yy.json` | $p^{\rm mult}_{3,4}\ge\operatorname{Tr}((A^{3/4}B)^4)$ | A = X⁴, B = Y² | Gram blocks, same ranks |
| `F64_11-xx-yy.json` | $\mathcal A_{6,4}\ge\operatorname{Tr}((A^{3/2}B)^4)$ | A = X², B = Y² | Gram blocks, ranks 44, 38 \| 31, 27 \| 15, 13 |
| `P44.json` | $\mathcal A_{4,4}(X^2,Y^2)\ge0$ for all Hermitian X, Y (known: a case of Stahl's theorem) | A = X², B = Y² | 50 terms, no localizers |
| `F24_11-xx-yy.json` | $\mathcal A_{2,4}\ge\operatorname{Tr}((A^{1/2}B)^4)$ (known case) | A = X², B = Y² | 20 explicit terms (11 \| 3 \| 6) |
| `F42_11-xx-yy.json` | $\mathcal A_{4,2}\ge\operatorname{Tr}((A^2B)^2)$ (known case) | A = X², B = Y² | 9 explicit terms (5 \| 3 \| 1) |

The last three files are sanity checks of the method on known cases.

### 4.3 What follows at each (n, m)

| (n, m) | Proved for A, B ≥ 0 of every size | (LH) for positive definite A, B |
|---|---|---|
| (3,3) | $\mathcal A_{3,3}\ge\operatorname{Tr}((AB)^3)$: Conjecture F (Theorem 1, not from a certificate of this type) | yes |
| (4,4) | $\mathcal A_{4,4}\ge p^{\rm mult}_{4,4}\ge\operatorname{Tr}((AB)^4)$: Conjecture F and both intermediate steps | yes |
| (3,4) | $\mathcal A_{3,4}\ge p^{\rm mult}_{3,4}\ge\operatorname{Tr}((A^{3/4}B)^4)$: Conjecture F and both intermediate steps | yes |
| (4,3) | only the version with the letters exchanged: $\mathcal A_{4,3}(A,B)\ge\operatorname{Tr}((AB^{3/4})^4)$ | yes |
| (6,4) | $\mathcal A_{6,4}\ge\operatorname{Tr}((A^{3/2}B)^4)$: Conjecture F; the intermediate steps are not certified | yes |
| (4,6) | only the version with the letters exchanged: $\mathcal A_{4,6}(A,B)\ge\operatorname{Tr}((AB^{3/2})^4)$ | yes |

### 4.4 Why (3,3) and (6,3) are out of reach of this cone

**Dual certificates.**
- Let y be a linear functional on words, invariant under rotation and reversal. It is ≥ 0 on every term of Section
  4.1 if and only if its localized moment matrices $M_P(y)_{u,v}=y(P\,\bar u\,P\,v)$ are positive semidefinite, for
  P ∈ {1, X, Y}. Here $\bar u$ is the reversed word.
- If in addition y(f) < 0, then f has no certificate.
- f is bihomogeneous in (X, Y). Comparing extreme bidegrees shows that only half-words of one fixed bidegree can
  occur in a certificate. So finite moment matrices decide the question in every degree.

**(3,3).**
- Let $y_{33}$ take the values 1, −4/3 and 2 on the classes of $A^3B^3$, of $A^2BAB^2$ (and its reversal) and of
  $(AB)^3$, and 0 on all other classes.
- Its moment matrices are 0 except for two copies of the positive definite 2 × 2 block with rows (2, −4/3) and
  (−4/3, 1).
- But $y_{33}(\mathcal A_{3,3})=\bigl(6\cdot1+12\cdot(-\tfrac43)+2\cdot2\bigr)/20=-\tfrac3{10}<0$.
- So not even $\mathcal A_{3,3}\ge0$, which is a case of Stahl's theorem and follows from Theorem 1, has a
  certificate of this type. Neither has any target $\mathcal A_{3,3}-r$ with $y_{33}(r)\ge0$, such as Conjecture F at
  (3,3). This holds for the substitutions (A, B) = (X², Y²), (X², Y⁴) and (X⁴, Y⁴).
- In words: these cones only see the Cauchy–Schwarz relation
  $|\operatorname{Tr}(A^2BAB^2)|^2\le\operatorname{Tr}(A^3B^3)\operatorname{Tr}((AB)^3)$ among the three traces, and
  that relation does not force $\mathcal A_{3,3}\ge0$.
- This matches an observation of I. Klep and M. Schweighofer (arXiv:0710.1074, Example 3.5): the BMV polynomial
  $S_{6,3}(X^2,Y^2)$, the sum of all 20 words (so $S_{6,3}=20\,\mathcal A_{3,3}$), is not cyclically equivalent to a
  sum of Hermitian squares.

**(6,3).** The same construction with A² in place of A ($y_{63}$ = 1, −4/3, 2 on $A^6B^3$, $A^4BA^2B^2$ and
$(A^2B)^3$) gives $y_{63}(\mathcal A_{6,3})=-\tfrac3{28}<0$. This was checked for the substitution (A, B) = (X², Y²).

**Without localizers** there is a simpler obstruction for odd m. Take A = X², B = Y² and n = km. Then the
alternating word $(A^kB)^m$ arises in a Gram expansion only from diagonal entries, which are ≥ 0. But its coefficient
in $\mathcal A_{n,m}-\operatorname{Tr}((A^kB)^m)$ is $(k+1)/\binom{n+m}{n}-1<0$.

The 14 non-existence certificates, all in [`../lower-half/sos/certs/`](../lower-half/sos/certs/):

| File | Target | Substitution | Localizers | Functional | y(f) |
|---|---|---|---|---|---|
| `nonSOS_F33_pureSOS.json` | $\mathcal A_{3,3}-\operatorname{Tr}((AB)^3)$ | X², Y² | 1 | indicator of $(AB)^3$ | −9/10 |
| `nonSOS_F33_QM.json` | $\mathcal A_{3,3}-\operatorname{Tr}((AB)^3)$ | X², Y² | 1, X, Y | $y_{33}$ | −23/10 |
| `nonSOS_H33_QM.json` | $\mathcal A_{3,3}-\operatorname{Tr}((A^{1/2}B^{1/2})^6)$ | X², Y² | 1, X, Y | $y_{33}$ | −3/10 |
| `nonSOS_H33_QM_Y4.json` | $\mathcal A_{3,3}-\operatorname{Tr}((A^{1/2}B^{1/2})^6)$ | X², Y⁴ | 1, X, Y | $y_{33}$ | −3/10 |
| `nonSOS_Q33_QM_X4Y4.json` | $\mathcal A_{3,3}-\operatorname{Tr}((A^{1/4}B^{1/4})^{12})$ | X⁴, Y⁴ | 1, X, Y | $y_{33}$ | −3/10 |
| `nonSOS_D33_QM.json` | $\mathcal A_{3,3}-p^{\rm mult}_{3,3}$ | X², Y² | 1, X, Y | indicator of $(AB)^3$ | −11/90 |
| `nonSOS_M33_QM.json` | $p^{\rm mult}_{3,3}-\operatorname{Tr}((AB)^3)$ | X², Y² | 1, X, Y | indicator of $(AB)^3$ | −7/9 |
| `nonSOS_P33_pureSOS.json` | $\mathcal A_{3,3}$ | X², Y² | 1 | $y_{33}$ | −3/10 |
| `nonSOS_P33_QM.json` | $\mathcal A_{3,3}$ | X², Y² | 1, X, Y | $y_{33}$ | −3/10 |
| `nonSOS_P33_QM_Y4.json` | $\mathcal A_{3,3}$ | X², Y⁴ | 1, X, Y | $y_{33}$ | −3/10 |
| `nonSOS_P33_QM_X4Y4.json` | $\mathcal A_{3,3}$ | X⁴, Y⁴ | 1, X, Y | $y_{33}$ | −3/10 |
| `nonSOS_P63_QM.json` | $\mathcal A_{6,3}$ | X², Y² | 1, X, Y | $y_{63}$ | −3/28 |
| `nonSOS_F63_QM.json` | $\mathcal A_{6,3}-\operatorname{Tr}((A^2B)^3)$ | X², Y² | 1, X, Y | $y_{63}$ | −59/28 |
| `nonSOS_S63_QM.json` | $\mathcal A_{6,3}-\operatorname{Tr}((AB^{1/2})^6)$ | X², Y² | 1, X, Y | $y_{63}$ | −3/28 |

These results exclude only certificates of the type in Section 4.1: localizers 1, X, Y and polynomial multipliers of
any degree. They do not exclude other types of certificate. Theorem 1 uses a different, non-polynomial certificate.

## 5. Status

**Status: CHECKED internally, not refereed externally.**

### 5.1 Checks

Both checks below were made on 2026-10-08 and 2026-10-09 with new code, written for the purpose and not reusing the
scripts behind the proofs. They are internal checks, not external referee reports. Scripts and logs are in
[`../lower-half/`](../lower-half/README.md). On 2026-10-09 we ran every script again from the published folders; the
outputs agree with the logs there (Section 6).

**Theorem 1** ([`../lower-half/thm33/independent-check/`](../lower-half/thm33/independent-check/)).
- **Every step re-derived** in different notation: the reduction, Lemma 2 and the positive semidefiniteness of
  $R^{(l)}$, the certificate, Lemma 3, Lemma 4, the derivative conditions and the exponential bound. No error or gap
  was found. The check's minor comments on presentation and references are taken into account in this note.
- **(I)–(III) by a different route.** Direct differentiation in (B, C) reproduces exactly the numerators
  $N_{\rm I}$, $N_{\rm II}$, $N_{\rm III}$ and every sign argument above, and gives the closed forms of Section 2.5.
- **A second proof of (I)–(III)** by verified interval arithmetic (python-flint arb, 128 bits). Two charts cover
  {0 ≤ B ≤ C, C > 0}, including the limit C → ∞. All 131 boxes have strictly positive certified lower bounds.
- **Identities** of Sections 2.1–2.3 confirmed in 256-bit ball arithmetic on 120 random instances, with 1 to 7
  distinct eigenvalues of A and multiplicities 1 to 3.
- **Lemma 3** tested directly on 400 point sets at 120 digits, including clustered and widely spread points.
- **Numerics.** f was evaluated in ball arithmetic, with every sign decided rigorously:
  - on 7,485 exactly constructed pairs with d = 2 to 30: random pairs, extreme spectra (condition numbers up to
    10¹⁶), near-commuting pairs, rank-deficient pairs, and the Cha–Lee family with shifts;
  - on 24 pairs with d = 50, 80 and 100;
  - at the minimisers of L-BFGS searches for d = 2 to 16.

  No violation was found.
- **The single-word example** of Section 3 was confirmed in exact arithmetic.

**Theorem 2** ([`../lower-half/sos/independent-check/`](../lower-half/sos/independent-check/)).
- **Targets.** Each target was rebuilt from the claimed statement, not from the file, and the file's own description
  was required to state the same target.
- **Identities.** Each identity was checked exactly over the rationals, modulo cyclic rotation only.
- **Gram blocks.** Every Gram block was shown exactly positive definite, in two ways: by an exact LDLᵀ factorization
  and by Sylvester's criterion.
- **Non-existence.** All 14 non-existence certificates were checked: the moment matrices over all half-words of the
  forced bidegree are exactly positive semidefinite, and y(f) has the stated negative value.
- **Numerics.** Each certificate was evaluated on random positive semidefinite pairs of sizes 2 to 8: 853 samples in
  all, 349 in exact rational arithmetic and 504 in ball arithmetic. Nothing failed.
- **Negative controls.** 17 tampered certificates or wrong claims behaved as expected.

Result: all 11 positive and all 14 non-existence certificates are valid. Our own verifier,
[`verify_certificate.py`](../lower-half/sos/verify_certificate.py), gives the same result.

### 5.2 Priority

We searched on 2026-10-08 and 2026-10-09.
- **The problem page.** The OQP 40 page lists only n = m = 1 (the Golden–Thompson inequality) and commuting pairs
  as known cases of the lower bound. We read it through its Internet Archive captures of 2023-10-29 and 2026-03-23,
  which have identical text. The live page returned HTTP 500 on both days.
- **The literature.** No source we read states the lower bound, or Conjecture F, at (3,3), (3,4), (4,3), (4,4),
  (4,6) or (6,4). The sources read:
  - H. Cha and J. Lee, arXiv:2603.19927 (versions 1, 3, 5 and 6);
  - google-deepmind/formal-conjectures issue #3457 and its comments;
  - T. H. Dinh, arXiv:2605.17782;
  - Furuichi–Kuriyama–Yanagi (2009) and Ando–Hiai–Okubo (2000), cited in Section 3;
  - D. Hägele, arXiv:math/0702217;
  - E. H. Lieb and R. Seiringer, arXiv:math-ph/0210027;
  - C. R. Johnson and C. J. Hillar (2002); C. J. Hillar and C. R. Johnson (2005); C. J. Hillar, arXiv:math/0507166;
  - I. Klep and M. Schweighofer, arXiv:0710.1074; S. Burgdorf, arXiv:0802.1153; P. S. Landweber and E. R. Speer,
    arXiv:0711.0672;
  - C. Fleischhack and S. Friedland, arXiv:0811.0030; F. Garbe and F. Wei, arXiv:2605.02314;
  - E. A. Carlen and E. H. Lieb, arXiv:2203.06136;
  - an arXiv search for "Bessis-Moussa-Villani", and web searches.
- **Not read:** the full text of Plevnik (2016), of which we read the abstract only; C. J. Hillar's thesis; versions
  2 and 4 of Cha–Lee.

This is not a guarantee of novelty.

## 6. Files

All scripts, certificates and logs are in [`../lower-half/`](../lower-half/README.md), with one command per log,
the requirements and the run times. Re-running every command reproduces the logs, apart from run times, date lines
and the order of files in one log (see the README there).
- `lower-half/thm33/`: the symbolic computations of Section 2.5, a numerical check of the certificate, and the
  single-word example.
- `lower-half/thm33/independent-check/`: the independent check of Theorem 1.
- `lower-half/sos/`: the 25 certificate files and our exact verifier.
- `lower-half/sos/independent-check/`: the independent check of Theorem 2.
