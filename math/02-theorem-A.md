# Theorem A: the pinched two-variable BMV identity

This note proves the identity behind [`01-pinching-theorem.md`](01-pinching-theorem.md): an explicit integral formula
for the difference between $\operatorname{Tr}e^{ag-tP}$ and its pinched version, with a nonnegative density.

**Credits.**
- For P with simple spectrum the formula is the explicit BMV measure of O. Heinävaara's PhD thesis (Princeton 2024,
  Section 1.4, proof of Theorem 24(1)).
- The split into atoms and a density, with atoms given by the pinching, goes back to H. Stahl's proof of the BMV
  conjecture (Acta Math. 211 (2013), Lemma 1 and Theorem 2).
- For orthogonal projections P the identity is Theorem D of our OQP 27 paper (github.com/anshM123/IQOQI-OQP-27,
  `papers/math/main.tex`). That theorem is formalized in Lean there. The remark with LaTeX label `rem:RIgeneralB` in that
  paper states the general case.
- The proof below follows the projection case. Two lemmas are needed beyond it: high-frequency averaging (Lemma 4, a
  special case of the strong-coupling limit of Burgarth, Facchi, Nakazato, Pascazio and Yuasa, Quantum 3, 152 (2019))
  and Lemma 5, a classical fact about exponential polynomials. Together they remove the singular parts on the interior
  lines.
- **Lean.** The identity for Hermitian P with spectrum in [0, 1] has a separate machine-checked proof by a different
  route, the multi-line Radon identity (`theoremA` in our Lean development, standard axioms only). General P follows
  by the affine rescaling of [`01-pinching-theorem.md`](01-pinching-theorem.md), Step 0, which is not formalized. The
  distributional proof written below is not the one formalized.

## 1. Statement

Let g and P be Hermitian M × M matrices. Let $p_1<\dots<p_r$ be the distinct eigenvalues of P and $Q_1,\dots,Q_r$
its spectral projections. Put:
- $g_d=\sum_kQ_kgQ_k$ (the pinching of g onto the eigenspaces of P);
- $\ell_{\min}\le\ell_{\max}$ for the extreme eigenvalues of g;
- $K=[\ell_{\min},\ell_{\max}]\times[p_1,p_r]$.

For $s\in\mathbb R$ and $\tau\notin\operatorname{spec}P$ let $\xi_1(s,\tau),\dots,\xi_M(s,\tau)$ be the roots of
$\xi\mapsto\det(g-s-\xi(P-\tau))$ (a polynomial of degree M), and put

$$\rho(s,\tau)=\frac1{2\pi}\sum_{i=1}^M|\operatorname{Im}\xi_i(s,\tau)|,$$

with $\rho:=0$ on the null set $\{\tau\in\operatorname{spec}P\}$.

**Theorem A.**
1. ρ ≥ 0. It is continuous on $\Omega=\mathbb R\times(\mathbb R\setminus\operatorname{spec}P)$ and vanishes outside
   $(\ell_{\min},\ell_{\max})\times(p_1,p_r)$.
2. For every $\tau\notin\operatorname{spec}P$,

   $$\int_{\mathbb R}\rho(s,\tau)\,ds=\mu(\tau):=\sum_{j<k}\frac{\|Q_jgQ_k\|_F^2}{p_k-p_j}\,\mathbf 1[p_j<\tau<p_k].$$

   Hence $\rho\in L^1(\mathbb R^2)$, with total mass $\sum_{j<k}\|Q_jgQ_k\|_F^2=\tfrac12\|g-g_d\|_F^2$.
3. For all $(a,t)\in\mathbb C^2$,

   $$\mathcal D(a,t):=\operatorname{Tr}e^{ag-tP}-\sum_{k=1}^re^{-tp_k}\operatorname{Tr}_{Q_k}e^{aQ_kgQ_k}=a^2\iint e^{as-t\tau}\rho(s,\tau)\,ds\,d\tau .$$

   The subtracted sum equals $\operatorname{Tr}e^{ag_d-tP}$.

At a = 1 this is Stahl's theorem (formerly the BMV conjecture) with an explicit split into atoms and a positive
density. Positivity of the density in **both** variables is what [`01-pinching-theorem.md`](01-pinching-theorem.md)
uses.

## 2. Lemmas

**Lemma 1 (the pencil).** Fix $s\in\mathbb R$ and $\tau\notin\operatorname{spec}P$. Put $p(\xi)=\det(g-s-\xi(P-\tau))$
and $q(\xi)=\det(g_d-s-\xi(P-\tau))$.
1. p and q have degree M, the same leading coefficient $c_\tau=\det(\tau-P)\ne0$, and the same sum of roots.
2. Every root ξ of p or q satisfies $|\xi|\le\|g-s\|/\operatorname{dist}(\tau,\operatorname{spec}P)$.
3. If $s\le\ell_{\min}$, $s\ge\ell_{\max}$, $\tau<p_1$ or $\tau>p_r$, all roots of p are real.
4. All roots of q are real.
5. The roots of p depend continuously on $(s,\tau)\in\Omega$.
6. If $p_k<\tau<p_{k+1}$ are consecutive eigenvalues of P, every non-real root ξ of p satisfies
   $|\xi|\le\|g-s\|/\sqrt{(\tau-p_k)(p_{k+1}-\tau)}$.

*Proof.*
1. $p(\xi)=c_\tau\det(\xi-(P-\tau)^{-1}(g-s))$, so the roots are the eigenvalues of $(P-\tau)^{-1}(g-s)$. Their sum
   is $\operatorname{Tr}[(P-\tau)^{-1}(g-s)]=\sum_k(p_k-\tau)^{-1}\operatorname{Tr}(Q_k(g-s))$. The same holds for q
   with $g_d$, and $\operatorname{Tr}(Q_kg)=\operatorname{Tr}(Q_kg_d)$.
2. A root ξ has a unit vector v with $(g-s)v=\xi(P-\tau)v$, and $\|(P-\tau)v\|\ge\operatorname{dist}(\tau,\operatorname{spec}P)$.
   For q use $\|g_d-s\|\le\|g-s\|$.
3. If $\operatorname{Im}\xi\ne0$, then $\langle v,(g-s)v\rangle=\xi\langle v,(P-\tau)v\rangle$ with both inner products
   real, so both vanish.
   - If g − s is semidefinite, this forces (g − s)v = 0, hence (P − τ)v = 0, which is impossible.
   - If P − τ is definite, $\langle v,(P-\tau)v\rangle=0$ is already impossible.
4. $g_d-s-\xi(P-\tau)$ is the direct sum over k of $Q_kgQ_k-s-\xi(p_k-\tau)$ on $\operatorname{ran}Q_k$. It is singular
   exactly when $\xi=(\mu-s)/(p_k-\tau)$ for an eigenvalue μ of $Q_kgQ_k$, which is real.
5. The coefficients are polynomials in (s, τ), and the leading coefficient does not vanish on Ω.
6. Write $w_j=\|Q_jv\|^2$ and $d_j=p_j-\tau$.
   - As in (3), $\sum_jd_jw_j=0$. Also $\sum_jw_j=1$.
   - No $p_j$ lies strictly between $p_k$ and $p_{k+1}$, so $(d_j-d_k)(d_j-d_{k+1})\ge0$, i.e.
     $d_j^2\ge(d_k+d_{k+1})d_j-d_kd_{k+1}$.
   - Multiplying by $w_j$ and summing gives
     $\|(P-\tau)v\|^2=\sum_jd_j^2w_j\ge-d_kd_{k+1}=(\tau-p_k)(p_{k+1}-\tau)$.
   - Finally $|\xi|\,\|(P-\tau)v\|=\|(g-s)v\|\le\|g-s\|$. ∎

By (6), $\rho(s,\tau)\le\frac{M}{2\pi}\,\|g-s\|/\sqrt{(\tau-p_k)(p_{k+1}-\tau)}$ on each gap. So
$\sup_s\rho(s,\cdot)$ is integrable and $\rho\in L^1$. Statement 1 of Theorem A follows from (3) and (5).

**Lemma 2 (a Jensen-type identity).** Let $p(\xi)=c\prod_{i=1}^M(\xi-\xi_i)$ and $q(\xi)=c\prod_{i=1}^M(\xi-y_i)$
with c ≠ 0, all $y_i$ real, and $\sum_i\xi_i=\sum_iy_i$. Then $\log|p/q|\in L^1(\mathbb R)$ and

$$\int_{\mathbb R}\log\Bigl|\frac{p(\xi)}{q(\xi)}\Bigr|\,d\xi=\pi\sum_{i=1}^M|\operatorname{Im}\xi_i| .$$

*Proof.* Write $\xi_i=\alpha_i+i\beta_i$, and split $\log|p/q|=A+C$ with
$A(\xi)=\frac12\sum_i\log(1+\beta_i^2/(\xi-\alpha_i)^2)\ge0$ and $C(\xi)=\sum_i[\log|\xi-\alpha_i|-\log|\xi-y_i|]$.
- **The A part.** $\int_{\mathbb R}\frac12\log(1+b^2/u^2)\,du=\pi|b|$, because $v\log(1+v^{-2})+2\arctan v$ is an
  antiderivative of $\log(1+v^{-2})$, with limits 0 at 0 and π at ∞.
- **The C part.** C has only logarithmic singularities, and $C(\xi)=O(\xi^{-2})$ at infinity because
  $\sum\alpha_i=\sum y_i$. So $C\in L^1$.
- **Its integral.** For $L>\max(|\alpha_i|,|y_i|)$ and $|a|<L$,
  $m_L(a)=\int_{-L}^L\log|\xi-a|\,d\xi=m_L(0)+a^2/L+O(a^4/L^3)$. Hence
  $\int_{-L}^LC=\sum_i(\alpha_i^2-y_i^2)/L+O(L^{-3})\to0$. ∎

**Lemma 3 (real slices).** For $\xi\in\mathbb R$:
- let $\lambda_j(\xi)$ be the eigenvalues of $g-\xi P$, and $\lambda^0_j(\xi)$ those of $g_d-\xi P$, both nondecreasing;
- let $U_\xi(w)=\sum_j[(w-\lambda_j)_+-(w-\lambda^0_j)_+]$ and $n_\xi=U_\xi'$.

Then:
1. $U_\xi$ is continuous, piecewise linear and compactly supported, and $n_\xi$ is bounded with compact support.
2. For $a\ne0$, $\int e^{aw}U_\xi(w)\,dw=a^{-2}\mathcal D(a,a\xi)$.
3. Off the eigenvalues, $(\mathcal Hn_\xi)(w)=\frac1\pi\log|\det(g-\xi P-w)/\det(g_d-\xi P-w)|$, where
   $\mathcal Hf(w)=\frac1\pi\,\mathrm{p.v.}\int f(u)/(w-u)\,du$.

*Proof.*
1. $U_\xi$ vanishes below all eigenvalues, and above them it equals $\operatorname{Tr}(g_d-\xi P)-\operatorname{Tr}(g-\xi P)=0$.
2. $U_\xi''=\sum_j(\delta_{\lambda_j}-\delta_{\lambda^0_j})$, so two integrations by parts give
   $a^{-2}\sum_j(e^{a\lambda_j}-e^{a\lambda^0_j})=a^{-2}[\operatorname{Tr}e^{a(g-\xi P)}-\sum_ke^{-a\xi p_k}\operatorname{Tr}_{Q_k}e^{aQ_kgQ_k}]$.
3. Pair $\lambda_j$ with $\lambda^0_j$. Each difference of indicators is ± the indicator of an interval, and
   $\frac1\pi\int_\alpha^\beta\frac{du}{w-u}=\frac1\pi\log|\frac{w-\alpha}{w-\beta}|$. ∎

**Lemma 4 (high-frequency averaging).** Let X be any M × M matrix, P Hermitian with distinct eigenvalues $p_k$ and
spectral projections $Q_k$, and $X_d=\sum_kQ_kXQ_k$. Then, as θ → ±∞,

$$\operatorname{Tr}e^{X-i\theta P}=\sum_ke^{-i\theta p_k}\operatorname{Tr}_{Q_k}e^{Q_kXQ_k}+O(1/|\theta|).$$

*Proof.* If P has only one eigenvalue there is nothing to prove, so let it have $r\ge2$ distinct eigenvalues. For
$0\le\sigma\le1$ let $Y(\sigma)=e^{i\theta\sigma P}e^{\sigma(X-i\theta P)}$. Then $Y'=X(\sigma)Y$ and Y(0) = 1, with

$$X(\sigma)=e^{i\theta\sigma P}Xe^{-i\theta\sigma P}=X_d+X_o(\sigma),\qquad X_o(\sigma)=\sum_{j\ne k}e^{i\theta\sigma(p_j-p_k)}Q_jXQ_k .$$

- **Antiderivative.** $X_o=Z'$ with
  $Z(\sigma)=\sum_{j\ne k}\frac{e^{i\theta\sigma(p_j-p_k)}}{i\theta(p_j-p_k)}Q_jXQ_k$, and
  $\|Z(\sigma)\|\le r^2\|X\|/(|\theta|\delta)$, where δ > 0 is the smallest gap between eigenvalues of P.
- **Duhamel and integration by parts.** By Duhamel, $Y(1)-e^{X_d}=\int_0^1e^{(1-u)X_d}X_o(u)Y(u)\,du$. Integrating
  by parts with $X_o=Z'$ bounds this by $O(\|Z\|)$, with constants depending on $\|X\|$ only.
- **Conclusion.** Hence $\operatorname{Tr}e^{X-i\theta P}=\operatorname{Tr}(e^{-i\theta P}Y(1))=\operatorname{Tr}(e^{-i\theta P}e^{X_d})+O(1/|\theta|)$.
  ∎

Applied to $X=ag-cP$ with real a, c, this gives $\mathcal D(a,c+i\theta)=O(1/|\theta|)$.

**Lemma 5 (exponential polynomials).** If $f(\theta)=\sum_{k=1}^re^{-i\theta p_k}\pi_k(\theta)$, with distinct real
$p_k$ and polynomials $\pi_k$, tends to 0 as θ → +∞, then every $\pi_k=0$.

*Proof.*
- Otherwise let n be the top degree among the nonzero $\pi_k$, and $c_k$ the coefficients of $\theta^n$.
- Then $T(\theta)=\sum_kc_ke^{-i\theta p_k}=f(\theta)/\theta^n+O(1/\theta)\to0$.
- But $\frac1L\int_L^{2L}|T|^2\to\sum_k|c_k|^2>0$, a contradiction. ∎

## 3. Proof of Theorem A

**Step 0 ($\mathcal D/a^2$ is entire).** $\mathcal D$ is entire on $\mathbb C^2$.
- At a = 0, $e^{-tP}=\sum_ke^{-tp_k}Q_k$ gives $\mathcal D(0,t)=0$.
- $\partial_a\mathcal D(0,t)=\sum_ke^{-tp_k}[\operatorname{Tr}(Q_kg)-\operatorname{Tr}(Q_kgQ_k)]=0$.
- Hence $\mathcal G:=\mathcal D/a^2=\int_0^1(1-u)\,\partial_a^2\mathcal D(ua,t)\,du$ is entire.

**Step 1 (a distribution supported in K).** For $\zeta\in\mathbb C^2$ put $(a,t)=(-i\zeta_1,i\zeta_2)$ and
$\eta=\operatorname{Im}\zeta$.
- The Hermitian part of $X=ag-tP$ is $\eta_1g+\eta_2P$. So
  $|\operatorname{Tr}e^X|\le Me^{\lambda_{\max}(\eta_1g+\eta_2P)}\le Me^{H_K(\eta)}$, where $H_K$ is the support
  function of K; note $(\langle v,gv\rangle,\langle v,Pv\rangle)\in K$ for unit v.
- Each pinched term is bounded by $\operatorname{rank}(Q_k)\,e^{H_K(\eta)}$, because $(\mu,p_k)\in K$ for every
  eigenvalue μ of $Q_kgQ_k$.
- Near $\zeta_1=0$, the maximum principle in $\zeta_1$ on a disc of radius 2 bounds $\mathcal G$ by the same
  exponential times a constant.
- So $|\mathcal G(-i\zeta_1,i\zeta_2)|\le Ce^{H_K(\operatorname{Im}\zeta)}$.
- By the Paley–Wiener–Schwartz theorem (Hörmander, Thm 7.3.1) there is a distribution Θ, supported in K, with
  $\Theta(e^{as-t\tau})=\mathcal G(a,t)$ for all $(a,t)\in\mathbb C^2$. Its Fourier transform is bounded on $\mathbb R^2$.

**Step 2 (Θ = ρ on Ω).** Let $\varphi\in C_c^\infty(\Omega)$.
- **Polar substitution.** Write $\Theta(\varphi)=(2\pi)^{-2}\int\hat{\mathcal G}(k)\hat\varphi(-k)\,dk$, and substitute
  $k=(\sigma,-\sigma\xi)$ (Jacobian |σ|).
- **Slices.** For fixed ξ, Lemma 3(2) identifies $\hat{\mathcal G}(\sigma,-\sigma\xi)$ with $\hat U_\xi(\sigma)$, and
  $|\sigma|\hat U_\xi=(\mathcal Hn_\xi)^\wedge$.
- **Parseval and Lemma 3(3).** Since $g-\xi P-(s-\xi\tau)=g-s-\xi(P-\tau)$, these give

  $$\Theta(\varphi)=\frac1{2\pi^2}\int_{\mathbb R}d\xi\iint\varphi(s,\tau)\log\Bigl|\frac{p_{s,\tau}(\xi)}{q_{s,\tau}(\xi)}\Bigr|\,ds\,d\tau .$$

- **Fubini and Lemma 2.**
  - On supp φ, $\operatorname{dist}(\tau,\operatorname{spec}P)\ge\varepsilon>0$, so by Lemma 1(2) all roots lie in a fixed
    disc of radius R.
  - By Lemma 1(1),(4) the two polynomials have the same leading coefficient and root sum, and q has real roots.
  - The integrand is bounded by an integrable function on $|\xi|\le2R$, and by $2MR^2/\xi^2$ for $|\xi|>2R$.
  - So Fubini applies, and Lemma 2 gives $\Theta(\varphi)=\iint\varphi\rho$.

**Step 3 (the τ-marginal).** By Duhamel,

$$\partial_a^2\operatorname{Tr}e^{ag-tP}\big|_{a=0}=\int_0^1\operatorname{Tr}\bigl(ge^{-\theta tP}ge^{-(1-\theta)tP}\bigr)d\theta=\sum_{j,k}\|Q_jgQ_k\|_F^2\int_0^1e^{-t(\theta p_j+(1-\theta)p_k)}d\theta .$$

- **The Laplace transform at a = 0.** The terms with j = k are cancelled by the pinched sum. So
  $\mathcal G(0,t)=\sum_{j<k}\frac{\|Q_jgQ_k\|_F^2}{p_k-p_j}\int_{p_j}^{p_k}e^{-t\tau}d\tau=\int e^{-t\tau}\mu(\tau)\,d\tau$.
- **The τ-marginal of Θ.** Let χ be in $C_c^\infty$ with χ = 1 near $[\ell_{\min},\ell_{\max}]$. The marginal
  $\psi\mapsto\Theta(\chi\otimes\psi)$ has Laplace transform $\mathcal G(0,t)$, so it equals $\mu(\tau)d\tau$.
- **Slices of ρ.** For ψ supported off spec P, Step 2 gives $\int\psi(\tau)\int\rho(s,\tau)\,ds\,d\tau=\int\psi\mu$.
  Both sides are continuous there, which proves statement 2 of Theorem A.

**Step 4 (no singular part on the lines τ = p_k).**
- **Structure.** $T:=\Theta-\rho$ is supported on the segments $[\ell_{\min},\ell_{\max}]\times\{p_k\}$. By the structure
  theorem for distributions supported on a hyperplane (Hörmander, Thm 2.3.5),
  $T=\sum_k\sum_{j\le N}\alpha_{k,j}\otimes\delta^{(j)}(\tau-p_k)$. Hence
  $\mathcal G(a,t)-\iint e^{as-t\tau}\rho=\sum_ke^{-tp_k}\sum_jt^jA_{k,j}(a)$, with $A_{k,j}$ entire.
- **High frequencies.** Fix real a ≠ 0 and real c, and put t = c + iθ.
  - The left side tends to 0 as |θ| → ∞: $\mathcal G$ by Lemma 4, and the ρ term by Riemann–Lebesgue.
  - The right side is an exponential polynomial in θ with distinct frequencies.
- **Conclusion.** By Lemma 5 every $A_{k,j}(a)=0$ for real a ≠ 0, so they vanish identically.
- Thus Θ = ρ, and $\mathcal G(a,t)=\iint e^{as-t\tau}\rho$ for all (a, t). This is statement 3. ∎

## 4. Numerical checks

The moment content of the identity for (g, P) = (B, A) was checked to high precision in the independent check
(`../independent-check/scripts/c2_quad_D1*.log`). That is the gap identity of
[`01-pinching-theorem.md`](01-pinching-theorem.md), Theorem 1, for up to 66 moments per configuration. It agrees to 28–39
significant digits in 8 configurations. The slice formula of Step 3 agrees to better than 1e-26 relative in the same
runs. Lower-precision quadrature checks at individual points (a, t) were also made during development; we do not
quote them because their logs were not kept.
