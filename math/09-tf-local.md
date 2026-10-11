# Conjecture TF near commuting pairs and near the identity

Ansh Mishra, Aryan Senthilkumar. 2026-10-10.

**Status.**
- **Theorem 1 (second order at commuting pairs): proved.**
  - Conjecture TF of [`08-general-lower-half-route.md`](08-general-lower-half-route.md) holds to second order at every
    generic commuting pair, in every dimension, on every ray and at every level.
  - The last step, the inequality E ≥ 0 of Section 1.5, is computer-assisted: analytic arguments plus rigorous ball
    arithmetic (Arb).
  - We re-ran the computation from the published scripts. We also tested its enclosures against independent
    high-precision code.
- **Theorem 2 (near the identity): the leading terms are proved.**
  - For A = e^{hX}, B = e^{hY} and small h, every term is explicit.
  - Inside the eigenvalue cluster, TF reduces to the Hermite–Hadamard inequality.
  - At the bottom level, the TF value is a trace of a product of two positive semidefinite matrices.
  - Uniformity across the edges of the cluster is sketched, not written out.
- **Still open:** Conjecture TF itself and the general lower half. Any proof of either must be at least as strong as
  Stahl's theorem ([`03-lower-half.md`](03-lower-half.md), Section 1).
- Nothing here has been refereed externally.

**Notation** is that of note 08:
- Z_θ = θ log A + (1−θ) log B, with eigenvalues ζ_1 ≤ … ≤ ζ_d;
- N₀ = 1/min(θ, 1−θ);
- T_θ(u) = ∫_{(u,∞)} e^{N₀v} d(μ^θ − κ^θ)(v).

TF says T_θ(u) ≥ 0 for all u. By symmetry we take θ ≤ 1/2, so N₀ = 1/θ, and we put r = (1−θ)/θ.

## 0. Three tools

**0.1 TF in terms of the Weyl distribution.**
- **The distribution Π.** Let Π = Π_{A,B} be the Weyl (Wigner) joint distribution of the pair. It is the compactly
  supported distribution on R² with ∫ e^{i(xa+yb)} dΠ = Tr e^{i(xA+yB)}, so ∫ F(xa + yb) dΠ = Tr F(xA + yB).
- **Relation to μ.** Heinävaara's measure is its radial smoothing: μ = ∫₀¹ ((1−t)/t) (D_t)_*Π dt, where
  D_t(a, b) = (ta, tb). Both sides have the same projections. For x, y ≥ 0 these are Σ_i (1/s − 1/λ_i)₊ ds, with λ_i
  the eigenvalues of xA + yB.
- **On a ray.** In the variable ℓ_θ this smoothing is convolution with k(w) = (1 − e^w)₊. So μ^θ = Π^θ * k and
  κ^θ = (Σ_i δ_{ζ_i}) * k.
- **TF in this language.** Integrating against e^{N₀v} 1[v > u] gives

  T_θ(u) = ⟨Π, g_u ∘ ℓ_θ⟩ − Tr g_u(Z_θ),  g_u(v) := 1[v > u]·[e^{N₀v} − (N₀+1)e^{N₀u} + N₀e^{(N₀+1)u−v}] / (N₀(N₀+1)).   (0.1)

  - g_u is C¹, convex and nondecreasing, and it vanishes together with its derivative at v = u.
  - Here ⟨Π, φ∘ℓ_θ⟩ := ∫ (φ'' + φ')(ℓ_θ) dμ. This is the usual pairing when φ is smooth, because
    (D² + D)e^{Nv} = N(N+1)e^{Nv} and p_{n,m} = N(N+1)∫ a^n b^m dμ.
  - So **TF says that the Weyl quantization of the convex function g_u∘ℓ_θ has a larger trace than g_u(Z_θ).**

**0.2 An exact Weyl-calculus identity.** Let S and T be Hermitian, let S have eigenvalues s_j and orthonormal
eigenvectors e_j, and put T_jk = ⟨e_j, T e_k⟩. For continuous F,

  ∫ F(s) t² dΠ_{S,T}(s, t) = Σ_{j,k} |T_jk|² ⨍_{[s_j, s_k]} F,  whereas  Tr(F(S) T²) = Σ_{j,k} |T_jk|² (F(s_j) + F(s_k))/2.

*Proof.*
- For F(s) = e^{iαs}, the left side is −∂_β² Tr e^{i(αS+βT)} at β = 0.
- By the Daleckii–Krein formula this equals Σ_{j,k} |T_jk|² (e^{iαs_j} − e^{iαs_k})/(iα(s_j − s_k)), which is the
  mean of e^{iαs} over [s_j, s_k].
- General F follows by Fourier synthesis and density. ∎

**0.3 The point N = −1 (a Kubo–Ando identity).** Let P_v = (⟨Av,v⟩, ⟨Bv,v⟩) be the pencil points of note 08, with
v the unit eigenvectors of A^{−1}B, and z_v = ℓ_θ(P_v). Then

  ∫ e^{−ℓ_θ} dΠ = Σ_v e^{−z_v} = Tr(A^{−1} #_{1−θ} B^{−1}),

where # is the Kubo–Ando weighted geometric mean.

*Proof.*
- **Analytic continuation.** For N > 0, ∫ e^{Nℓ_θ} dΠ = N(N+1) ∫ e^{Nℓ_θ} dμ, and the left side is entire in N.
  - The singular part of μ contributes Σ_v e^{Nz_v}.
  - The continuous part vanishes outside a compact subset of the open quadrant. So its contribution is N(N+1) times
    an entire function, which is 0 at N = −1.
- **Why the continuous part avoids the axes.** Write C_φ = cos φ A + sin φ B and D_φ = sin φ A − cos φ B.
  - In polar coordinates, the density of the continuous part at r(cos φ, sin φ) is a positive multiple of Σ|Im ξ|,
    the sum over the roots ξ of det(rI − C_φ − ξD_φ).
  - If rI − C_φ or D_φ is definite, all roots are real. Indeed, a non-real root with null vector w forces
    ⟨(rI − C_φ)w, w⟩ = ⟨D_φw, w⟩ = 0. This is Theorem A, Lemma 1(3).
  - D_φ is definite outside the angular range [φ_min, φ_max] of the pencil eigenvalues. rI − C_φ is definite outside
    [λ_min(C_φ), λ_max(C_φ)], and λ_min(C_φ) is bounded below by min(λ_min(A), λ_min(B)) > 0.
- **The mean.** Take A-normalised eigenvectors w_v, so that W*AW = I and W*BW = Λ = diag(λ_v). Then
  e^{−z_v} = ⟨Av,v⟩^{−θ}⟨Bv,v⟩^{−(1−θ)} = ‖w_v‖² λ_v^{−(1−θ)}. So Σ_v e^{−z_v} = Tr(WΛ^{−(1−θ)}W*).
- **Congruence.** A^{−1} = WW* and B^{−1} = WΛ^{−1}W*. By congruence covariance of the mean,
  A^{−1} #_{1−θ} B^{−1} = WΛ^{−(1−θ)}W*. ∎

The reference side at N = −1 is Tr e^{−Z_θ}. By Ando–Hiai log-majorisation the identity gives
Φ(−1) := ∫ e^{−ℓ_θ} dΠ − Tr e^{−Z_θ} ≤ 0: the lower half fails at N = −1.

## 1. Theorem 1: TF to second order at commuting pairs

**Theorem 1.** Let A and B be commuting positive definite matrices. Call the pair *generic* for θ if its joint
eigenvalues P_j = (α_j, β_j) satisfy two conditions:
- they lie on distinct rays through the origin;
- their levels ℓ_θ(P_j) are distinct.

Let H be Hermitian and B(ε) = e^{iεH} B e^{−iεH}. Then for every u ∈ R,

  T_θ(u; A, B(ε)) = ε² T₂(u) + o(ε²),  with T₂(u) ≥ 0.

For non-generic commuting pairs the same holds for the second-order coefficient against smooth test functions, by
continuity.

The proof has five steps.

**1.1 Pair decomposition.** T₂ = Σ_{j<k} |H_jk|² T₂^{(jk)}. Here T₂^{(jk)} is the same coefficient for the 2 × 2 pair
diag(α_j, α_k), diag(β_j, β_k), with B rotated by the angle ε.
- **Word side.** By the Fourier form of Π, the ε² coefficient of ⟨Π_ε, e^{i(xa+yb)}⟩ = Tr e^{i(xA+yB(ε))} comes from
  two terms:
  - the first-order Duhamel term in (iε)²[H,[H,B]]/2;
  - the second-order Duhamel term in iε[H, B].

  Both are sums over pairs j ≠ k of |H_jk|² times functions of P_j and P_k alone.
- **Reference side.** Write Z_θ(ε) = Z₀ + εZ₁ + ε²Z₂ + O(ε³), in the joint eigenbasis. The second-order coefficient
  of Tr φ(Z_θ(ε)) is
  Σ_j φ'(ζ_j)(Z₂)_jj + ½ Σ_{j≠k} |(Z₁)_jk|² (φ')^{[1]}(ζ_j, ζ_k). This is also a pair sum.
- **Conclusion.** Both sides decompose over pairs, and each pair contributes exactly its 2 × 2 problem.

**1.2 The 2 × 2 formula.**

*Lemma 1 (Bloch-sphere formula).* Let A = a₀ + a⃗·σ⃗ and B = b₀ + b⃗·σ⃗ be 2 × 2 Hermitian matrices, with σ⃗ the Pauli
vector. Then

  ⟨Π_{A,B}, F⟩ = (1/2π) ∫_{S²} (1 + r∂_r) F(a₀ + r a⃗·n, b₀ + r b⃗·n) |_{r=1} dn.

*Proof.*
- Take F(a, b) = f(xa + yb), and put c = xa₀ + yb₀ and κ⃗ = xa⃗ + yb⃗.
- Then κ̂·n is uniform on [−1, 1], so the right side is ∫₋₁¹ d/dt[t f(c + |κ⃗|t)] dt = f(c + |κ⃗|) + f(c − |κ⃗|).
  This is Tr f(xA + yB).
- A compactly supported distribution is determined by its projections. ∎

*Lemma 2 (second variation).* Let A = diag(a₁, a₂) and B(ε) = R_ε diag(b₁, b₂) R_εᵀ. Put P_i = (a_i, b_i) and
P(u) = P₂ + u(P₁ − P₂). For F ∈ C²,

  d²/dε² ⟨Π_{A,B(ε)}, F⟩ |_{ε=0} = −2 (a₁ − a₂)(b₁ − b₂) ∫₀¹ F_ab(P(u)) du.

*Proof.*
- **The perturbation.** In Lemma 1 only the b-coordinate depends on ε: it is
  b₀ + r b_z(n_z cos 2ε + n_x sin 2ε), with b_z = (b₁ − b₂)/2. Expand F to second order in ε.
- **Averaging.** Average over the circles n_z = t, using E[n_x] = 0 and E[n_x²] = (1 − t²)/2. Then apply (1 + r∂_r)
  and integrate by parts in t. With σ := b₁ − b₂, the ε² coefficient is
  −σ[F_b(P₁) − F_b(P₂)] + σ² ∫₀¹ F_bb(P(u)) du.
- **Conclusion.** F_b(P₁) − F_b(P₂) = ∫₀¹ ((a₁ − a₂)F_ab + σF_bb)(P(u)) du, so the ε² coefficient is
  −(a₁ − a₂)σ ∫₀¹ F_ab du. ∎
- **Check.** For F = ab this gives the exact ε² term of Tr(AB(ε)).

*Corollary (the 2 × 2 second-order density).*

**Normalisation.** Normalise P₂ = (1, 1) and P₁ = (e^X, e^Y), with Δ := θX + (1−θ)Y > 0. Put:
- p = e^X − 1 and q = e^Y − 1;
- A(u) = θ log(1 + up) and B(u) = (1−θ) log(1 + uq);
- ℓ = A + B, α = θX and β = (1−θ)Y.

Then for φ ∈ C²,

  lim_{ε→0} ε^{−2} [⟨Π_ε, φ∘ℓ_θ⟩ − Tr φ(Z_θ(ε))] = ∫₀¹ φ''(ℓ(u)) K(u) du,  K := (αβ/Δ) ℓ' − A'B'.

*Proof.*
- **Word side.** ℓ_θ is a function of a plus a function of b, so (φ∘ℓ_θ)_ab = θ(1−θ) φ''(ℓ_θ)/(ab). By Lemma 2,
  the word side contributes −∫ φ''(ℓ) A'B' du.
- **Reference side.** The eigenvalues of Z_θ(ε) are Δ − (αβ/Δ)ε² + O(ε⁴) and (αβ/Δ)ε² + O(ε⁴) (explicit 2 × 2
  computation). They contribute (αβ/Δ)(φ'(Δ) − φ'(0)) = (αβ/Δ) ∫ φ''(ℓ) ℓ' du. ∎

**1.3 From smooth test functions to the TF kernel.** Let ν_ε := ε^{−2}(μ^θ_ε − κ^θ_ε).
- **Bounded total variation.** For a generic pair, the total variation of μ^θ_ε − κ^θ_ε is O(ε²):
  - the levels ζ_i(ε) and the pencil levels z_v(ε) move by O(ε²), and at ε = 0 they coincide;
  - the continuous part has mass −2 log|det V_ε| = O(ε²) (note 08, Lemma 2).
- **Weak convergence.** By 1.1–1.2, ν_ε converges against smooth test functions to ν₂ := ν_K * k''. Here
  ν_K := ℓ_*(K du) is absolutely continuous, so ν₂ is too. With the total-variation bound, ν_ε therefore also converges
  against the function e^{N₀v} 1[v > u], which has a single jump.
- **The limit.** Using (0.1),

  T₂(u) = ∫₀¹ w_u(ℓ(t)) K(t) dt,  w_u := g_u'' = 1[v > u] (N₀e^{N₀v} + e^{(N₀+1)u−v})/(N₀+1).

- **Check.** In the 2 × 2 case we checked Lemma 2 directly with the Bloch-sphere formula, including for the TF kernel
  itself (`tf-local/second-order/bloch_kernel_check.py`).

**1.4 Reduction to the level of the lower point.**
- **The density.** Let k̃ be the density of ν_K := ℓ_*(K du), summed over the branches of ℓ. ℓ is concave, with
  ℓ(0) = 0 and ℓ(1) = Δ, so ν_K lives on [0, v_max], where v_max = max ℓ.
- **Lemma A.** On (0, v_max), k̃ is nondecreasing and its jumps are upward.
  - **One branch** (ℓ monotone). Then k̃ = αβ/Δ − 1/(1/A' + 1/B'), and 1/A' + 1/B' is affine in u with slope
    1/(θ(1−θ)) > 0.
  - **Two branches** (an interior maximum at u*). On each branch, |ℓ'|/|A'B'| is affine with the right sign, so each
    branch density increases in v. The second branch starts at v = Δ with the value K(1)/|ℓ'(1)| > 0.
- **Lemma B.** The density of ν₂ is f₂ = k̃ − Ek̃, where (Ek̃)(t) = ∫_t^∞ e^{t−v} k̃(v) dv. Moreover
  (e^{−t}f₂)' = e^{−t}k̃' (because k'' = δ − e^w 1[w<0]).
- **Shape of T₂.** As a function of the level t = u, T₂(t) = ∫_t^∞ e^{N₀s} f₂(s) ds behaves as follows:
  - **Below 0:** f₂ = −e^t (Ek̃)(0) has constant sign, so T₂ is monotone on (−∞, 0]. Its limit at −∞ is the
    second-order Golden–Thompson gap, which is ≥ 0 by Chebyshev's covariance inequality.
  - **On (0, v_max):** e^{−t}f₂ is nondecreasing, so f₂ changes sign at most once, from − to +. As t decreases from
    v_max, T₂ first increases and then decreases. So on [0, v_max], T₂ ≥ min(T₂(0), T₂(v_max)) = min(T₂(0), 0).
  - **Above v_max:** T₂ vanishes.
- **Hence** T₂ ≥ 0 everywhere if and only if E := (N₀+1) T₂(0) ≥ 0.

**1.5 The inequality E ≥ 0 (computer-assisted).**
- **The closed form.** In the coordinates x = X, y = rY, s = x + y = Δ/θ,
  - E = θ[xy(e^s − 1)/s − (e^x − 1)(e^y − 1)] + θxy(1 − e^{−θs})/s
    + pq/(p−q)² [(1−θ)p(e^{θ(Y−X)} − 1) + θq(e^{(1−θ)(X−Y)} − 1)].
  - The first bracket is the Golden–Thompson part, ≥ 0 by Chebyshev's covariance inequality.
  - It comes from E = ∫₀¹ [N₀e^{N₀ℓ} + e^{−ℓ}] K du (that is, (N₀+1)T₂(0)) by integrating term by term. N₀θ = 1
    makes the first part elementary. The p, q-term equals −θ(1−θ)pq ∫₀¹ (1+up)^{−1−θ}(1+uq)^{−2+θ} du.
- **Statement.** E(θ, X, Y) ≥ 0 for all θ ∈ (0, 1/2] and all real X, Y with Δ ≥ 0, with equality exactly when XY = 0.
- **Proof structure.** Write E = θx²y²H, with H = g − tm. Here g = Cov(e^{xU}, e^{yU})/(xy) is positive and
  increasing in x and in y, and tm is the remaining term.
  - **Boundary s = 0 (analytic).** There H has a closed form, decreasing in θ by log-convexity of (e^z − 1)/z. So
    H(θ, x, −x) ≥ H(1/2, x, −x) = (2 sinh²t + tanh²t − 3t²)/(8t⁴) > 0, with t = x/2.
  - **The square |x|, |y| ≤ 10 (rigorous ball arithmetic).** Every box is certified either to have H > 0 or to have
    ∂H/∂s > 0 at fixed (θ, x − y). Integrating down to s = 0 then gives H ≥ 0.
    - Near the degenerate corner (θ, x, y) = (1/2, 0, 0) we use Taylor models: degree-15 polynomials whose
      coefficients come from samples on a torus, with maximum-principle (Cauchy) error bounds. 318 boxes, all
      certified.
    - Elsewhere we use interval arithmetic with monotone enclosures and adaptive bisection. 167,626 boxes, 0 failures.
  - **Far region max(x, y) ≥ 10 (analytic).** Explicit bounds give tm < g there.
  - **Coverage.** A script checks it mechanically.
- **Our checks.**
  - We re-ran all runs from the published scripts; the results matched.
  - Independent mpmath code confirms the analytic identities to 57–61 digits.
  - In random tests, no certified enclosure was violated.
- Details are in [`../lower-half/tf-local/E-proof/PROOF.md`](../lower-half/tf-local/E-proof/PROOF.md).

**Remark (the tight corner).** H(θ, 0, 0) = (1+θ)(1−2θ)/(12(1−θ)), which vanishes at θ = 1/2. So near
(θ, x, y) = (1/2, 0, 0), E is small to higher order than x²y². This corner is why the derivative test (dH/ds > 0) is
needed there. The same degeneracy appears near the identity, in Theorem 2.3 below, with an explicit positive next
term.

## 2. Theorem 2: near the identity

**Setting.**
- X and Y are Hermitian, A = e^{hX} and B = e^{hY}, with h → 0.
- S := θX + (1−θ)Y, so Z_θ = hS **exactly**. Its eigenvalues are s_1 ≤ … ≤ s_d, with eigenvectors e_j.
- T := X − Y, T_jk := ⟨e_j, Te_k⟩, κ := ‖[X, Y]‖_F² and K := −[X, Y]² ≥ 0. Note [S, T] = −[X, Y].

**Theorem 2.**
1. **Word averages.** For integers n, m ≥ 0,
   p_{n,m}(A, B) − L_{n,m}(A, B) = (h⁴/24)·nm(n+m−1)·κ + O(h⁵).
   More generally, Φ(N) := ∫ e^{Nℓ_θ} dΠ − Tr e^{NZ_θ} = (θ(1−θ)κh⁴/24)·N²(N−1) + O(h⁵) for every real N, locally
   uniformly. The integer case is N = n + m, θ = n/N.
2. **Interior of the cluster.** For every γ ∈ R, T_θ(hγ) = h³ τ(γ) + O(h⁴), uniformly in γ, where

   τ(γ) = (θ(1−θ)/2) Σ_{j<k, s_j<s_k} |T_jk|² (s_k − γ)₊(γ − s_j)₊/(s_k − s_j) ≥ 0.

3. **Bottom level.**
   - For θ < 1/2: T_θ(ζ_1) = (h⁴/24)(1−θ)(1−2θ)κ + O(h⁵) > 0.
   - At θ = 1/2 this leading term vanishes, and T_θ(ζ_1) = (h⁵/48)·Tr((S − s_1 I)K) + O(h⁶) ≥ 0.

*Proof of 1.* Write σ := Π^θ − Σ_i δ_{ζ_i}, with moments M_j := ∫ v^j dσ, so that Φ(N) = Σ_j N^j M_j/j!.
- **Low moments.** M₀ = M₁ = 0 exactly: ridge functions integrate exactly, and ∫ log a dΠ = Tr log A.
- **Rescaling.** By affine covariance, Π_{A,B} is the image of Π_{X_h,Y_h}, where X_h = (e^{hX} − I)/h. Expanding
  ℓ_θ/h = s − (h/2)(θx² + (1−θ)y²) + O(h²), Tool 0.2 gives:
  - M₃ = (h⁴/4)θ(1−θ)κ + O(h⁵);
  - M_j = O(h⁵) for j ≥ 4.
- **The second moment.** M₂ = 2θ(1−θ)[∫ log a log b dΠ − Tr(log A log B)].
  - For f, g smooth (Π lives near (1, 1)), ∫ f(a)g(b) dΠ − Tr f(A)g(B) = (1/24) f''(1)g''(1) Tr[A, B]² + O(h⁵). This uses
    Tr e^{P+Q} − Tr e^Pe^Q = (1/24) Tr[P, Q]² + … with P = iαA and Q = iβB, then Fourier synthesis.
  - Hence M₂ = −(h⁴/12)θ(1−θ)κ + O(h⁵).
- **Conclusion.** Φ(N) = (θ(1−θ)κh⁴/24)·N²(N−1) + O(h⁵) on every ray, and θ(1−θ)N² = nm. ∎

*Proof of 2.*
- **The kernel.** At the level u = hγ, g_u(hw) = e^{N₀hγ}[h²(w−γ)₊²/2 + O(h³)] (uniformly).
- **The deviation.** By the rescaling above and Tool 0.2, applied with F = φ',
  ∫ φ(ℓ_θ/h) dΠ − Tr φ(S) = (h/2)θ(1−θ) Σ_{j,k} |T_jk|² [(φ'(s_j) + φ'(s_k))/2 − ⨍_{[s_j,s_k]} φ'] + O(h²).
  This uses the operator identity θX² + (1−θ)Y² = S² + θ(1−θ)T².
- **Hermite–Hadamard.** With φ(w) = (w−γ)₊²/2 we have φ' = (w−γ)₊, which is convex. So each bracket is a trapezoid
  value minus a mean value, which is ≥ 0. On [s_j, s_k] it equals (s_k − γ)₊(γ − s_j)₊/(2(s_k − s_j)). ∎
- **Link with Theorem A.** Away from the eigenvalues, −τ'' = θ(1−θ)·μ_{T,S}, where
  μ_{T,S}(γ) = Σ_{j<k} |T_jk|²/(s_k − s_j)·1[s_j < γ < s_k] is the marginal of Theorem A
  ([`02-theorem-A.md`](02-theorem-A.md)) for g = X − Y and P = S. So near the identity, the TF tail is θ(1−θ) times
  the potential of Theorem A's pair marginal.

*Proof of 3.*
- **The bottom formula.**
  - Π lives on the joint numerical range W, since its projections live between the extreme eigenvalues of xA + yB.
    On W we have ℓ_θ ≥ ζ_1 (Jensen: log⟨Au,u⟩ ≥ ⟨log A u,u⟩). So
    σ lives on [ζ_1, ∞).
  - There, for u ≤ ζ_1, g_u is a combination of e^{N₀v}, 1 and e^{−v}. Since Φ(0) = 0,
    T_θ(u) = [Φ(N₀) + N₀e^{(N₀+1)u}Φ(−1)]/(N₀(N₀+1)) for u ≤ ζ_1.
  - By Tool 0.3, Φ(−1) = Tr(A^{−1} #_{1−θ} B^{−1}) − Tr e^{−Z_θ}.
- **θ < 1/2.** Part 1 (the ray form) at N = N₀ and N = −1 gives (h⁴/24)θ(1−θ)κ[N₀(N₀−1) − 2] = (h⁴/24)(1−θ)(1−2θ)κ, using
  N₀(N₀−1) − 2 = (N₀−2)(N₀+1).
- **θ = 1/2.** One more order is needed:
  - by the Baker–Campbell–Hausdorff formula, Φ(2) = h⁴κ/24 + (h⁵/12)Tr(SK) + O(h⁶);
  - from the expansion log(e^P # e^Q) = (P+Q)/2 − (1/48)([P,[P,Q]] + [Q,[Q,P]]) + O(5), we get
    Φ(−1) = −h⁴κ/48 + (h⁵/48)Tr(SK) + O(h⁶).
  - Substituting gives (h⁵/48)Tr((S − s_1)K). ∎

**Checks** (`tf-local/near-identity/`):
- Part 1 against exact word averages: d = 2, 3, 4, seven (n, m), 60 digits. The ratio tends to 1 linearly in h, and
  the h⁴ coefficient matches to 13 digits.
- The fourth moment of the first-order deviation predicted by Part 2 matches to 9 digits.
- T_θ(hγ)/(h³τ(γ)) → 1, computed directly with the exact Bloch-sphere formula.
- The θ = 1/2 bottom value: 12 random pairs, d = 2, …, 5, relative error ≤ 1e-7.
- The geometric-mean expansion is checked separately.

**Uniformity (sketch, not written out).**
- Inside the cluster TF has slack of order h³. Below it the slack is h⁴ (θ < 1/2) or h⁵ (θ = 1/2), and above ζ_d TF
  is trivial.
- Matching across the boundary layer [ζ_1, min_W ℓ_θ], of width O(h²), works whenever the bottom eigenvector of S is
  coupled by T to a higher one.
- Otherwise the bottom eigenvector is a joint eigenvector, splits off, and the dimension drops.

## 3. What this shows, and what it does not

- **Both perturbative regimes.** TF holds in both (Theorems 1 and 2), each time for a transparent reason:
  - Chebyshev's covariance inequality plus E ≥ 0 at commuting pairs;
  - Hermite–Hadamard plus an explicit positive bottom value near the identity.
- **The tightest place** is the bottom level at θ = 1/2 near the identity. This is also where the adversarial searches
  of note 08 found their minimisers.
- **The global conjecture is open.**
  - TF can be restated as follows: Heinävaara's measure of the pair dominates (tilted, on rays) that of its
    *Z-pinched* pair. That pair is obtained by pinching log A − log B onto the eigenspaces of Z_θ while keeping Z_θ
    fixed, and it commutes.
  - This has the shape of Theorem A, which proves an exact positive formula for a pinching difference of Tr e^{ag−tP}.
  - The analogue for word averages is what is missing.
- **Dynamic strategies that fail** are listed in note 08, Section 5. Monotonicity along paths fails; the static
  statements survive.

Code and logs: [`../lower-half/tf-local/`](../lower-half/tf-local/README.md).
