# A route to the general lower half: a joint spectral measure and a tilted-dominance conjecture

Ansh Mishra, Aryan Senthilkumar. 2026-10-10.

**Status.** The lower half of OQP 40 for general (n, m) remains **open**. This note records a reduction, and proves its
supporting facts:
- **Proved:** Corollary 1, Lemma 2 and Proposition 3, all from O. Heinävaara's theorem on tracial joint spectral measures.
- **Conjecture TF:** if true, TF implies the lower half for all n, m ≥ 1. It is supported by exact-data tests and
  adversarial searches, but not proved.
- **Negative results:** variants of TF that fail. These are proofs or reproducible computations, as labelled.

Notation as in [`03-lower-half.md`](03-lower-half.md):
- A, B are positive definite d × d matrices, and N = n + m.
- p_{n,m}(A, B) (written 𝒜_{n,m} there) is the average of Tr W over the words W with n letters A and m letters B.
- L_{n,m}(A, B) = Tr exp(n log A + m log B).
- The lower half is p_{n,m} ≥ L_{n,m}.

## 1. Word averages are moments of one positive measure

**Theorem (Heinävaara, arXiv:2310.03227, Theorems 1.4 and 1.7).** For Hermitian A, B there is a positive measure μ_{A,B}
on R² such that, for all x, y ∈ R,

  Tr H(f)(xA + yB) = ∫ f(ax + by) dμ_{A,B}(a, b),  H(f)(x) = ∫_0^1 ((1 − t)/t) f(xt) dt,

for every measurable f with ∫_{−M}^{M} |f(t)/t| dt < ∞ for all M. If A ≥ 0, μ_{A,B} lives on {a ≥ 0}; so for A, B ≥ 0 it
lives on the closed quadrant.

Explicitly, if A is invertible and A^{−1}B has distinct eigenvalues, μ = μ_s + μ_c:
- **Singular part:** μ_s(φ) = Σ_v ∫_0^1 ((1 − t)/t) φ(t⟨Av, v⟩, t⟨Bv, v⟩) dt, the sum running over unit eigenvectors v of
  A^{−1}B.
- **Continuous part:** dμ_c/dm₂ (a, b) = (1/2π) Σ_i |Im λ_i((I − (aA + bB)/(a² + b²))(bA − aB)^{−1})|.

We checked the normalisation 1/2π of the continuous part numerically: it reproduces the word averages to 8 digits
(`../lower-half/general-tjsm/calib.py`).

**Corollary 1.** For n + m = N ≥ 1,

  p_{n,m}(A, B) = N(N+1) ∫ a^n b^m dμ_{A,B}(a, b) = S_{n,m} + N(N+1) ∫ a^n b^m dμ_c,

where S_{n,m} = Σ_v ⟨Av, v⟩^n ⟨Bv, v⟩^m.

*Proof.*
- **First identity.** With f(t) = t^N, H(f)(t) = t^N/(N(N+1)). Compare the coefficients of x^n y^m in
  Tr(xA + yB)^N = Σ_n C(N, n) x^n y^{N−n} p_{n,N−n}.
- **Second identity.** The singular part contributes N(N+1)·Σ_v ∫_0^1 (1 − t) t^{N−1} dt ·⟨Av,v⟩^n⟨Bv,v⟩^m
  = S_{n,m}. ∎

In particular, for fixed N the sequence n ↦ p_{n,N−n} is a positive mixture of geometric sequences. Also,
Tr(AB^y) = (1+y)(2+y) ∫ a b^y dμ for real y > 0. To see this, apply the theorem with f(t) = t_+^{y+1} at the point (ε, 1), so to
Tr H(f)(εA + B), and differentiate at ε = 0.

**Lemma 2 (mass of the continuous part).** Let V = [v_1, …, v_d] be the matrix of unit eigenvectors of A^{−1}B. Then

  μ_c(R²) = −2 log |det V|.

So μ_c(R²) ≥ 0 (Hadamard's inequality), with equality if and only if A and B commute.

*Proof.*
- **The identity for small exponents.** For real N > 0, f(t) = t_+^N gives Tr A^N = Σ_v ⟨Av, v⟩^N + N(N+1) ∫ a^N dμ_c.
- **Divide by N and let N → 0.** The left side minus the sum tends to Tr log A − Σ_v log⟨Av, v⟩. The right side tends to
  μ_c(R²), by monotone and dominated convergence; μ_c is absolutely continuous, and a ≤ ‖A‖ on its support.
- **Evaluate.** The vectors v_i are A-orthogonal, so V*AV = diag(⟨Av_i, v_i⟩), and
  Tr log A − Σ_v log⟨Av, v⟩ = log det A − log det(V*AV) = −2 log |det V|. ∎

## 2. Ray projections and the commuting reference

Fix θ ∈ (0, 1). Put:
- ℓ_θ(a, b) = θ log a + (1 − θ) log b, and μ^θ := (ℓ_θ)_* μ_{A,B}, a positive measure on R;
- Z_θ = θ log A + (1 − θ) log B, with eigenvalues ζ_1, …, ζ_d;
- κ^θ := Σ_i k(u − ζ_i) du, where k(w) = (1 − e^w)_+.

For (n, m) = N(θ, 1 − θ):

  p_{n,m} = N(N+1) ∫ e^{Nu} dμ^θ(u),  L_{n,m} = Σ_i e^{Nζ_i} = N(N+1) ∫ e^{Nu} dκ^θ(u).

If A and B commute, μ^θ = κ^θ. In general the two measures have the same total "regularised" mass: by Lemma 2, the first
order term of p_{Nθ,N(1−θ)} as N → 0 is N·Tr Z_θ, exactly as for L. Here p_{x,y} := (x + y)(x + y + 1) ∫ a^x b^y dμ for
real x, y > 0.

## 3. Conjecture TF and why it implies the lower half

**Conjecture TF(θ).** Let N_0 := 1/min(θ, 1 − θ). For every u ∈ R,

  T_θ(u) := ∫_{(u,∞)} e^{N_0 v} d(μ^θ − κ^θ)(v) ≥ 0.

N_0 is the point of the ray whose smaller exponent equals 1. At u = −∞, TF(θ) is Golden–Thompson at that point:
- for θ ≤ 1/2 that point is (1, y) with y = (1 − θ)/θ;
- there T_θ(−∞) = [Tr(AB^y) − Tr exp(log A + y log B)]/(N_0(N_0 + 1)) ≥ 0.

So TF(θ) says that the Golden–Thompson surplus at the base point of the ray is not undone further along the ray.

**Proposition 3.** If TF(θ) holds, then p_{n,m} ≥ L_{n,m} at every point (n, m) = N(θ, 1 − θ) with N ≥ N_0, that is with
min(n, m) ≥ 1. The same holds for real exponents. Hence TF(θ) for every rational θ ∈ (0, 1) implies the lower half for all
n, m ≥ 1.

*Proof.*
- **Rewrite with a tilt.** Write ∫ e^{Nv} d(μ^θ − κ^θ) = ∫ h(v) e^{N_0 v} d(μ^θ − κ^θ)(v), with h(v) = e^{(N−N_0)v}.
  Here h is nondecreasing and h ≥ 0.
- **Layer cake.** Since h(v) = h(−∞) + ∫_{(−∞,v)} dh(u), the integral equals h(−∞)·T_θ(−∞) + ∫ T_θ(u) dh(u) ≥ 0.
- **Integrability.** Both tilted measures are finite, because e^{N_0 v} kills their logarithmic growth at −∞. ∎

## 4. Evidence for TF

**An exact test on the rays through (1, r), r = 1, 2, 3, …**
- **The measures.** On such a ray, the tilted measure e^{N_0 v} dμ^θ, written in the variable s = a b^r, is a measure ω
  on [0, ‖A‖‖B‖^r]. Its moments are known exactly from word averages:
  - ω has moments ∫ s^k dω = p_{k+1, r(k+1)}/(N_k(N_k + 1)), with N_k = (1 + r)(k + 1);
  - the reference ω_κ has the same moments with L in place of p.
- **The criterion.** TF on the ray says that ω dominates ω_κ in first-order stochastic order, with mass surplus given by
  Golden–Thompson.
- **The test.** We compute ρ* := min ∫ h dω / ∫ h dω_κ over increasing polynomials h with h(0) = 0 and degree ≤ K. This
  is a semidefinite program in the moments (Markov–Lukács). TF on the ray requires ρ* ≥ 1 for every K; a value below 1
  would be a counterexample certificate.

**Results** (`tf_ratio_sdp.py`, `tff_sdp.py`; logs in `../lower-half/general-tjsm/logs/`).
- **Families tested:** rays through (1, 1), (1, 2) and (1, 3), K up to 14, on these pairs:
  - near-commuting pairs (rotation angles ε = 0.3, 0.1, 0.03; d = 3, 4);
  - the Cha–Lee family, which breaks the refinement and chain routes (x = 0.3 and 0.1, shifts 1e-2 and 1e-3);
  - random pairs with d ≤ 6.

  In every case ρ* > 1. The smallest values are 1 + 7e-6 (near-commuting) and 1.002 (random).
- **Adversarial searches** (`tf_hunt.py`; about 75,000 random pairs with d = 2, …, 5 and several eigenvalue spreads,
  followed by local descent). No value below 1 beyond the solver tolerance was found. The minimisers are nearly
  commuting 2 × 2 pairs, where ρ* → 1 (`hunt_minimizers.py`).
- **Other rays** (θ = 0.2, 0.25, 1/3, 0.1). A direct quadrature of the density of μ_c gives no violation either
  (`tftest2.py`, `tfstress.py`). That quadrature is accurate only for moderate exponents.

## 5. What fails

Each item is reproducible from the scripts. The first is a numerical finding about the measure itself; the others are
counterexamples to stronger or different statements.
1. **The real-exponent lower half fails for small exponents.** Along every ray tested,
   p_{Nθ,N(1−θ)} − L = N²·G_θ + O(N³) with G_θ < 0 (`icxtest.py`). The first-order terms agree by Lemma 2.
   - So no ordering of μ^θ and κ^θ that implies the comparison for all real N > 0 can hold: not first-order dominance
     without tilt, and not the increasing convex order.
   - A proof must use min(n, m) ≥ 1. TF does so through the tilt.
2. **Without the tilt, dominance fails** near the bottom eigenvalue of Z_θ (`tailtest.py`, `tailconv.py`). The deficit is
   about 1e-3 for a 2 × 2 pair, stable under refinement of the quadrature.
3. **Tilting along a column instead of a ray fails.** Fix m and tilt the moment measure in n by one letter A, so that the
   base is Golden–Thompson Tr(AB^m) ≥ L_{1,m}. This first-order dominance fails at m = 2: ρ* = 0.9933 for a random 3 × 3
   pair (`coltf_sdp.py`).
4. **The reference built from Conjecture F fails on the diagonal.** Replace exp(log A + log B) by AB, which would give
   Conjecture F rather than the lower half. Then the dominance fails: ρ* = 0.99989 for a random 3 × 3 pair
   (`tff_sdp.py`). So TF genuinely uses the gap between F and L (Araki's log-majorization).
5. **p_{n,m}/L_{n,m} is not monotone in n**, even at m = 1 (`latmono.py`, exact word averages).

## 6. Where a proof could start

- **Small parameter.** TF is tightest near commuting pairs, where all deviations are of second order in the commutator.
  An exact second-order expansion of T_θ(u), which for the lower half itself reduces to 2 × 2 pair terms
  ([`03-lower-half.md`](03-lower-half.md), Section 4), is the natural first step.
- **A dead end.** The pinching and convex-ridge arguments that make Heinävaara's measure monotone under pinching do not
  apply directly, because the test functions a^x b^y are not convex.

Code and logs: [`../lower-half/general-tjsm/`](../lower-half/general-tjsm/README.md).
