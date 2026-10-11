# Conjecture TF holds for all 2 × 2 pairs: an exact reduction, a computer-assisted proof and an analytic tail

Ansh Mishra, Aryan Senthilkumar. 2026-10-11.

This is the full proof behind note 10 ([`../../math/10-tf-2x2.md`](../../math/10-tf-2x2.md)). Theorem A,
Proposition C, Theorem B and Theorem 6.5 here are Theorem 1, Proposition 2, Theorem 3 and Theorem 4 of the
note.

Labels: **PROVED** = analytic argument written out here (or cited from a proved note); **RIGOROUS** = ball
arithmetic (Arb via python-flint 0.9.0) with stated error control; **NUMERICAL** = floating point or
high-precision sampling, no error control.

## 0. Status (short)

**Main Theorem (PROVED, with a RIGOROUS computer-assisted part).** For every pair of positive definite 2 × 2 matrices
A, B and every θ ∈ (0, 1), Conjecture TF holds: T(u) ≥ 0 for every level u. (θ > 1/2 follows from θ ≤ 1/2 by
exchanging A and B.) Previously TF was known only perturbatively, near commuting pairs and near the identity (note 09).

The proof has four parts:
1. **Theorem A (PROVED).** For every 2 × 2 positive definite pair and every θ ∈ (0, 1/2], TF holds at every level
   if and only if one explicit closed-form number is ≥ 0. In particular TF follows from the closed-form inequality

   **(C)**  Tr(A B^r) − λ₂^{N₀} ≥ ( Tr(A⁻¹ #_{1−θ} B⁻¹) − λ₂⁻¹ )^{−N₀},  λ₂ := λ_max(e^{Z}), Z = θ log A + (1−θ) log B.

   The only non-trivial new step is a geometric lemma about the Weyl distribution of a 2 × 2 pair (Lemma 2.3, the
   "lens lemma"): ⟨Π, 1[ℓ > u]⟩ ≤ 1 strictly inside the range of ℓ on the joint numerical range. It forces the
   minimum of the TF tail into the window [ζ₁, min_W ℓ], where everything is in closed form.
2. **Section 3 (PROVED).** (C) is scale and unitarily invariant; in determinant-normalised hyperbolic coordinates
   (θ, a, c, w) — a, c the half log-spectral spreads of A and B^r, w the cosine of the angle between their Bloch
   vectors — it reads F(θ, a, c, w) ≥ 0 with explicit F, and κ(A) = e^{2a}, κ(B^r) = e^{2c}.
3. **Theorem B (RIGOROUS).** F ≥ 0 for all θ ∈ (0, 1/2], a, c ∈ [0, 40], w ∈ [−1, 1], i.e. (C) for all pairs with
   κ(A) ≤ e^{80} and κ(B^r) ≤ e^{80} (runs `runs/final_L40_*`, 183,421 certified boxes, coverage verified;
   Section 5). The proof covers every degenerate boundary inside this region: commuting pairs (both
   orientations), one matrix scalar, θ → 0, the identity corner at θ = 1/2 where TF is tight to order h⁵, and the
   exponentially thin near-commuting layers of ill-conditioned pairs (Lemma 3.7).
4. **Theorem 6.5 (PROVED, tail lemma).** F ≥ 0 for all θ ∈ (0, 1/2], all w, whenever max(a, c) ≥ 40. Two explicit
   sufficient conditions are proved with elementary estimates: layer conditions at the explicit faces
   w = ±(1 − 1/ε_P(0)) when min(a, c) ≥ 1 (Lemma 6.3), and a condition uniform in w when min(a, c) < 1 (Lemma 6.4);
   the integral representation (M2) gives explicit exponential bounds for V' and V''.

Also: **Proposition C (PROVED).** (C) holds whenever the Golden–Thompson gap is large:
Tr(AB^r) − Tr e^{log A + r log B} ≥ (det A)^{1/2} (det B)^{r/2}.

Checks: the numerical constants of the tail lemma are verified in Arb / exact rational arithmetic (`tail_constants.py`,
RIGOROUS); every intermediate inequality of the tail lemma is re-evaluated by independent code at 4090 corner and
random points (`tail_check.py`, NUMERICAL, no violation); the box certificates are tested against independent
50–160-digit code (Section 4.4); far-region samples up to max(a, c) = 360 confirm F ≥ 0 directly (`scan_far.py`,
NUMERICAL).

Dependencies (all established earlier): positivity of Heinävaara's measure μ; Ando–Hiai log-majorisation;
note 09 (`math/09-tf-local.md`) Lemma 1 (Bloch-sphere formula) and Tool 0.3 (Kubo–Ando identity at
N = −1); note 09 Theorem 1 (second order at commuting pairs) together with the rigorous E-proof
(`../tf-local/E-proof/PROOF.md`, H ≥ 0), used only on the commuting face w = −1 (Lemma 3.5).

---------------------------------------------------------------------------------------------------------------

## 1. Setting

A, B positive definite 2 × 2, θ ∈ (0, 1/2], N₀ = 1/θ, r = (1−θ)/θ, ℓ(a, b) = θ log a + (1−θ) log b,
Z = θ log A + (1−θ) log B with eigenvalues ζ₁ ≤ ζ₂. For a level u,

  g_u(v) = 1[v > u] [e^{N₀v} − (N₀+1)e^{N₀u} + N₀e^{(N₀+1)u−v}] / (N₀(N₀+1)),
  T(u) = ⟨Π, g_u∘ℓ⟩ − g_u(ζ₁) − g_u(ζ₂),

Π = Π_{A,B} the Weyl distribution. **TF (2 × 2):** T(u) ≥ 0 for all u ∈ R. Equivalently (note 09, (0.1)):
T(u) = ∫_{(u,∞)} e^{N₀v} d(μ^θ − κ^θ)(v), μ^θ = Π^θ * k, κ^θ = (δ_{ζ₁} + δ_{ζ₂}) * k, k(w) = (1 − e^{w})₊.

Commuting pairs: Π = δ_{P₁} + δ_{P₂} at the joint eigenvalue points and ℓ(P_i) = ζ_i, so T ≡ 0. **From now on A
and B do not commute.** Write A = a₀ + a⃗·σ⃗, B = b₀ + b⃗·σ⃗; then a⃗, b⃗ are linearly independent. Let M be the 2 × 2
matrix with rows a⃗ᵀ, b⃗ᵀ restricted to span(a⃗, b⃗) (invertible), Q₀ = (a₀, b₀), D the closed unit disk in that
plane, ℓ̃(y) := ℓ(Q₀ + My) (y ∈ D), w(y) := (1 − |y|²)^{−1/2}. The joint numerical range is W = Q₀ + MD. Let
v_min = min_D ℓ̃, v_max = max_D ℓ̃.

Facts about ℓ̃ (elementary): ℓ̃ is real-analytic and concave on a neighbourhood of D (each of 1 + a⃗·y, 1 + b⃗·y is
positive there after normalising a₀ = b₀ = 1, since |a⃗|, |b⃗| < 1); ∇ℓ̃ = θa⃗/(1 + a⃗·y) + (1−θ)b⃗/(1 + b⃗·y) is a
positive combination of two independent vectors, hence never 0. So v_min and v_max are attained on ∂D only.
Jensen gives ζ₁ ≤ v_min and ζ₂ ≤ v_max (for a unit eigenvector e of Z, ⟨Ze, e⟩ ≤ ℓ(⟨Ae,e⟩, ⟨Be,e⟩)).

## 2. Theorem A: reduction of TF(2 × 2) to one closed-form inequality (PROVED)

**2.1 Disk representation.** By note 09 Lemma 1 and the fact that the projection of the uniform measure on S² to a
plane has density (2π)^{−1} w(y) on D, for every C¹ function F on a neighbourhood of W

  ⟨Π, F⟩ = (1/π) ∫_D ((1 + y·∇_y) F̃)(y) w(y) dy,  F̃(y) := F(Q₀ + My).                      (2.1)

The right side is defined for every Lipschitz F (w ∈ L¹(D)); we use it as the definition of ⟨Π, F⟩ for such F.

**2.2 Derivative of the tail.** ∂_u g_u(v) = −e^{N₀u} k(u − v) and ∂_u g_u'(v) = −e^{N₀u} e^{u−v} 1[v > u]
(both bounded, continuous resp. with one jump). Differentiating (2.1) under the integral (dominated convergence),

  T'(u) = −e^{N₀u} f(u),   f(u) := m(u) − κ(u),   m(u) := ⟨Π, k(u − ℓ)⟩,  κ(u) := Σ_i k(u − ζ_i).   (2.2)

(m is the continuous density of μ^θ; in particular m ≥ 0 by Heinävaara's positivity of μ.)

**2.3 The lens lemma.** For u ∈ R put D_u := {y ∈ D : ℓ̃(y) > u}, Γ_u := {y ∈ D : ℓ̃(y) = u} and

  Λ(u) := (1/π) [ ∫_{D_u} w dy + ∫_{Γ_u} (y·n̂) w dσ ],  n̂ = ∇ℓ̃/|∇ℓ̃| (pointing into D_u).

*Lemma 2.1.* u ↦ e^{−u} m(u) and u ↦ e^{−u} f(u) are Lipschitz, with
(e^{−u} m)' = −e^{−u} Λ(u) and (e^{−u} f)' = −e^{−u} (Λ(u) − #{i : ζ_i > u}) for a.e. u.

*Proof.* On D_u, (1 + y·∇)k(u − ℓ̃) = 1 − e^{u−ℓ̃} + e^{u−ℓ̃} (y·∇ℓ̃), and it is 0 off D_u. Hence
e^{−u}m(u) = (1/π)∫_D [(e^{−u} − e^{−ℓ̃})₊ + e^{−ℓ̃} 1[ℓ̃ > u] (y·∇ℓ̃)] w dy. The first part has u-derivative
−e^{−u}(1/π)∫_{D_u} w. For the second, the coarea formula (∇ℓ̃ ≠ 0 on D) gives
∫_D e^{−ℓ̃} 1[ℓ̃ > u]·(y·∇ℓ̃) w dy = ∫_u^∞ e^{−s} h(s) ds with h(s) = ∫_{Γ_s} (y·n̂) w dσ ∈ L¹, whose derivative is
−e^{−u}h(u) a.e. Finally e^{−u}κ(u) = Σ_i (e^{−u} − e^{−ζ_i})₊ has derivative −e^{−u} #{ζ_i > u}. ∎

*Lemma 2.3 (lens lemma).* For every u ∈ (v_min, v_max) that is not a critical value of ℓ̃|_{∂D} (all but finitely
many u), Λ(u) ≤ 1. More precisely Λ(u) = 2 − k − (1/π) Σ_{j=1}^k ∫_{L_j} (1 − |y|²)^{−3/2} dy, where k ≥ 1 is the
number of arcs of ∂D on which ℓ̃ ≤ u and L_j are the "lenses" defined below.

*Proof.* For a region R ⊂ D with piecewise smooth boundary meeting ∂D transversally put
Λ_R := (1/π)[∫_R w dy − ∫_{∂R ∩ D} (y·ν_R) w dσ] (ν_R the outer normal). Λ_R is finitely additive (shared
boundary pieces have opposite normals), and Λ(u) = Λ_{D_u}.
(i) Λ_D = (1/π)∫_D w = 2 (no boundary inside D).
(ii) For a half-disk cap S = {y ∈ D : y·e > t}, |t| < 1: the push-forward of w dy to the e-axis has density π on
[−1, 1], so ∫_S w = π(1 − t); on the chord y·ν_S = −t and ∫_{chord} w dσ = π. Hence Λ_S = (1 − t) + t = 1.
(iii) For a region L ⊂ D whose closure meets ∂D only at finitely many corner points (where its two boundary curves
are transversal to ∂D): the divergence theorem for the field y·w(y), with ∇·(y w) = (2 − |y|²)(1 − |y|²)^{−3/2},
applied on L ∩ {|y| ≤ 1 − ε} and ε → 0 (the flux through the small arcs near the corners is O(ε·ε^{−1/2}) → 0),
gives Λ_L = (1/π)∫_L [w − (2 − |y|²)(1 − |y|²)^{−3/2}] dy = −(1/π)∫_L (1 − |y|²)^{−3/2} dy ≤ 0.
Now let u be as in the statement. Since v_min < u < v_max are attained on ∂D, the set {ℓ̃ ≤ u} ∩ ∂D is a union of
k ≥ 1 closed arcs B_j (finitely many: ℓ̃|_{∂D} is real-analytic and non-constant), with endpoints on Γ_u, crossed
transversally. Let c_j be the chord joining the endpoints of B_j and S_j the closed cap cut off by c_j on the side
of B_j; the caps are disjoint. The set K := {ℓ̃ > u} (on the domain of ℓ̃) is convex (superlevel set of a concave
function), so K ∩ D̄ contains the convex hull of the arcs of ∂D on which ℓ̃ > u, which is D̄ minus the interiors of
the S_j. Inside S_j the convex set K ∩ S_j contains c_j and avoids B_j, so it is a lens L_j bounded by c_j and an arc
of Γ_u. Thus D_u = (D ∖ ∪_j S_j) ∪ ∪_j L_j, and by additivity, (i), (ii), (iii):
Λ(u) = (2 − k) + Σ_j Λ_{L_j} ≤ 2 − k ≤ 1. ∎

(Consistency: for ℓ linear the lenses are empty and Λ ≡ 1, the trace of a spectral projection of rank 1.
At u ↓ v_min the formula gives the atom (1 − κ_b)^{−1/2} > 1 of Π^θ at v_min, κ_b the relative curvature of the
level curve at the tangency point; this is why f jumps up at v_min. NUMERICAL check of Λ < 1 in the interior and of
the monotonicity of e^{−u}f directly from the exact tail: `check_structure.py`.)

**2.4 Closed form below v_min.** For u ≤ v_min the functions g_u∘ℓ and φ_u∘ℓ/(N₀(N₀+1)),
φ_u(v) := e^{N₀v} − (N₀+1)e^{N₀u} + N₀e^{(N₀+1)u−v}, agree with their first derivatives on W, so (2.1) and the exact
moments ⟨Π, ab^r⟩ = Tr(AB^r) (Weyl symmetrisation is exact for a·h(b)), ⟨Π, 1⟩ = 2,
⟨Π, e^{−ℓ}⟩ = G := Tr(A⁻¹ #_{1−θ} B⁻¹) (note 09, Tool 0.3) give, for u ∈ [ζ₁, v_min],

  N₀(N₀+1) T(u) = C(u) := Tr(AB^r) − e^{N₀ζ₂} − (N₀+1)e^{N₀u} + N₀ e^{(N₀+1)u} c,   c := G − e^{−ζ₂},   (2.3)
  f(u) = 1 − c e^{u}.                                                                                  (2.4)

Here c > 0: by Ando–Hiai, λ_max(A #_{1−θ} B) ≤ e^{ζ₂}, so G = Tr (A #_{1−θ} B)⁻¹ > 1/λ_max(A # B) ≥ e^{−ζ₂}.
Also c ≤ e^{−ζ₁} (Ando–Hiai again: G ≤ Tr e^{−Z}). C'(u) = N₀(N₀+1)e^{N₀u}(c e^{u} − 1), so C has its global minimum
at u_c := −log c ≥ ζ₁, with C(u_c) = Tr(AB^r) − e^{N₀ζ₂} − c^{−N₀}.
(NUMERICAL check of (2.3) against the exact Bloch-sphere tail: 10 digits, `explore_shape.py`.)

**Theorem A.** Let A, B be positive definite 2 × 2 and θ ∈ (0, 1/2]. Then TF holds at every level u if and only if
C(min(u_c, v_min)) ≥ 0. In particular TF holds whenever

  (C)  Tr(AB^r) − e^{N₀ζ₂} ≥ (G − e^{−ζ₂})^{−N₀}.

*Proof.* For u ≥ ζ₂, κ = 0 on (u, ∞) and T(u) = ∫_u^∞ e^{N₀v} m(v) dv ≥ 0. For u ≤ ζ₁ ≤ v_min, f(u) = e^{u}·AH,
AH = Tr e^{−Z} − G ≥ 0, so T is nonincreasing on (−∞, ζ₁]. On [ζ₁, ζ₂] we have #{ζ_i > u} = 1, and:
on [ζ₁, v_min], e^{−u}f = e^{−u} − c is strictly decreasing (2.4); on [v_min, ζ₂] ⊂ [v_min, v_max), e^{−u}f is
nondecreasing (Lemma 2.1 and Lemma 2.3, the exceptional u forming a finite set). Moreover f(ζ₂) = m(ζ₂) ≥ 0.
Case u_c ≥ v_min: f ≥ 0 on [ζ₁, v_min], hence (monotonicity of e^{−u}f) on [ζ₁, ζ₂]; T is nonincreasing on
(−∞, ζ₂] and T ≥ T(ζ₂) ≥ 0 everywhere; also C(v_min) = N₀(N₀+1)T(v_min) ≥ 0.
Case u_c < v_min: f > 0 on [ζ₁, u_c), f < 0 on (u_c, v_min], and on [v_min, ζ₂] e^{−u}f increases from a negative
value to f(ζ₂)e^{−ζ₂} ≥ 0, so f changes sign once more at some u′ ≤ ζ₂ (or not at all, if f(ζ₂) = 0). By (2.2) T
decreases on (−∞, u_c], increases on [u_c, u′], decreases on [u′, ζ₂] to T(ζ₂) ≥ 0, and is ≥ 0 beyond. Hence
min_R T = min(T(u_c), something ≥ 0), and T(u_c) = C(u_c)/(N₀(N₀+1)) by (2.3). In both cases TF ⇔
C(min(u_c, v_min)) ≥ 0, and C(min(u_c, v_min)) ≥ C(u_c), which is (C). ∎

*Remarks.* (1) The bottom-level inequality BL (T(ζ₁) ≥ 0) is not sufficient for 2 × 2 TF: the minimum of T sits at
u_c > ζ₁ when u_c < v_min, as the shape study had observed. (C) is BL improved by an AH² term:
(C) ⇔ λ₁AH ≤ 1 − (1 + GT/λ₁^{N₀})^{−θ}, while BL ⇔ θ·GT ≥ λ₁^{N₀+1}AH, λ₁ = e^{ζ₁}.
(2) For commuting pairs both sides of (C) are equal (= λ₁^{N₀}).

## 3. Inequality (C) in hyperbolic coordinates (PROVED identities)

**3.1 Normalisation.** Under A → sA, B → s'B both sides of (C) scale by k^{N₀}, k = s^θ s'^{1−θ}; (C) is unitarily
invariant. So assume det A = det B = 1: A = e^{a x̂·σ⃗}, B = e^{b ŷ·σ⃗}, a, b ≥ 0, unit vectors with x̂·ŷ = w ∈ [−1, 1].
Put c := r b, so b = θc/(1−θ), and R_E := |a x̂ + c ŷ| = (a² + c² + 2acw)^{1/2}. Then N₀Z = (a x̂ + c ŷ)·σ⃗, so
λ₂ = e^{θR_E}, e^{N₀ζ₂} = e^{R_E}. The condition numbers are κ(A) = e^{2a}, κ(B^r) = e^{2c}.

**Lemma 3.1.** (i) P := Tr(AB^r) = 2[cosh a cosh c + w sinh a sinh c].
(ii) For det-1 positive 2 × 2 matrices X, Y and t ∈ [0, 1]: X #_t Y = [sinh((1−t)δ) X + sinh(tδ) Y]/sinh δ with
cosh δ = Tr(X⁻¹Y)/2. Hence G = 2[sinh(θd) cosh a + sinh((1−θ)d) cosh b]/sinh d, cosh d = cosh a cosh b − w sinh a sinh b.
*Proof.* (i) is the trace of a product of two SU(2)-type exponentials. (ii) Both sides are covariant under
X → SXS*, Y → SYS* (det S = 1), which reduces to X = I, Y = diag(e^δ, e^{−δ}); there the identity
sinh((1−t)δ) + sinh(tδ)e^{±δ} = sinh(δ) e^{±tδ} gives Y^t. Apply it with X = A⁻¹, Y = B⁻¹, t = 1 − θ. ∎
(NUMERICAL cross-check against the matrix closed forms: `explore_hyp.py`, ratios 1 to 15 digits.)

**3.2 The normalised margin.** Put ε_P := P − 2cosh R_E (Golden–Thompson gap), ε_G := 2cosh(θR_E) − G (Ando–Hiai gap),
X_P := e^{R_E} ε_P, Y_G := e^{−θR_E} ε_G. Since P − e^{R_E} = e^{−R_E}(1 + X_P) and G − e^{−θR_E} = e^{θR_E}(1 − Y_G),

  (C) ⇔ F := θ log(1 + X_P) + log(1 − Y_G) ≥ 0.

With q := (1 − w²)a²c², Ch(z) := cosh √z = Σ zⁿ/(2n)!, U_t(cosh d) := sinh(td)/sinh d,
V := U_θ(C) cosh a + U_{1−θ}(C) cosh b and nodes z₋ = (a−c)², z = R_E², z₊ = (a+c)², C₋ = cosh(a−b),
C = cosh a cosh b − w sinh a sinh b, C₊ = cosh(a+b):

**Lemma 3.2.** ε_P = 8 q Ch[z₋, z, z₊] =: q E_P and
ε_G = 2(1 − w²)[sinh²a sinh²b V[C₋, C, C₊] − 4θ⁴a²c² Ch[θ²z₋, θ²z, θ²z₊]] = (θ/(1−θ))² q E_G with
E_G = 2[S_a S_b V[C₋, C, C₊] − 4θ²(1−θ)² Ch[θ²z₋, θ²z, θ²z₊]], S_x = (sinh x/x)² (square brackets = divided
differences). Consequently F = θ q R with

  R = m_P φ₁(q m_P) − g_G φ₂(θ q g_G),  m_P = e^{R_E}E_P,  g_G = e^{−θR_E} θ E_G/(1−θ)²,
  φ₁(X) = log(1+X)/X,  φ₂(Y) = −log(1−Y)/Y.

*Proof.* As functions of w, cosh a cosh c + w sinh a sinh c is the affine interpolant of Ch(R_E²) at w = ±1, and
R_E² is affine in w with slope 2ac; Newton's formula f(w) − (interpolant) = (w−1)(w+1) f[−1, 1, w] gives ε_P.
Likewise 2cosh(θR_E) = 2Ch(θ²R_E²) and G = 2V(C) both interpolate the same endpoint values (at w = ±1 the pair
commutes and the geometric mean is e^{−Z}); θ²R_E² is affine in w with slope 2θ²ac and C is affine in w with
slope −sinh a sinh b, and Newton's formula again gives ε_G. The last formula is F = θq·R after dividing by θq. ∎

**Lemma 3.3 (monotonicity facts).** (M1) Ch has positive Taylor coefficients, so every divided difference
Ch[x₁, …, x_m] = Σ_n h_{n−m+1}(x)/(2n)! (h complete homogeneous) is positive and increasing in each node x_i ≥ 0.
(M2) For 0 < t < 1 and C > −1, U_t(C) = (sin πt/π)∫₀^∞ λ^{−t} dλ/(1 + 2Cλ + λ²); hence
U_t[x₀, x₁, x₂] = (sin πt/π)∫₀^∞ λ^{−t}(2λ)²/∏_i(1 + 2x_iλ + λ²) dλ > 0 is decreasing in each node x_i ≥ 1, and
(−1)^k U_t^{(k)} > 0 with |U_t^{(k)}| decreasing on [1, ∞).
(M3) U_t(1 + y) = t Σ_{k≥0} q_k(t)(−2y)^k, q_k(t) = ∏_{j=1}^k (j² − t²)/(2k+1)!, |q_k| ≤ 4^{−k} for |t| ≤ 1
(|y| < 2), and |d/dt (t q_k)| ≤ (1 + 2k)4^{−k}.
*Proof.* (M1) is standard (Hermite–Genocchi or the series). (M2): partial fractions
1/((λ + e^d)(λ + e^{−d})) = [1/(λ + e^{−d}) − 1/(λ + e^{d})]/(2 sinh d) and ∫₀^∞ λ^{−t}/(λ + μ) dλ = π μ^{−t}/sin πt;
divided differences of C ↦ 1/(p + qC) are (−q)^k/∏(p + qx_i). (M3): differentiating (M2) at C = 1,
U_t^{(k)}(1) = (sin πt/π)(−2)^k k! B(k+1−t, k+1+t) = (−2)^k k! t ∏_{j≤k}(j² − t²)/(2k+1)!; the series has radius 2
(singularity at C = −1) and both sides are entire in t. |q_k| ≤ (k!)²/(2k+1)! ≤ 4^{−k}. ∎

**Lemma 3.4 (two analytic sufficient conditions).** Since det(A #_{1−θ} B) = 1, G ≥ 2, so
1 − Y_G = e^{−θR_E}(G − e^{−θR_E}) ≥ e^{−θR_E}, i.e. −log(1 − Y_G) ≤ θR_E. Hence
(I) if ε_P ≥ 1 − e^{−R_E} then F ≥ θ log((1 + X_P)e^{−R_E}) ≥ 0;
(F) F ≥ θ log(1 + X_P) − min(θR_E, −log(1 − Y_G)).
**Proposition C** (PROVED) is (I) in matrix form: ε_P = GT/√(det A det B^r) and e^{−R_E} = λ_min(e^{N₀Z})/√det(e^{N₀Z}),
so GT ≥ √(det A det B^r) implies (C).

**Lemma 3.5 (commuting faces).** R(θ, a, c, ±1) := lim_{w→±1} R = 4H(θ, x, y), where H is the function of the E-proof
(`../tf-local/E-proof/PROOF.md`, H = E/(θx²y²)) and (x, y) = (2a, 2c) at w = 1, (x, y) = (2a, −2c) (a ≥ c) or (−2a, 2c)
(a < c) at w = −1. Hence R(θ, a, c, ±1) ≥ 0 (E-proof, RIGOROUS there), with equality only at θ = 1/2, a = c = 0.
*Proof.* Exactly, θX_P − Y_G = θ e^{R_E}[GT − N₀λ₁^{N₀+1}AH] = (N₀+1) T_E(ζ₁) in the frame normalised so that the
lower joint eigenpoint of the commuting limit is (1, 1) (scale factor e^{R_E}); X_P, Y_G = O(1 ∓ w), so
F = θX_P − Y_G + O((1 ∓ w)²). The pair at angle w is the commuting pair with B rotated by an angle 2ε,
1 ∓ w = 1 − cos 2ε; note 09 Theorem 1 gives T_E(ζ₁) = ε² E/(N₀+1) + o(ε²) (generic pairs; continuity for the
non-generic a = c at w = −1), hence lim F/(1 ∓ w) = E/2 and R(±1) = E/(4θa²c²) = 4H. ∎
(Independently checked: `test_rcore.py` compares the rigorous enclosure of R at w = ±1 with the E-proof routine
`ecore.H_point`, 40 random points, agreement to 12 digits.)

**Lemma 3.6 (w-derivative).** For a, c > 0, w ∈ (−1, 1) with R_E > 0:
∂_w R = Ψ₁,m ∂_w m_P − Ψ₂,g ∂_w g_G + (Ψ₁,q − Ψ₂,q) ∂_w q, where Ψ₁(q, m) = log(1+qm)/q, Ψ₂(q, g) = −log(1−θqg)/(θq);
∂_w m_P = ac e^{R_E}[E_P/R_E + 16Ch[z₋, z, z, z₊]] > 0; ∂_w q = −2wa²c²;
∂_w E_G = 2S_aS_b |V[C₋, C, C, C₊]| sinh a sinh b − 16θ⁴(1−θ)²ac Ch[θ²z₋, θ²z, θ²z, θ²z₊];
0 ≤ −Ψ₁,q ≤ m_P²/2, 0 ≤ Ψ₂,q ≤ θg_G²/(1 − Y_G), Ψ₁,m = 1/(1 + X_P), Ψ₂,g = 1/(1 − Y_G),
|V[C₋, C, C, C₊]| ≤ (cosh a |U_θ'''(1)| + cosh b |U_{1−θ}'''(1)|)/6, |U_t'''(1)| = t(1−t²)(4−t²)(9−t²)/105.
Dropping the positive terms gives ∂_w R ≥ ac·D with D explicit (implemented in `rbox.dw_lower`). The 1/R_E term
dominates near R_E = 0, which is how the degenerate corner and the line {w = −1, a = c} are handled.
*Proof.* Direct differentiation; divided differences differentiate as ∂_{x_i} f[x₀..x_n] = f[x₀..x_n, x_i];
signs and bounds from Lemma 3.3 and the elementary inequalities log(1+X) − X/(1+X) ≤ X²/2,
Y/(1−Y) + log(1−Y) ≤ Y²/(1−Y). ∎

**Lemma 3.7 (whole-column certificate W).** Fix a box Θ × A × C = [θ₀,θ₁] × [a₀,a₁] × [c₀,c₁] with θ₀ > 0, and
t₊, t₋ ∈ (0, 1) with −1 + t₋ < 1 − t₊. Suppose
 (i) ε_P ≥ 1 on the two faces w = 1 − t₊ and w = −1 + t₋ (for all (θ, a, c) in the box);
 (ii) y₊ := e^{−θR₊} t₊ K₊ < 1 and θR₊(1 − y₊) ≥ y₊, where R₊ ≤ R_E(1 − t₊) and
      K₊ ≥ 2|V'(C₋)| sinh a sinh b = 2(|U_θ'(C₋)| cosh a + |U_{1−θ}'(C₋)| cosh b) sinh a sinh b;
 (iii) y₋ := e^{−θ|a−c|} t₋ K₋ < 1 and θ log(1 + e^{|a−c|})(1 − y₋) ≥ y₋, where
      K₋ ≥ 4θ²ac Ch'(θ² R_E(−1 + t₋)²);
(with the constants replaced by box-uniform bounds). Then F ≥ 0 on Θ × A × C × [−1, 1].
*Proof.* ε_P is concave in w (affine minus the convex function Ch(R_E²), R_E² affine in w) and vanishes at w = ±1.
Bulk [−1 + t₋, 1 − t₊]: ε_P ≥ min of the two face values ≥ 1, so F ≥ 0 by Lemma 3.4(I).
Layer [1 − t₊, 1], s := (1 − w)/t₊ ∈ [0, 1]: by concavity ε_P(w) ≥ s, and R_E is increasing in w, so
X_P ≥ e^{R_E(1−t₊)} s. Since ε_G(1) = 0 and −∂_wε_G = 2|V'(C)| sinh a sinh b − 4θ²ac Ch'(θ²R_E²) ≤ 2|V'(C₋)| sinh a sinh b
(|V'| decreasing by (M2), C ≥ C₋), ε_G(w) ≤ (1 − w)K₊ and Y_G ≤ y₊ s. With log(1 + Ms) ≥ s log(1 + M) (concavity in s)
and −log(1 − ys) ≤ ys/(1 − y): F ≥ s[θ log(1 + e^{R₊}) − y₊/(1 − y₊)] ≥ s[θR₊ − y₊/(1 − y₊)] ≥ 0.
Layer [−1, −1 + t₋], s := (1 + w)/t₋: ε_P ≥ s, X_P ≥ e^{|a−c|} s (R_E ≥ R_E(−1) = |a − c|), and
∂_wε_G ≤ 4θ²ac Ch'(θ²R_E²) ≤ K₋ on the layer (Ch' increasing, R_E increasing in w), so Y_G ≤ y₋ s; conclude as above. ∎
This handles the exponentially thin layers {ε_P < 1} near w = ±1 for large a, c in one step (they are invisible to
box subdivision in w). Implemented in `rbox.wcert` (t± = 2^{−k±} chosen as the thinnest dyadic layers whose face
passes (i); |U_t'(C₋)| enclosed by Arb power series with t ranging over the box).

## 4. The computer-assisted part (RIGOROUS)

**4.1 Box bounds (`rbox.py`).** For a box Θ × A × C × W = [θ₀,θ₁] × [a₀,a₁] × [c₀,c₁] × [w₀,w₁] with exact dyadic
ends: the ranges of z (z is increasing in w and convex in (a, c): upper bound at a vertex; lower bound = minimum of
the vertex values and, on each edge whose critical point may lie in the edge, the exact unconstrained edge minimum
a_v²(1 − w₀²) resp. c_v²(1 − w₀²), which is ≤ the constrained one), z₋, z₊, q, b are computed from the
corners; then by the monotonicity in Lemma 3.2 (Ψ₁ increasing in m, decreasing in q; the subtracted term increasing
in g, θ, q) and Lemma 3.3:

  R ≥ m_P^lo φ₁(q^hi m_P^lo) − g_G^hi φ₂(θ₁ q^hi g_G^hi),
  m_P^lo = e^{√z^lo} 8 Ch[z₋^lo, z^lo, z₊^lo],  g_G^hi = e^{−θ₀R_E^lo} θ₁/(1−θ₁)² max(E_G^hi, 0),
  E_G^hi = 2[S_a^hi S_b^hi (cosh a₁ U_θ[nodes^lo]^hi + cosh b₁ U_{1−θ}[nodes^lo]^hi) − 4(θ₀(1−θ₀))² Ch[θ₀²(·)^lo]],

where nodes^lo are lower bounds of C₋, C, C₊ (C₋^lo = cosh(dist(0, [a₀ − b₁, a₁ − b₀])),
C^lo = C₋^lo + (1 − w₁) sinh a₀ sinh b₀, C₊^lo = cosh(a₀ + b₀)) — valid because U[·] decreases in each node (M2) —
and the θ-dependence of U_t[nodes] is handled by the mean value theorem around the midpoint of Θ with the
derivative (d/dt U_t)[nodes] enclosed on the whole Θ. E_G ≥ 0 is the Ando–Hiai inequality. Also
ε_P^lo = q^lo 8Ch[lo nodes] and the bound of Lemma 3.4(F) are computed.

**Point evaluations.** Ch-divided differences: the positive series of (M1) with ball nodes and the tail bound
h_k ≤ C(k+m−1, m−1)M^k (tail < 2·first omitted term, ratio < 1/2). U_t[x₀,x₁,x₂] with all nodes ≤ 1.5: the series of
(M3) summed with h_{k−2}(y), tail ≤ (1+2k)2^{−k}C(k,2)Y^{k−2} geometric. Otherwise: explicit divided-difference
formula; a first difference of two nodes whose gap is ≤ 2^{−24}(1 + smaller node) is replaced by the enclosure of
U' over their hull, a second difference of three such nodes by U''/2 on the hull (mean value theorem). U and its
C-derivatives come from (M3) with explicit tails for C ≤ 1.5 and from Arb power series of sinh(td)/sinh d with
d = log(C + √(C² − 1)) (`arb_series`) for C > 1.25 (a ball straddling both is split at 1.375). Working precision
100 bits in the box bounds, 160 bits inside W (k + 96 bits for the exact faces w = ±(1 − 2^{−k})), 160 in tests.

**4.2 Certificates.** A leaf box carries one of:
- **P**: the lower bound of R is > 0. Then F = θqR ≥ 0 on the box (F = 0 where q = 0).
- **I**: ε_P^lo ≥ 1 ⇒ (C) by Lemma 3.4(I).
- **F**: θ₀ log(1 + X_P^lo) − min(θ₁R_E^hi, −log(1 − Y_G^hi)) > 0 ⇒ F > 0 by Lemma 3.4(F) (implemented; not needed in
  the final runs).
- **W**: (for full columns w ∈ [−1, 1], θ₀ > 0) the hypotheses of Lemma 3.7 hold, with t± = 2^{−k±} the thinnest
  dyadic layers whose faces pass (i); the faces are exact dyadic Arb numbers (working precision k + 96 bits), so
  layers far thinner than double precision (k up to ≈ 120 at a = c = 40) are handled exactly.
- **D**: the lower bound D of Lemma 3.6 is > 0 on the column Θ × A × C × [−1, w₁]. Then for every point of the box
  R(θ, a, c, w) ≥ R(θ, a, c, −1) = 4H ≥ 0 (Lemma 3.5) (R is continuous on [−1, w] and differentiable inside, with
  ∂_wR ≥ ac·D > 0; at the single line R_E = 0 the derivative is +∞ and integrable).
Since every leaf gives F ≥ 0 on the whole leaf, and the leaves cover the region (Section 4.3), (C) holds on the
region.

**4.3 Coverage (`check_coverage.py`).** Exact rational arithmetic on the leaf list: all leaves certified, all inside
the domain, pairwise disjoint interiors (exact test inside 64 × 64 buckets), and the total volume equals the domain
volume. These imply that the union of the closed leaves is the closed domain. A random-point check is added.

**4.4 Tests (final code).** `test_wcert.py`: random W-certified boxes, 12 points each including points inside both
thin layers and at 1 − w = 10^{−5..−30}: 60 boxes with a, c ∈ [2, 7.5], 60 with a, c ∈ [8, 20] (120 digits), 60 with
a, c ∈ [20, 40] (160 digits): F ≥ 0 at all 2160 points. `check_lemma37.py`: the two derivative bounds of Lemma 3.7
at 300 random points (NUMERICAL, independent code): no violation. `test_rcore.py`: the ball enclosure of R at points vs an independent 60-digit mpmath implementation
(`hyp.py`, the closed forms of Lemma 3.1 without divided differences), 40 points incl. w within 10⁻⁸ of ±1, θ = 0.01,
large a, c: all contained; the commuting faces vs the E-proof's H (12 digits). `test_rbox.py`: random boxes
(touching every face, θ up to 1/2) × 4 random points each: every bound (R, ε_P, F, D) is respected by the
high-precision values — 200 boxes with a, c ≤ 4 (50 digits) and 150 boxes with a, c ≤ 40 (150 digits),
0 violations.

## 5. Theorem B (RIGOROUS)

**Theorem B.** For all θ ∈ (0, 1/2], a, c ∈ [0, 40], w ∈ [−1, 1], inequality (C) holds (F ≥ 0).
*Proof.* The region [0, 1/2] × [0, 40]² × [−1, 1] is covered by the certified leaves of the final runs of
`cert_v2.py`: `runs/final_L40_lo.txt` (θ ∈ [0, 1/4]; 103,074 leaves: W 33,675, P 54,850, I 14,508, D 41; 674 s) and
`runs/final_L40_hi.txt` (θ ∈ [1/4, 1/2]; 80,347 leaves: W 26,420, P 45,883, I 8,027, D 17; 521 s); no failures.
`check_coverage.py 40 runs/final_L40_lo.txt runs/final_L40_hi.txt`: all leaves certified, total volume 1600 equal
to the domain volume, 5,245,022 exact pair tests with 0 overlaps (`runs/coverage_final_L40.log`). Each certificate
implies F ≥ 0 on its leaf (Section 4.2); the D leaves (58, around the identity corner θ ≈ 1/2, a, c ≤ 1/2, near
the line {w = −1, a = c} and at θ ≤ 1/64) use Lemma 3.5. (The smaller run `runs/final_L20_*`, 39,822 leaves,
49 s + 54 s, coverage `runs/coverage_final_L20.log`, certifies the subregion a, c ≤ 20 independently.) ∎

(In the problem's normal form A = I + ασ_z: a = artanh α, and c = r·artanh β.) Theorem B covers both perturbative
regimes and the whole degenerate structure in between: near commuting pairs, near the identity including the tight
corner θ = 1/2 (h⁵ slack), θ → 0, and one matrix near a multiple of the identity. The complement max(a, c) > 40 is
Section 6.

## 6. The far region max(a, c) ≥ 40: tail lemma (PROVED)

Throughout θ ∈ (0, 1/2], b = θc/(1−θ) ≤ c, shc(x) = sinh(x)/x, ψ(R) := R/(1 − e^{−R}) (increasing, ψ(R) ≥ max(1, R)),
s_θ := sin(πθ)/π ≤ θ, and d := |a − b|, so that C₋ = cosh(a − b) = cosh d.

**Lemma 6.1 (pointwise criterion).** Let a, c > 0 and w ∈ (−1, 1). If ε_P ≥ 1, or if
Y_G ≤ ½ min(1, θψ(R_E)) ε_P, then F ≥ 0.

*Proof.* If ε_P ≥ 1 − e^{−R_E}, Lemma 3.4(I) applies. Otherwise 0 ≤ X_P < e^{R_E} − 1 and ε_P < 1. Concavity of
log(1 + x) on [0, e^{R_E} − 1] gives log(1 + X_P) ≥ X_P R_E/(e^{R_E} − 1) = ψ(R_E) ε_P. The hypothesis gives
Y_G ≤ ε_P/2 < 1/2, hence −log(1 − Y_G) ≤ Y_G/(1 − Y_G) ≤ 2Y_G ≤ min(1, θψ(R_E)) ε_P ≤ θψ(R_E) ε_P. So
F ≥ θψ(R_E)ε_P − θψ(R_E)ε_P = 0. ∎

**Lemma 6.2 (slopes and integral bounds).** Fix θ and a, c > 0.
(a) ε_P is concave in w, ε_P(±1) = 0, and ε_P'(w) = 2ac[shc(a)shc(c) − shc(R_E(w))] is decreasing. Hence
    ε_P(w) ≥ (1 − |w|) ε_P(0); ε_P(w) ≥ (1 − w)(−ε_P'(v)) for v ≤ w; ε_P(w) ≥ (1 + w) ε_P'(v) for w ≤ v.
(b) ε_G(±1) = 0, −∂_wε_G ≤ K₊ := 2|V'(C₋)| sinh a sinh b, and ∂_wε_G(w) ≤ 2θ²ac·shc(θR_E(w)). (Indeed
    ∂_wε_G = 4θ²ac Ch'(θ²R_E²) − 2|V'(C)| sinh a sinh b with Ch'(x²) = shc(x)/2; |V'| is decreasing in C and C ≥ C₋.)
(c) From (M2), V(C) = s_θ ∫₀^∞ λ^{−θ}(cosh a + λ cosh b)/(1 + 2Cλ + λ²) dλ, and 1 + 2λ cosh d + λ² = (λ+e^d)(λ+e^{−d}):
    |V'(C₋)| = s_θ[cosh a·I_a + cosh b·I_b],   V''(C₋) = s_θ[cosh a·II_a + cosh b·II_b],   with
    I_a = ∫₀^∞ 2λ^{1−θ}/((λ+e^d)²(λ+e^{−d})²) dλ,  I_b = ∫₀^∞ 2λ^{2−θ}/((λ+e^d)²(λ+e^{−d})²) dλ,
    II_a = ∫₀^∞ 8λ^{2−θ}/((λ+e^d)³(λ+e^{−d})³) dλ,  II_b = ∫₀^∞ 8λ^{3−θ}/((λ+e^d)³(λ+e^{−d})³) dλ.
(d) Splitting ∫₀^∞ at e^{−d} and e^{d} and using λ + e^{±d} ≥ max(λ, e^{±d}):
    I_a ≤ 2e^{−2d}[e^{θd}/(2−θ) + 2 sinh(θd)/θ + e^{−θd}/(2+θ)] ≤ 2e^{−(2−θ)d}[1.07 + min(1/θ, 2d)],
    I_b ≤ 2e^{−(1+θ)d}[1/(1−θ) + 1/(1+θ) + 1/(3−θ)] ≤ 6.8 e^{−(1+θ)d},
    II_a ≤ e^{−(3−θ)d}[48/(9−θ²) + min(8/θ, 16d)] ≤ e^{−(3−θ)d}[5.49 + min(8/θ, 16d)],
    II_b ≤ e^{−(2+θ)d}[8/(4−θ) + 8/(1−θ) + 8/(2+θ)] ≤ 22.3 e^{−(2+θ)d}.
    (Used: 2 sinh(θd)/θ ≤ e^{θd} min(1/θ, 2d), 4/(4−θ²) ≤ 1.07, and θ ≤ 1/2 for the numerical constants.)

*Proof.* (a) and (b) restate computations of Sections 3–4 (ε_P is affine minus the convex Ch(R_E²), R_E² affine
in w). (c) differentiates (M2) under the integral sign. (d) is elementary integration on [0, e^{−d}], [e^{−d}, e^{d}],
[e^{d}, ∞). ∎

**Lemma 6.3 (explicit faces).** Let E₀ := ε_P(0) ≥ 1, w₁ := 1 − 1/E₀, w₂ := −1 + 1/E₀, R_i := R_E(w_i),
P₊ := −ε_P'(w₁) = 2ac[shc(R₁) − shc(a)shc(c)]. If
 (L+) P₊ > 0 and e^{−θR₁} K₊ ≤ ½ min(1, θψ(R₁)) P₊,   and   (L−) shc(a)shc(c) − shc(R₂) ≥ 2θ,
then F ≥ 0 for every w ∈ [−1, 1].

*Proof.* Bulk w ∈ [w₂, w₁]: ε_P ≥ (1 − |w|)E₀ ≥ 1, Lemma 6.1. Layer w ∈ [w₁, 1): ε_P(w) ≥ (1 − w)P₊ (6.2(a)),
ε_G(w) ≤ (1 − w)K₊ (6.2(b)) and e^{−θR_E(w)} ≤ e^{−θR₁}, so
Y_G ≤ (1 − w)e^{−θR₁}K₊ ≤ ½ min(1, θψ(R₁))(1 − w)P₊ ≤ ½ min(1, θψ(R_E(w))) ε_P(w); Lemma 6.1.
Layer w ∈ (−1, w₂]: ε_P(w) ≥ (1 + w)P₋ with P₋ := ε_P'(w₂) = 2ac[shc(a)shc(c) − shc(R₂)], and
ε_G(w) ≤ (1 + w)·2θ²ac·shc(θR_E(w)), so Y_G ≤ (1 + w)·2θ²ac·[e^{−x}shc(x)]_{x=θR_E(w)} ≤ (1 + w)·2θ²ac (because
e^{−x}shc(x) = (1 − e^{−2x})/(2x) ≤ 1). By (L−), 2θ²ac ≤ ½θP₋ ≤ ½ min(1, θψ(R_E))P₋ (ψ ≥ 1), and Lemma 6.1 applies.
At w = ±1, F = 0. ∎

**Lemma 6.4 (a condition uniform in w).** Put t := |a − c|, M_P := 4Ch''(t²) = (t cosh t − sinh t)/t³ and
M_G := (sinh a/a)²(sinh b/b)² V''(C₋). If
 (T)  e^{−θt} (θ/(1−θ))² M_G ≤ ½ min(1, θψ(t)) M_P,
then F ≥ 0 for every w.

*Proof.* E_P = 8Ch[z₋, z, z₊] ≥ 8Ch[z₋, z₋, z₋] = M_P by (M1) (z, z₊ ≥ z₋); E_G ≤ 2S_aS_b V[C₋, C, C₊] ≤ M_G because
V[x₀, x₁, x₂] = V''(ξ)/2 with ξ ≥ C₋ and V'' is decreasing by (M2); and R_E ≥ t. Hence
Y_G = e^{−θR_E}(θ/(1−θ))² q E_G ≤ ½ min(1, θψ(t)) q M_P ≤ ½ min(1, θψ(R_E)) ε_P; Lemma 6.1. ∎

**Theorem 6.5 (tail).** For θ ∈ (0, 1/2] and M := max(a, c) ≥ 40, F(θ, a, c, w) ≥ 0 for all w ∈ [−1, 1].

*Proof.* Let m := min(a, c). If m = 0 then q = 0 and F ≡ 0.

**Region F2: m ≥ 1.** Put h := ac/(a + c) = mM/(m + M) ≥ 40/41, Δ := |a − b| + (c − b) ≥ 0 and
η₀ := ½ − e^{−40/41} ≥ 0.123. Note Δ ≥ M − m: if a = m and b ≥ a then Δ = (b − a) + (c − b) = c − a; if a = m and
b < a then Δ ≥ c − b > c − a; if a = M then Δ ≥ a − b ≥ a − c (b ≤ c).
1. *E₀ and the faces.* With s = √(a² + c²) = a + c − 2ac/(a + c + s) ≤ a + c − h,
   E₀ = cosh(a + c) + cosh(a − c) − 2 cosh s ≥ e^{a+c}/2 − e^{s} ≥ η₀ e^{a+c} ≥ 1. Further
   δ := (a + c) − R₁ = 2ac/(E₀(a + c + R₁)) ≤ 2h/E₀ ≤ (a + c)e^{−(a+c)}/(2η₀) ≤ 2.8·10⁻¹⁶ (as h ≤ (a + c)/4 and
   a + c ≥ 41), and R₂ = ((a − c)² + 2ac/E₀)^{1/2} ≤ |a − c| + 1.
2. *P₊.* 2ac·shc(R₁) ≥ 2ac·sinh(R₁)/(a + c) ≥ h e^{a+c} e^{−δ}(1 − e^{−80}) and 2ac·shc(a)shc(c) = 2 sinh a sinh c
   ≤ e^{a+c}/2, so P₊ ≥ e^{a+c}(h(1 − 3·10⁻¹⁶) − ½) > 0.
3. *K₊.* By 6.2(c, d), cosh x ≤ e^x, sinh x ≤ e^x/2, s_θ ≤ θ and e^{−θR₁} ≤ e^{θδ}e^{−θ(a+c)}:
   e^{−θR₁}K₊ ≤ e^{θδ}(s_θ/2)e^{−θ(a+c)}[e^{2a+b} I_a + e^{a+2b} I_b]
            ≤ e^{θδ} e^{a+c} [ (1.07θ + min(1, 2θd)) e^{X_A} + 3.4θ e^{X_B} ],
   X_A := (1−θ)a + b − (1+θ)c − (2−θ)d,   X_B := −θa + 2b − (1+θ)c − (1+θ)d.
   Substituting c = (1−θ)b/θ one finds exactly: X_A = −Δ if a ≥ b and X_A = −Δ − 2(1−θ)(b − a) if a < b;
   X_B = −Δ − 2θ(a − b) if a ≥ b and X_B = −Δ if a < b. Hence X_A, X_B ≤ −Δ, and with min(1, 2θd) ≤ 2θd, d ≤ Δ:
   e^{−θR₁}K₊ ≤ e^{θδ} e^{a+c} θ (4.47 + 2d) e^{−Δ} ≤ e^{θδ} e^{a+c} θ (4.47 + 2Δ) e^{−Δ}.
   (The direction a ≈ b at θ = 1/2 is exactly Δ = 0, where the exponentials cancel; there h ≈ M/2 in P₊ wins.)
4. *(L+).* Since ψ(R₁) ≥ R₁ ≥ a + c − δ, the right side of (L+) is ≥ ½ min(1, θ(a + c − δ)) e^{a+c}((1 − 3·10⁻¹⁶)h − ½).
   If θ(a + c − δ) ≤ 1, it suffices that e^{θδ}(4.47 + 2Δ)e^{−Δ} ≤ ½(a + c − δ)((1 − 3·10⁻¹⁶)h − ½): the left side is
   ≤ 4.48 ((4.47 + 2Δ)e^{−Δ} is decreasing in Δ ≥ 0) and the right side is ≥ ½·40.9·0.475 ≥ 9.7.
   If θ(a + c − δ) > 1, it suffices (θ ≤ ½) that (4.47 + 2Δ)e^{−Δ}(1 + 10⁻¹⁵) ≤ (1 − 3·10⁻¹⁶)h − ½: for m ≥ 20,
   h ≥ 40/3 while the left side is ≤ 4.48; for m < 20, Δ ≥ M − m > 20 and the left side is < 10⁻⁷ ≤ 0.47.
5. *(L−).* shc(a)shc(c) = shc(m)shc(M) and shc(R₂) ≤ shc(M − m + 1). For m ≥ 1,
   shc(M)/shc(M − m + 1) ≥ e^{m−1}(1 − e^{−2M})(M − m + 1)/M = (1 − e^{−2M}) g(m), g(m) := e^{m−1}(M − m + 1)/M,
   and g is nondecreasing on [1, M] (g'(m) = e^{m−1}(M − m)/M), so g ≥ g(1) = 1. Hence
   shc(a)shc(c) − shc(R₂) ≥ shc(M − m + 1)[(1 − e^{−80}) shc(m) g(m) − 1]. If M − m ≥ 3 this is
   ≥ shc(4)(shc(1)(1 − e^{−80}) − 1) ≥ 6.82·0.175 ≥ 1.19; if M − m < 3 then m > 37 and (shc(M − m + 1) ≥ 1, g ≥ 1)
   it is ≥ (1 − e^{−80})shc(37) − 1. Either way it is ≥ 1 ≥ 2θ.
   By Lemma 6.3, F ≥ 0 on F2.

**Region F1: 0 < m < 1.** Then t = |a − c| = M − m > 39, and since t cosh t − sinh t ≥ (t − 1)cosh t ≥ (t − 1)e^t/2 and
ψ(t) ≥ t, the right side of (T) is RHS_T ≥ min(1, θt)(t − 1)e^t/(4t³). On the left, (θ/(1−θ))² = (b/c)², so
LHS_T = e^{−θt}(sinh a/a)²(sinh b/c)² V''(C₋), and V''(C₋) ≤ θ[cosh a·II_a + cosh b·II_b].
*Case a = M, c = m.* Then b ≤ c < 1, d = a − b ≥ a − 1 and t ≥ a − 1; (sinh b/c)² = shc(b)²(θ/(1−θ))² ≤ 1.3811·4θ²,
(sinh a/a)² ≤ e^{2a}/(4a²), e^{−θt}e^{2a}e^{a−(3−θ)d} ≤ e³ and e^{−θt}e^{2a}e^{−(2+θ)d} ≤ e³. Hence
LHS_T ≤ (5.525e³/4)θ²[θ(5.49 + 22.3 cosh 1) + 8]/a² ≤ 776θ²/a² ≤ 776θ²/t² (t ≤ a). If θt ≥ 1, (T) follows from
776θ² ≤ (t − 1)e^t/(4t); if θt < 1, from 776θ ≤ (t − 1)e^t/4. Both hold for t ≥ 39 by a huge margin.
*Case a = m, c = M.* (sinh a/a)² ≤ shc(1)² = 1.3811 and t ∈ (c − 1, c].
 – If b < 1: (sinh b/c)² ≤ 1.3811(b/c)² ≤ 5.525θ², II_a ≤ 5.49 + 8/θ and II_b ≤ 22.3, so
   LHS_T ≤ 1.3811·5.525θ²·cosh(1)·θ(5.49 + 8/θ + 22.3) ≤ 258θ²; (T) follows from 258θ² ≤ (t − 1)e^t/(4t³) if θt ≥ 1
   and from 258θ ≤ (t − 1)e^t/(4t²) if θt < 1 (t > 39).
 – If b ≥ 1: then θ ≥ 1/(c + 1), so θt ≥ (c − 1)/(c + 1) ≥ 0.951. From d ≥ b − 1:
   sinh²b·II_a ≤ (e³/4)(5.49 + 8/θ) and sinh²b·cosh b·II_b ≤ 5.575 e^{θc + 2 + θ} (as (1−θ)b = θc); also
   e^{−θt}e^{θc} = e^{θa} ≤ e^θ. Hence LHS_T ≤ (1.3811/c²)[cosh(1)(e³/4)(5.49θ + 8) + 5.575θe^{2+2θ}] ≤ 193/c²
   ≤ 193/t² (the bracket is increasing in θ; its value at θ = 1/2 times 1.3811 is 192.31…), and (T) follows from
   193 ≤ 0.951(t − 1)e^t/(4t) if θt < 1 and from 193 ≤ (t − 1)e^t/(4t) if θt ≥ 1.
By Lemma 6.4, F ≥ 0 on F1. ∎

**Checks.** *RIGOROUS:* `tail_constants.py` verifies every numerical constant of this section in Arb ball arithmetic
(200 bits; the θ-dependent constants of 6.2(d) on 4096 subintervals of [0, 1/2]) or in exact rational arithmetic, and
lists the elementary facts it relies on (sin y ≤ y, monotonicity of x e^{−x}, …) with their one-line proofs; all
claims hold (`runs/tail_constants.log`). This check caught one slip in an earlier draft (the F1 constant for b ≥ 1 is
192.31…, now bounded by 193).
*NUMERICAL (independent code, 80 digits):* `tail_check.py` evaluates every intermediate inequality of this proof —
both forms of each bound in 6.2(d), E₀ ≥ e^{a+c}(½ − e^{−h}) ≥ η₀e^{a+c}, δ ≤ 2h/E₀ ≤ 2.8·10⁻¹⁶, the bound for P₊,
Δ ≥ M − m, the exponent identities for X_A and X_B, both bounds for e^{−θR₁}K₊, the sub-cases of Step 4, (L+), the
two bounds of Step 5, (L−), R₂ ≤ |a − c| + 1, the lower bound for RHS_T, the intermediate and final bounds of the
three F1 cases, and (T) — at 45 fixed corner points and 2000 random points for each of two seeds (4090 points:
F1 1372, F2 2718; θ from 10⁻⁴ to ½ including θ = ½ exactly, M from 40 to 300, m from 10⁻⁶ to M). The integrals of
6.2(c) are taken from closed forms (s_θI_a = |U_θ'(C₋)|, s_θI_b = |U_{1−θ}'(C₋)|, s_θII_a = U_θ''(C₋),
s_θII_b = U_{1−θ}''(C₋); λ → 1/λ in (M2) shows that ∫λ^{−t}(1 + 2Cλ + λ²)^{−1}dλ is even in t) and compared with
quadrature of (M2) at every fifth point (largest relative deviation 1.5·10⁻⁸). No inequality is violated. Largest
ratios left/right side: (L+) 0.0064 (θ = ½, a = c = 40), (L−) 4.3·10⁻¹⁶, (T) 4.7·10⁻¹⁶; the constants 776 and 193
are nearly attained (ratios 0.9993 and 0.9964), 258 is not (4.1·10⁻⁵) (`runs/tail_check_s2.log`, `_s3.log`;
LOG.md, Step 9). `tail_explore.py` maps the ratios of (L±) and (T) on a grid with max(a, c) up to 2000 and
min(a, c) down to 10⁻⁴·max: the largest (L±) ratio on F2 is again 0.0064 (θ = ½, a = c = 40) and the largest (T)
ratio on F1 is 3.3·10⁻¹⁷ (θ = ½, a = 40, c = 0.4) (`runs/tail_explore.log`).

## 6A. Proof of the Main Theorem

Let A, B be positive definite 2 × 2 and θ ∈ (0, 1/2]. If A, B commute, T ≡ 0 (Section 1). Otherwise, by Theorem A
it suffices to prove (C). By Section 3.1, (C) is invariant under A → sA, B → s'B and unitary conjugation; after
normalising det A = det B = 1 it reads F(θ, a, c, w) ≥ 0 (Section 3.2) with a, c ≥ 0, w ∈ [−1, 1]. If
max(a, c) ≤ 40 this is Theorem B; if max(a, c) ≥ 40 it is Theorem 6.5. For θ ∈ (1/2, 1), TF for (A, B, θ) is TF for
(B, A, 1 − θ) (the definitions are symmetric under this exchange: N₀ = 1/min(θ, 1 − θ)). ∎

What the proof rests on: Heinävaara's positivity of μ (used for levels u ≥ ζ₂ and for m(ζ₂) ≥ 0); Ando–Hiai
log-majorisation; note 09 Lemma 1 (Bloch-sphere formula) and Tool 0.3 (Kubo–Ando identity at N = −1); and, only for the
58 D-boxes of Theorem B, note 09 Theorem 1 together with the rigorous E-proof (H ≥ 0 on the commuting face w = −1,
Lemma 3.5). Everything else is proved here or certified by the runs listed in Section 5.

## 7. Files and commands

- `cf2x2.py` (matrix closed forms, mpmath), `hyp.py` (hyperbolic closed forms, mpmath): NUMERICAL references.
- `explore_shape.py`, `check_structure.py`: NUMERICAL checks of Theorem A's ingredients against the exact tail.
- `explore_C.py`, `explore_hyp.py`, `explore_w.py`, `explore_gaps.py`, `scan_far.py`: NUMERICAL landscape/scans.
- `rcore.py`: rigorous point/ball evaluation of R (Arb). `rbox.py`: rigorous box bounds (P, I, F) and Lemma 3.6 (D).
- `cert_v2.py T0 T1 L out` (certificates W, P, I, F, D; used for the final runs) and its predecessor
  `cert_core.py` (P, I, F, D only; superseded): adaptive certification; `check_coverage.py L files…`: coverage.
- `test_rcore.py`, `test_rbox.py`, `test_wcert.py`: tests against independent mpmath code and the E-proof.
- `tail_constants.py` (every numerical constant of Section 6 in Arb or exact rational arithmetic, RIGOROUS),
  `tail_check.py` (every intermediate inequality of Section 6 at corner and random points, NUMERICAL) and
  `tail_explore.py` (map of the ratios in (L±), (T), NUMERICAL); `check_lemma37.py` (derivative bounds of Lemma 3.7,
  NUMERICAL).
- `runs/`: final leaf lists and logs `final_L40_*`, `final_L20_*`, `coverage_final_L40.log`,
  `coverage_final_L20.log`, final test logs `test_*_final*.log`, `check_lemma37.log`,
  far-region scans `scan_far_s1.log`, `scan_far_s2_40_150.log`, `scan_far_s4_150_300.log`, tail-lemma checks
  `tail_constants.log`, `tail_check_s2.log`, `tail_check_s3.log`, `tail_explore.log`; everything made before the
  fixes of LOG.md Steps 7–9 is in `runs/superseded/` (not used by the proof).
- Run times (one core each, two processes in parallel): L = 40 certification 674 s + 521 s (L = 20: 49 s + 54 s);
  coverage 20 s; tests a few minutes each; `scan_far.py 1 4000` about 2 minutes; `tail_constants.py` a few seconds,
  `tail_check.py s 2000 5` about 10 minutes per seed, `tail_explore.py` about 1 second.
Python 3 with python-flint 0.9.0 (Arb) and mpmath 1.3.0, OMP_NUM_THREADS=1.

**Reproduction** (from this folder, `PY=python`, OMP_NUM_THREADS=1):

    $PY cert_v2.py 0.0 0.25 40.0 runs/final_L40_lo.txt        # 674 s
    $PY cert_v2.py 0.25 0.5 40.0 runs/final_L40_hi.txt        # 521 s
    $PY check_coverage.py 40 runs/final_L40_lo.txt runs/final_L40_hi.txt
    $PY test_rcore.py 11 40;  $PY test_rbox.py 7 200;  $PY test_rbox.py 8 150 39.5 150
    $PY test_wcert.py 5 60;  $PY test_wcert.py 6 60 8 19.9;  $PY test_wcert.py 9 60 20 39.9 160;  $PY check_lemma37.py 1 300
    $PY scan_far.py 2 1500 40 150 350;  $PY scan_far.py 1 4000;  $PY scan_far.py 4 3000 150 300 520  # NUMERICAL far-region scans
    $PY tail_constants.py                                       # RIGOROUS constants of Section 6 (seconds)
    $PY tail_check.py 2 2000 5;  $PY tail_check.py 3 2000 5;  $PY tail_explore.py   # NUMERICAL checks of Section 6
    $PY explore_shape.py 1 3;  $PY check_structure.py 3 2      # NUMERICAL checks of Theorem A's ingredients

(`explore_shape.py`, `check_structure.py` import the exact-tail reference `../tf-local/near-identity/tf2x2_sphere.py`;
`test_rcore.py` imports the E-proof module `../tf-local/E-proof/ecore.py`.)
