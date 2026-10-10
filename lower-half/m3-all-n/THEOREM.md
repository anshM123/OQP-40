# Conjecture F at (n, 3) for every n: the lower half of OQP 40 whenever min(n, m) ≤ 3

Ansh Mishra, Aryan Senthilkumar. 2026-10-09/10. Computer-assisted where stated; not externally refereed.

Notation as in `publish/OQP-40/math/05-lower-half-m3.md` (the "m3 note"): K_n(x,y,z) = h_n(x,y,z)/C(n+2,2) - (xyz)^{n/3},
the min-apex kernel E(s,t) = K_n(1,s,t) - sqrt(K_n(t,1,1) K_n(t,s,s)) (1 < s < t), E(s,s) = K_n(1,s,s), the weight
w(s) = sqrt(K_n(1,s,s)), F = E/(w(s) w(t)), and Lemma 4 / Lemma 7(n) / Proposition 6 of the m3 note.
Scaled log coordinates: sigma = log s, tau = log t, a = n sigma, d = n (tau - sigma), b = a + d = n tau, and

    L1 = (log F)_sigma / n,   L2 = -(log F)_tau / n,   L3 = -F_{sigma tau} / (n^2 F).

The four Lemma 4 conditions (F >= 0, F_s >= 0, F_t <= 0, F_st <= 0) are F >= 0, L1 >= 0, L2 >= 0, L3 >= 0.

## 0. Status

**Theorem B (computer-assisted, independently checked, not externally reviewed).** For every n ≥ 37,
A_{n,3}(A, B) ≥ Tr((A^{n/3} B)^3) for all positive definite A, B of every size. With Theorem 5 of
[`../../math/05-lower-half-m3.md`](../../math/05-lower-half-m3.md) (exact verification for every n ≤ 36) this holds for
**every n ≥ 1**, so the lower half of OQP 40 holds at (n, 3) and (3, n) for every n, hence whenever min(n, m) ≤ 3.

How the proof is put together:
- Section 1: Proposition 6', a family of certificates that contains the one of the m3 note
  ([`05-lower-half-m3.md`](../../math/05-lower-half-m3.md), the "m3 note").
- Section 2: why the certificate of the m3 note cannot be pushed to all n (its asymptotic margin is only 1.35e-4).
- Section 3: the Gaussian-design certificate, with healthy asymptotic margins.
- Section 8: Theorem B. The four conditions of Lemma 4 of
  [`04-lower-half-new-cases.md`](../../math/04-lower-half-new-cases.md) are verified in ball arithmetic for every
  n ≥ 37 at once (eps = 1/n is an interval variable), on charts that cover the whole domain, including s → 1, t → ∞
  and the corner where s and t are both near 1.

Checks: [`independent-check/CHECK_REPORT.md`](independent-check/CHECK_REPORT.md). A second implementation, which
shares no verification code with the first, re-verifies every region (605,334 boxes, 0 failures) and checks the
coverage mechanically. It found one real gap in the first implementation (an eps-truncation in `tb_arb.S_of` that made
10 regions unjustified); those regions were re-run with the correction and verified. See the README of this folder for
which logs are authoritative.

## 1. Generalised certificates

**Proposition 6'.** Let n >= 1 and let R be a positive semidefinite kernel on (0, infinity) with R(u, u) = 1 for all u
(it may depend on n). For 1 < s < t put

    cap(s,t) = sqrt(K_n(t,1,1) K_n(t,s,s)),     E^R(s,t) = E^R(t,s) = K_n(1,s,t) - cap(s,t) R(n log t, n log(t/s)),

and E^R(s,s) = K_n(1,s,s). If E^R is a positive semidefinite kernel on (1, infinity), then
A_{n,3}(A,B) >= Tr((A^{n/3} B)^3) for all positive definite A, B of any size. For R = 1 this is Proposition 6 of the
m3 note.

*Proof.* Let A have distinct eigenvalues alpha_1 < ... < alpha_r. For each triple alpha_i < alpha_j < alpha_k give the
largest point the share G^(k)_{ij} = cap_{alpha_k}(alpha_i, alpha_j) R(n log(alpha_k/alpha_i), n log(alpha_k/alpha_j)),
where cap_z(x,y) = sqrt(K_n(z,x,x) K_n(z,y,y)); give the middle point 0 and the smallest point
G^(i)_{jk} = K_n(alpha_i, alpha_j, alpha_k) - G^(k)_{ij}; put G^(l)_{aa} = K_n(alpha_l, alpha_a, alpha_a). The share identity
of Lemma 2 of [`04-lower-half-new-cases.md`](../../math/04-lower-half-new-cases.md) holds by construction. Each G^(l) is block diagonal (the cross entries,
where l is the middle point, are 0).
- Below block (indices a with alpha_a < alpha_l): G^(l)_{aa'} = u(a) u(a') R(p_a, p_a') with u(a) = sqrt(K_n(alpha_l,
  alpha_a, alpha_a)) and p_a = n log(alpha_l/alpha_a) > 0 distinct; on the diagonal u(a)^2 = u(a) u(a) R(p_a, p_a). So the
  block is D_u [R(p_a, p_a')] D_u, positive semidefinite.
- Above block (alpha_b > alpha_l): K_n and cap are homogeneous of degree n and R depends only on ratios, so with
  s = alpha_b/alpha_l, t = alpha_b'/alpha_l the entry is alpha_l^n E^R(s, t) (the diagonal included). Positive
  semidefinite by hypothesis.
Lemma 2 of [`04-lower-half-new-cases.md`](../../math/04-lower-half-new-cases.md) gives Phi(K_n) = 3 sum_l <R^(l), G^(l)> >= 0, and Phi(K_n) = A_{n,3} -
Tr((A^{n/3}B)^3) (m3 note, Section 2). For r <= 2 there is nothing to prove. QED

Examples of admissible R: R = 1; Markov correlations R(u,v) = p(max(u,v))/p(min(u,v)) with p > 0 decreasing;
Gaussian correlations R(u,v) = exp(-(Phi(u) - Phi(v))^2) for ANY real function Phi; cos(theta(u) - theta(v)) for any
theta; products and mixtures of these.

## 2. The stationary limit and the obstruction for the m3-note certificate

Put kappa(d) = K_inf(d,0,0) = 2(e^d - 1 - d)/d^2 - e^{d/3} (d > 0), which is > 0 and ~ d^2/36 as d -> 0.

**Theorem A (stationary limit).** Fix sigma > 0 and d > 0, s = e^sigma, t_n = s e^{d/n}. Let R be as in Proposition 6'
with R(b, d) -> R_inf(d) as b -> infinity (for R = 1, R_inf = 1). Then

    F^R_n(s, t_n) := E^R(s, t_n) / (w(s) w(t_n))  ->  f_R(d) := 2 sinh(d/2)/d - sqrt(kappa(d)/2) R_inf(d)   (n -> inf).

For R = 1 this is f_inf(d) = 2 sinh(d/2)/d - sqrt(kappa(d)/2) = [(d - 1 + e^{-d})/d^2 + e^{d/3}/2] / [2 sinh(d/2)/d +
sqrt(kappa(d)/2)] (the second form has no cancellation). If moreover R(b, .) -> R_inf with derivatives, exponentially
fast in b (true for the examples below and for R = 1), then L1, L2 -> -f_R'/f_R and L3 -> f_R''/f_R.

*Proof.* Write [x,y] = (y^{n+2} - x^{n+2})/(y - x), so h_n(1,s,t) = ([s,t] - [1,s])/(t - 1). As n -> inf with d fixed:
- [s, t_n] = s^{n+1} (e^{(n+2)d/n} - 1)/(e^{d/n} - 1) = n s^{n+1} ((e^d - 1)/d) (1 + O(1/n)), while [1,s] = O(s^{n+2})
  is smaller by a factor 1/n; with C(n+2,2) = n^2 (1 + O(1/n))/2:
  h_n(1,s,t_n)/C(n+2,2) = (2 s^{n+1}/(n(s-1))) ((e^d - 1)/d) (1 + O(1/n)); and (s t_n)^{n/3} = s^{2n/3} e^{d/3} is
  exponentially smaller (s > 1).
- K_n(1,x,x) = ((n+1) x^{n+2} - (n+2) x^{n+1} + 1)/((x-1)^2 C(n+2,2)) - x^{2n/3} = (2 x^{n+1}/(n(x-1))) (1 + O(1/n)) for
  x = s and x = t_n; hence w(s) w(t_n) = (2 s^{n+1} e^{d/2}/(n(s-1))) (1 + O(1/n)).
- K_n(t,1,1) = (t^{n+2} - (n+2) t + n + 1)/((t-1)^2 C(n+2,2)) - t^{n/3} = (2 s^{n+2} e^d/(n^2 (s-1)^2)) (1 + O(1/n)).
- K_n(t_n, s, s) = s^n K_n(e^{d/n}, 1, 1) and K_n(e^{d/n},1,1) = 2(e^d - 1 - d)(1 + O(1/n))/d^2 - e^{d/3} -> kappa(d)
  (expand (e^{d/n})^{n+2} = e^d (1 + 2d/n + ...), (n+2) e^{d/n} = n + 2 + d + O(1/n), (e^{d/n} - 1)^2 C(n+2,2) =
  (d^2/2)(1 + O(1/n))).
So cap(s, t_n) = (s^{n+1}/(n(s-1))) e^{d/2} sqrt(2 kappa(d)) (1 + o(1)), and dividing,
F^R_n -> [2(e^d - 1)/d - e^{d/2} sqrt(2 kappa(d)) R_inf(d)] / (2 e^{d/2}) = f_R(d). The second form of f_inf follows from
(2 sinh(d/2)/d)^2 - kappa(d)/2 = (d - 1 + e^{-d})/d^2 + e^{d/3}/2.
Derivatives (sketch): every normalised quantity above is, apart from exponentially small terms (s^{-n}, s^{-n/3}, ...), an
analytic function of (sigma, d, 1/n) near (sigma, d, 0), so the convergence holds with sigma- and d-derivatives.
With d_sigma|_tau = d_sigma|_d - n d_d and d_tau|_sigma = n d_d: L1 = -d_d log F + O(1/n), L2 = -d_d log F,
L3 = d_d^2 F/F - (1/n) d_sigma d_d F/F, which converge to -f'/f, -f'/f, f''/f. The R-terms contribute
n d_b R(n tau, d), which tends to 0 under the stated assumption. QED

**Weights (exact identity).** If the weight w is replaced by W = w e^{psi}, F becomes F e^{-psi(sigma)-psi(tau)} and, with
g = psi'/n,

    L1 -> L1 - g(sigma),   L2 -> L2 + g(tau),   L3 -> L3 - g(sigma) L2 + g(tau) L1 - g(sigma) g(tau).

(Proof: F~_{st}/F~ = (log F~)_{st} + (log F~)_s (log F~)_t, expand.) In the stationary regime L1 = L2 = l(d), L3 = f''/f.
If g(sigma) -> gamma(sigma) with gamma continuous (for example psi = n Gamma(sigma), a local exponential tilt), then
g(tau) - g(sigma) -> 0 there and L1 -> l - gamma, L2 -> l + gamma, L3 -> f''/f - gamma^2 <= f''/f. So the
square-root-of-diagonal weight (gamma = 0) is optimal in the stationary regime, and such weights cannot raise the
asymptotic rectangle margin above min_d f''/f. (A weight oscillating on the scale 1/n adds
l (g(tau) - g(sigma)) - g(sigma) g(tau); we expect, but did not prove, that this does not help either.)

**Lemma A2 (rigorous; `verify_stationary.py`, log `verify_stationary.log`, plus the tail argument below).** With
lam = 7/100 and rr(d) = (2 sinh(d/2)/d - e^{-lam d})/sqrt(kappa(d)/2), for every d > 0:

    (V1) -f_inf'(d)/f_inf(d) >= 0.0600,     (V2) f_inf''(d)/f_inf(d) >= 1.340e-4,     (V3) 0 < rr(d) < 1, i.e. f_inf(d) < e^{-lam d}.

*Proof.* On (0, 60] by verified ball arithmetic (python-flint arb, 256 bits): adaptive bisection into 6184 intervals;
on [0, 2] Taylor polynomials of degree 40 with explicit remainders for the four removable singularities; on [2, 60]
the closed forms as arb power series with the centred form; (V3) is checked as e^{lam d} f_inf(d) < 1 on [2, 60]
(equivalent because sqrt(kappa/2) > 0); rr > 0 because 2 sinh(d/2)/d >= 1 > e^{-lam d}. Certified minima:
-f'/f >= 0.06002, f''/f >= 1.3400e-4 (near d = 8.40), 1 - e^{lam d} f >= 0.0220 (near d = 8.55). The formulas of the
script were compared with direct 40-digit evaluation of the definitions at d = 0.3, 1.5, 1.99, 2.5, 8.36, 40 (agreement
to 12 digits). Tail d >= 60: f_inf = (d/2) e^{-d/6} P/Q with P = 1 + 2 u e^{-d/3}, u = (d - 1 + e^{-d})/d^2, and
Q = 1 - e^{-d} + sqrt(1 - eps), eps = (1 + d) e^{-d} + (d^2/2) e^{-2d/3}. For d >= 60: 0 < u <= 1/d, |u'| <= 3/d^2,
|u''| <= 11/d^3, so |(log P)'|, |(log P)''| <= 3e-11; eps <= 7.7e-15, |eps'| <= 5.2e-15, |eps''| <= 3.8e-15, so
Q >= 2 - 1e-14 and |(log Q)'|, |(log Q)''| <= 1.5e-15 (d^k e^{-cd} is decreasing there). Hence
(log f)' = 1/d - 1/6 + (log P)' - (log Q)' <= -0.1499, f''/f = (log f)'' + ((log f)')^2 >= 0.1499^2 - 1/3600 - 1e-10
>= 0.0222, and e^{lam d} f = (d/2) e^{-(1/6 - lam) d} P/Q <= 30 e^{-5.8} (1 + 1e-10)/(2 - 1e-14) < 0.05. QED

**Corollary A1 (the m3-note certificate in the stationary limit).** f_inf is positive, strictly decreasing and
strictly convex on (0, infinity) and tends to 0; by Polya's criterion f_inf(|x|) is a positive definite function, and
the limits of the scaled Lemma 4 conditions satisfy L1, L2 -> -f_inf'/f_inf >= 0.060 and L3 -> f_inf''/f_inf >= 1.34e-4
(rigorous, Lemma A2 and Theorem A). The margin is also small rigorously: ball evaluation at d = 8.3608 gives
f''/f = 1.3451017e-4 +- 3e-14 (`finf_point_values.log`), so min_d f''/f lies in [1.340e-4, 1.3452e-4].
Numerically (`finf_constants.py`, 40 digits): -f'(0+) = 1/(6 sqrt 2) = 0.117851
(exact), min -f'/f = 0.060466 at d = 5.2917, **min f''/f = 1.3451e-4 at d* = 8.3608**, f''/f = 0.0388 at 0+ and
-> 1/36 at infinity. So in the stationary regime (s fixed, t/s = e^{d/n}, d ~ 8.4) the rectangle condition F_st <= 0
holds with a relative margin of only 1.35e-4 for large n. Direct computation agrees (`explore_critical.log`,
sigma = 8, d = 8.377): L3 = 8.4e-4 (n = 50), 3.0e-4 (n = 200), 1.74e-4 (n = 800), i.e. about 1.35e-4 + 0.035/n.

**Consequence.** A proof of Lemma 7(n) for all n >= N0 through the four Lemma 4 conditions, with any weight, must
control the error terms of the stationary regime to relative accuracy ~1e-4. With errors ~0.035/n this forces
N0 ~ 10^3 or more, and the exact per-n verification cannot reach that (it costs ~n^5: 31 min at n = 29, 3 does not
divide n). The two-regime route, applied to the m3-note certificate, is blocked by this. The obstruction is an
artifact of the Polya-type criterion, not of the kernel: the Fourier transform of f_inf(|x|) is robustly positive
(fhat(w) w^2/(2 * 0.1179) >= 0.42 for w >= 0.25; `finf_fourier.py`, numerical).

## 3. A certificate with healthy asymptotic margins

**Proposition C (curvature budget; rigorous given the numerical value of the integral).** For every R as in
Theorem A with R_inf continuous at 0: f_R >= f_inf (because R_inf <= 1), and f_R(d) = 1 - R_inf(0) d/(6 sqrt 2) + o(d).
If f_R is convex, decreasing and tends to 0, and f_R'' >= m f_R on (0, inf), then

    m <= (-f_R'(0+)) / int_0^inf f_R <= (1/(6 sqrt 2)) / int_0^inf f_inf = 0.11785/11.4752 = 0.01027.

(Integrate f_R'' >= m f_R.) So no certificate of the family can have an asymptotic rectangle margin above ~0.0103.

**The Gaussian design.** Take R(u, v) = exp(-(Phi(u) - Phi(v))^2) (admissible for any Phi), with Phi chosen so that the
stationary profile is the mixture f_R = (1 - eta) f_inf + eta e^{-lam d}:

    rr(d) = (2 sinh(d/2)/d - e^{-lam d}) / sqrt(kappa(d)/2),   Phi(d) = -sqrt(-log(1 - eta (1 - rr(d)))),

so that R(inf, d) = exp(-Phi(d)^2) = 1 - eta (1 - rr(d)). For lam = 7/100, 0 < rr < 1 on (0, infinity) (Lemma A2,
(V3)), so Phi is well defined (and Phi(d) -> 0 exponentially fast). The share of the largest point is
cap(s,t) exp(-(Phi(n log t) - Phi(n log(t/s)))^2).

**Corollary A3 (rigorous: stationary margins of the Gaussian design).** For lam = 7/100 and 0 < eta <= 1 the stationary
profile f_R = (1 - eta) f_inf + eta e^{-lam d} satisfies, for all d > 0,

    -f_R'/f_R >= 0.06,      f_R''/f_R >= eta lam^2 = 0.0049 eta.

*Proof.* By (V3), f_R <= e^{-lam d}. By (V1), -f_R' >= 0.06 (1 - eta) f_inf + 0.07 eta e^{-lam d} >= 0.06 f_R. By (V2),
f_R'' >= eta lam^2 e^{-lam d} >= eta lam^2 f_R. QED
So, by Theorem A, the scaled Lemma 4 conditions of the Gaussian-design certificate have limits L1, L2 >= 0.06 and
L3 >= 0.0049 eta in the stationary regime (0.0034 for eta = 0.7), against 1.345e-4 for the m3-note certificate.

Lemma 4 margins (minimum over grids in (a, d); numerical, mpmath 45-60+ digits, numerical differentiation;
`explore_gauss_eta.py`, `explore_gauss_fine.py`, `scan_design.py`):

| certificate | n | min L1 | min L2 | min L3 |
|---|---|---|---|---|
| m3 note (R = 1) | inf (limit kernel) | 0.0629 | 0.0629 | 4.0e-4 at a = 256 (-> 1.35e-4 as a -> inf) |
| Gaussian, lam = 0.07, eta = 0.3 | inf, coarse grid (a <= 256, d <= 64) | 0.0656 | 0.0656 | 0.00185 |
| Gaussian, lam = 0.07, eta = 0.7 | inf, coarse grid | 0.0692 | 0.0692 | 0.0037 |
| same | inf, near diagonal (a = 1..64, d = 0.001..1) | 0.081 | 0.081 | 0.0068 |
| same | inf, small a (a = 0.002..0.7, d <= 96) | 1.41 | 0.075 | 0.106 |
| same | inf, stationary corner (a = 64..1024) | 0.0677 | 0.0677 | 0.00355 |
| same | 96 | 0.0654 | 0.0652 | 0.0040 |
| same | 30 | 0.0541 | 0.0527 | 0.0027 |
| same | 24 | 0.0475 | 0.0464 | 0.0022 |
| same | 18 | 0.0427 | 0.0383 | 0.0015 |
| same | 12 | 0.0276 | 0.0234 | -0.0003 (fails) |
| same | 1, 2, 3, 6, 9 | | | fails (large d) |
| lam = 0.07, eta = 0.75 | inf, critical regions | 0.0682 | 0.0682 | 0.0038 |
| lam = 0.07, eta = 0.8 / 0.85 / 1 | inf | | | 0.0020 / -0.0005 / -0.014 (near the diagonal) |

So the generalised certificate keeps L1, L2 at the level of the old one and raises the asymptotic L3 margin from
1.35e-4 to ~0.0036 (the budget bound is 0.0103). It fails for n <= 12, where the m3-note certificate is already proved.

A Markov correlation cannot do this: it is first order at its diagonal, while E = O((s-1)^2) as s -> 1, and the local
regime breaks (L2 = -0.156 at a = 0.05; `explore_markov_006.log`). The Gaussian correlation is second order there.

## 8. Theorem B: Conjecture F at (n, 3) for every n >= 37 (computer-assisted)

Notation of Sections 0-3: eps = 1/n, a = n log s, d = n log(t/s), b = a + d; F = E^R/(w(s) w(t)) for the Gaussian
design (lam = 7/100, eta = 7/10, R(u,v) = exp(-(Phi(u) - Phi(v))^2), Section 3); L1 = (log F)_a, L2 = -(log F)_b,
L3 = -F_ab/F (derivatives in the scaled variables).

**Exact list of what Lemma 4 needs.** By Lemma 4 of [`04-lower-half-new-cases.md`](../../math/04-lower-half-new-cases.md) and its smooth version, E^R is a
positive semidefinite kernel on (1, inf) as soon as
- (B0) F is continuous on {1 < s <= t} with F(s, s) = 1 (i.e. E^R(s,t) -> K_n(1,s,s) as t -> s+), and F is C^2 on
  an open set containing {1 < s <= t};
- (B1) F > 0, F_s >= 0, F_t <= 0, F_st <= 0 on {1 < s < t}, i.e. F > 0 and L1, L2, L3 >= 0 for all a, d > 0.
No condition at s -> 1 or t -> inf is needed (Lemma 4 is applied to finite point sets, which lie in compact
subsets of (1, inf)); but (B1) must hold at every point, so the verification has to reach every point of the open
quadrant {a > 0, d > 0}, uniformly up to its boundary. (B0) holds for every n: by the mixed form (F4) below, F is
real-analytic in (a, d) on a neighbourhood of {d >= 0} (with the analytic branch d sqrt(S(d)) of sqrt(kappa(d)),
which also defines the extension to d < 0), and at d = 0 the mixed form gives F = om_a/om_a = 1.

**Theorem B' (rigorous, computer-assisted).** For every integer n >= 37, and also for the limit kernel (eps = 0),
F > 0 and L1, L2, L3 > 0 at every point with a = n log s >= 3, i.e. for every pair 1 < s < t with s >= e^{3/n}.
(All 19 regions of the table in 8.3 VERIFIED, no failure; 1,084,767 boxes, 26,165 s of computation in total.)
Theorem B' is the part a >= 3 of Theorem B below; the strip 0 < a < 3, including the corner where s and t are both
close to 1, is Theorem B'' (8.4).

**Theorem B (rigorous, computer-assisted; not externally refereed).** For every integer n >= 37, and for the limit
kernel (eps = 0), the Gaussian-design certificate satisfies F > 0, F_s > 0, F_t < 0, F_st < 0 at every point
1 < s < t (Theorem B' for s >= e^{3/n}, Theorem B'' for s < e^{3/n}). Hence (B0) and (B1) hold, Lemma 4 makes E^R a
positive semidefinite kernel on (1, inf), and Proposition 6' gives A_{n,3}(A, B) >= Tr((A^{n/3} B)^3) for all positive
definite A, B: **Conjecture F at (n, 3), hence the lower half of OQP 40 at (n, 3) and (3, n), holds for every
n >= 37.** Together with the exact verifications for n <= 36 (Theorem 5 of `../../math/05-lower-half-m3.md`) it holds for every
n >= 1. Computation: 1,084,767 boxes (Theorem B') + 38,640 boxes and cells (Theorem B''), all VERIFIED; the
formulas are checked against the definitions (8.1, 8.4). The code and runs were checked independently: see `independent-check/CHECK_REPORT.md`.

### 8.1 eps-smooth closed forms (exact for eps = 1/n; at eps = 0 they give the limit kernel)

With c = 2/(1+eps), c2 = 2/((1+eps)(1+2eps)), phi1(x) = (e^x - 1)/x, and for z > 0
  nu(z) = eps/(1 - e^{-z eps}) = 1/(z phi1(-z eps)),  m(z) = nu(z) - eps = 1/(z phi1(z eps))  (both decreasing in z),
  P(z) = phi1(z(1+2eps))/phi1(z eps),  Q(z) = z phi1(z eps):
- (F1) kappa(z) := K_n(e^{z eps},1,1) = c (P(z) - 1)/Q(z) - e^{z/3}, W(z) := K_n(1,e^{z eps},e^{z eps}) =
  c (e^{z(1+eps)} - P(z))/Q(z) - e^{2z/3}, K_n(1,s,t) = c [e^{a(1+eps)} P(d) - P(a)]/Q(b) - e^{(a+b)/3}
  (from h_n(1,x,y) = ([x,y] - [1,x])/(y - 1), [x,y] = (y^{n+2} - x^{n+2})/(y - x), x = e^{a eps}, y = e^{b eps},
  C(n+2,2) = (1+eps)(1+2eps)/(2 eps^2)); E^R = K_n(1,s,t) - e^{a/2} sqrt(kappa(b) kappa(d)) R(b,d), w(s)^2 = W(a),
  w(t)^2 = W(b).
- (F2) nu-form: kappa(z) = c2 e^z nu_z^2 gam_z, W(z) = c e^z nu_z om_z, K_n(1,s,t) = c2 e^b nu_b nu_d khat, where
  p_z = e^{-z(1+2eps)} + (1+2eps) e^{-z(1+eps)}/nu_z, y_z = e^{-z/3}/(nu_z sqrt c2), gam_z = 1 - p_z - y_z^2,
  om_z = 1 - nu_z (1 - e^{-z(1+2eps)})/(1+2eps) - e^{-z/3}/(c nu_z), khat = 1 - u1 - u2 - y_b y_d,
  u1 = e^{-d(1+2eps)}, u2 = (1+2eps) [phi1(-a(1+2eps))/phi1(-a eps)] e^{-d(1+eps)}/nu_d; hence (using
  e^{a(1+2eps)} e^{d(1+2eps)} = e^{b(1+2eps)})
      F = e^{d/2} nu_d sqrt(nu_b/nu_a) D / ((1+2eps) sqrt(om_a om_b)),   D = khat - R sqrt(gam_b gam_d).
- (F3) perfect square (removes the leading cancellation K_n(1,s,t) ~ cap for large d): N = khat^2 - gam_b gam_d =
  (y_b - y_d)^2 + [p_b + p_d - 2u1 - 2u2] + (u1+u2)^2 + 2(u1+u2) y_b y_d - p_b p_d - p_b y_d^2 - p_d y_b^2 and
  D = N/(khat + sqrt(gam_b gam_d)) + sqrt(gam_b gam_d)(1 - R). In the code no growing or decaying exponential is
  left unnormalised: Dhat = e^{(1/2+lam) d} D, Phihat(z) = Phi(z) e^{mu z} with mu = (1/2 + lam)/2, 1 - R = x phi1(-x),
  x = e^{-(1/2+lam) d} (Phihat_b e^{-mu a} - Phihat_d)^2, and log F = -lam d + log nu_d + (log nu_b - log nu_a)/2
  - log(1+2eps) - (log om_a + log om_b)/2 + log Dhat.
- (F4) mixed form (small d): F = sqrt(nu_b/nu_a) Bm/sqrt(om_a om_b), Bm = e^{-d(1/2+eps)} [P(d) - nu_a (1 -
  e^{-a(1+2eps)})/(1+2eps)] - e^{-a/3} e^{-d/6}/(c nu_b) - (sqrt(c2 gam_b)/c) d sqrt(S(d)) R.
- (F5) S(x; eps) := kappa_n(x)/x^2 = sum_{k>=2} s_k(eps) x^{k-2} (entire in x) with the exact eps-polynomials
  s_k = 2 sum_{i+j=k} psi_i beta_j eps^j - 1/(3^k k!), psi_i = h_i(eps, 1+2eps)/(i+2)!, h_i(u,v) = sum_l u^l v^{i-l},
  (z/(e^z - 1))^2 = sum_j beta_j z^j; i.e. kappa_n(x) = 2 [x eps, x(1+2eps)]phi1 / phi1(x eps)^2 - e^{x/3}. Tail
  bounds: |beta_j| <= 13 (Cauchy on |z| = 1, where |phi1| >= 3 - e), |psi_i| <= v^i/(i+1)!, |d psi_i/d eps| <=
  2 v^i/i!, v = 1 + 2eps. Also nu_z om_z = z^2 S(-z)/c and c2 gam_z = z^4 phi1(-z eps)^2 S(z) e^{-z} (no cancellation
  for small z).
- Design function: for z <= 2 from the Taylor series of 2 sinh(z/2)/z, (1 - e^{-lam z})/z, kappa_inf(z)/z^2
  (degree 100, explicit tails); for z >= 2 Phihat(z) = -sqrt(z) phit(z), phit = sqrt(ell(y) eta (1 - q)/sqrt G),
  G = 1 - (1+z) e^{-z} - (z^2/2) e^{-2z/3}, q = e^{lam z} f_inf(z) = [(z - 1 + e^{-z}) e^{-(1/2-lam) z}/z +
  (z/2) e^{-(1/6-lam) z}]/(1 - e^{-z} + sqrt G), y = eta (1 - rr(z)) = eta z e^{-(1/2+lam) z} (1 - q)/sqrt G,
  ell(y) = -log(1 - y)/y (the cancellation-free forms of Lemma A2).

Checks (numerical, not part of the proof): (F1)-(F4) against direct 60-360 digit evaluation of the definitions at
128 points for n = 37, 50, 100, 1000 (a, d from 0.01 to 400): max relative deviation 3e-57; at eps = 0 against the
limit kernel 2e-65 (`tb_formulas_mp.log`). Ball values of L1, L2, L3 and their gradients from every form and every
chart against mpmath numerical differentiation of the definitions at ~300 points (n = 37, 50, 100, 1000, limit;
random points and points on every chart boundary): agreement to 2e-16 (the accuracy of the numerical
differentiation), reference values inside the chart balls, gradients to 8 digits (`tb_check_arb.log`,
`tb_check_v4.log`, `tb_check_charts.log`); S(x; eps) and dS/d eps against the closed form to 1e-32.

### 8.2 Verification method

python-flint arb balls (160 bits). Truncated Taylor jets in (a, b, eps), eps = 1/n being a jet variable; univariate
functions are composed through their Taylor coefficients (arb power series, or explicit series with rigorous tails;
Phihat through enclosures on cells of width 1/128 obtained by centred forms and bisected until every coefficient has
radius <= 2e-4). On a box with centre c and half-widths r_a, r_d, r_e (box edges: d/da at fixed d = d_a + d_b,
d/dd at fixed a = d_b):

    L_k(box) in L_k(c) + [(d_a + d_b) L_k](box) [-r_a, r_a] + [d_b L_k](box) [-r_d, r_d] + [d_eps L_k](box) [-r_e, r_e],

with L_k(c) computed from thin balls and the gradients from jets over the whole box. Option --dual: every
intermediate quantity is carried twice (thin centre, box) and, before every univariate function and after every
product, each Taylor coefficient Q_m of its box jet is replaced by the mean-value enclosure
Q_m(c) + [(d_a + d_b) Q_m] [-r_a, r_a] + [d_b Q_m] [-r_d, r_d] + [d_eps Q_m] [-r_e, r_e] (d_a Q_m = (m_a + 1) Q_{m+e_a},
etc.), intersected with the naive one. F > 0 on a box is implied by the evaluation itself (logarithms and square
roots of balls that must be positive). A box is accepted when all three lower bounds are > 0, otherwise bisected
(in the direction of the largest contribution). The jets compute the analytic interpolation in eps of the exact
finite-n quantities; every bound used holds for all real eps in [0, 1/37], so the result holds at eps = 1/n,
n >= 37, and at eps = 0.

### 8.3 Charts, coverage of {a >= 3}, and results

| chart | region | parametrisation, form, script |
|---|---|---|
| C1 core | 3 <= a <= 64, 3 <= d <= 512 | (a, d, eps); (F2)+(F3); `tb_bb.py --dual nu2` (on 16 <= a <= 64, 3 <= d <= 15/4 the mixed form (F4) instead) |
| C2 d-strip | 3 <= a <= 64, 0 <= d <= 3 | (a, d, eps); (F4); `tb_bb.py --dual mixed3` |
| C3 stationary tail | a >= 64, 0 <= d <= 512 | (m_a, eps, d), m_a = nu_a - eps in [0, 1/64]; `tb_tail2.py` |
| C4 far tail | 3 <= a <= 64, d >= 512 | (a, w, eps), w = 1/d in [0, 1/512]; `tb_dtail.py` |
| C5 double tail | a >= 64, d >= 512 | (m_a, w, eps), plain cells; `tb_ddouble.py` |

The union is {a >= 3, d >= 0}, for all eps in [0, 1/37]. Results (generated by `tb_table.py`, `tb_table.md`):

| chart | region (all eps in [0, 1/37]) | log | boxes / cells | time (s) | result |
|---|---|---|---|---|---|
| C3 stationary tail | a >= 64, 0 <= d <= 64 | `tb_tail2_A64.log` | 34689 | 202.8 | VERIFIED |
| C3 stationary tail | a >= 64, 64 <= d <= 512 | `tb_tail2_A64_far.log` | 165150 | 616.7 | VERIFIED |
| C5 double tail | a >= 64, d >= 512 | `tb_ddouble.log` | 256 | 0.0 | VERIFIED |
| C4 far tail | 3 <= a <= 64, d >= 512 | `tb_dtail.log` | 698 | 0.9 | VERIFIED |
| C1 core | 3 <= a <= 16, 3 <= d <= 16 | `tb_core_A1.log` | 279637 | 7374.7 | VERIFIED |
| C1 core | 16 <= a <= 64, 16 <= d <= 64 | `tb_core_A2a_hi.log` | 20469 | 644.5 | VERIFIED |
| C1 core | 16 <= a <= 64, 15/4 <= d <= 16 | `tb_core_A2a_lo1.log` | 246646 | 9036.9 | VERIFIED |
| C1 (mixed form) | 16 <= a <= 40, 3 <= d <= 15/4 | `tb_core_lo2_16_40.log` | 57232 | 1171.0 | VERIFIED |
| C1 (mixed form) | 40 <= a <= 64, 3 <= d <= 15/4 | `tb_core_lo2_40_64.log` | 62108 | 1274.7 | VERIFIED |
| C1 core | 3 <= a <= 16, 16 <= d <= 64 | `tb_core_A2b.log` | 6254 | 311.6 | VERIFIED |
| C1 core | 3 <= a <= 64, 64 <= d <= 512 | `tb_core_far.log` | 24073 | 1332.3 | VERIFIED |
| C2 d-strip | 3 <= a <= 8, 0 <= d <= 3 | `tb_dstrip_3_8.log` | 17239 | 425.3 | VERIFIED |
| C2 d-strip | 8 <= a <= 13, 0 <= d <= 3 | `tb_dstrip_8_13.log` | 13954 | 297.5 | VERIFIED |
| C2 d-strip | 13 <= a <= 18, 0 <= d <= 3 | `tb_dstrip_13_18.log` | 15780 | 333.1 | VERIFIED |
| C2 d-strip | 18 <= a <= 23, 0 <= d <= 3 | `tb_dstrip_18_23.log` | 16300 | 337.5 | VERIFIED |
| C2 d-strip | 23 <= a <= 28, 0 <= d <= 3 | `tb_dstrip_23_28.log` | 16402 | 347.8 | VERIFIED |
| C2 d-strip | 28 <= a <= 33, 0 <= d <= 3 | `tb_dstrip_28_33.log` | 16366 | 478.0 | VERIFIED |
| C2 d-strip | 33 <= a <= 48, 0 <= d <= 3 | `tb_dstrip_33_48.log` | 45180 | 988.7 | VERIFIED |
| C2 d-strip | 48 <= a <= 64, 0 <= d <= 3 | `tb_dstrip_48_64.log` | 46334 | 991.3 | VERIFIED |

**C3 (a >= 64).** For a >= A every a-dependent quantity is a function of m_a = 1/(a phi1(a eps)) in (0, 1/a] and of
exponentially small atoms: nu_a = m_a + eps, nu_b = nu_a/(e^{-d eps} + nu_a d phi1(-d eps)), m_b = m_a (nu_b/nu_a)
e^{-d eps}, d nu/da = -nu m, d^2 nu/da^2 = nu m (nu + m), (log nu)' = -m, (log nu)'' = nu m (same in b). The
eps-direction of the jets is d/d eps at fixed (m_a, d); a = log(1 + eps/m_a)/eps and |da/d eps| = a^2 phi2(-a eps)
<= a^2/2 (phi2(x) = (e^x - 1 - x)/x^2). On a box [m0, m1] x [e0, e1] x [d0, d1] the atoms are bounded with
a_min = log(1 + e1/m1)/e1 (the smallest a on the box; >= 37 here), so the bounds hold at every point of the box:
Q1 = e^{-a/3}/(nu_b sqrt c2) <= (a + d) e^{-a/3}, Q2 = e^{-a}(e^{-2 eps b} + (1+2eps) e^{-eps b}/nu_b) <=
2 e^{-a}(1 + 3b), e^{-a/3}/(c nu_a) <= 2a e^{-a/3}, e^{-a(1+2eps)} <= e^{-a}, PH = Phihat(b) e^{-mu a} (Lemma T);
the (a, b)-Taylor coefficients of order <= 2 of an atom Z are <= the bound for Z (derivative factors <= 1), its
eps-coefficients are <= Z (a^2 + a + d + 2) (from |da/d eps| <= a^2/2, |d log nu_b/d eps| <= b + m_b a^2/2,
|d log nu_a/d eps| <= a), and all these bounds decrease in a for a >= 30, d <= 512, so they are taken at
a = a_min, d = d_hi.

**Lemma T.** For real b >= 30 and |zeta - b| <= 1 (so Re zeta >= 29, |zeta| <= b + 1): |1 - G(zeta)| <= 2e-6,
|q(zeta)| <= 0.47, |y(zeta)| <= 2e-6, hence |phit(zeta)| <= 1.02 (principal branches; all square-root and log
arguments stay in the right half-plane) and |Phihat(zeta)| <= 1.02 sqrt(b+1). By Cauchy's estimate
|Phihat^{(k)}(b)/k!| <= 1.02 sqrt(b+1); multiplying by the a-jet of e^{-mu a}, every Taylor coefficient of PH is
<= 2.4 sqrt(a + d + 1) e^{-mu a}. (Bounds: |e^{-c zeta}| = e^{-c Re zeta}; e.g. |q| <= [(|zeta| + 2) e^{-0.43 x}/|zeta|
+ (|zeta|/2) e^{-0.0967 x}]/1.99 with x = Re zeta >= 29.)
**Lemma T'.** For z >= 400 the same discs give |phit(zeta) - sqrt eta| <= 2(z+1) e^{-(1/6-lam)(z-1)}; hence
|phit(z) - sqrt eta| and |phit^{(k)}(z)/k!| (k <= 3) are <= 4e-19 for z >= 512.
**C4 (d >= 512).** With w = 1/d and m_d in [0, w] (enclosed on each (w, eps) cell by monotonicity),
log F = -lam d + log(d nu_d) + (log nu_b - log nu_a)/2 - log(1+2eps) - (log om_a + log om_b)/2 + log(Dhat/d),
Dhat/d = sg [phit_d - sqrt(1 + a w) phit_b e^{-mu a}]^2 psi + tau Ntil nu_d^2/(khat + sg), tau = e^{-(1/6-lam)d}/(d nu_d^2)
<= d e^{-(1/6-lam) d}; d-jets: (log(d nu_d))' = w - m_d, '' = -w^2 + nu_d m_d, ''' = 2w^3 - nu_d m_d (nu_d + m_d),
w' = -w^2; nu_b = nu_d/(e^{-a eps} + nu_d a phi1(-a eps)).
**Lemma T''.** For d >= 512 and 3 <= a <= 64 (so b = a + d >= 515), using 1/nu_z <= z, nu_z <= 1, m_z <= 1/z:
(i) p_z <= (1 + 1.06 z) e^{-z} and y_z^2 <= z^2 e^{-2z/3}, so |gam_z - 1| <= 2 z^2 e^{-2z/3} (z = b, d), and
|sg - 1| <= 4 b^2 e^{-2d/3}; (ii) |khat - 1| <= (1 + 1.06 d) e^{-d} + b d e^{-2d/3}; (iii) psi = phi1(-x) with
0 <= x <= 4 d e^{-(1/2+lam) d}, |psi - 1| <= x; (iv) |om_b - 1 + nu_b/(1+2eps)| <= e^{-b} + b e^{-b/3};
(v) 0 <= tau Ntil nu_d^2/(khat + sg) <= 4 d e^{-(1/6-lam) d} (Ntil nu_d^2 <= 8, khat + sg >= 2 - 1e-100). The largest
is (v), <= 7e-19 at d = 512 and decreasing in d. Each term is a product of factors z^k e^{-cz} and of smooth factors
whose logarithmic derivatives are bounded by 1 + c in modulus, so all its Taylor coefficients of order <= 3 are at
most 8 times its bound; the code encloses each of these quantities, with all coefficients, in [-1e-12, 1e-12].
**C5** uses the same bounds and, for a >= 64, |e^{-a/3}/(c nu_a)| <= a e^{-a/3} <= 4e-8 and
|sqrt(1 + a w) phit_b e^{-mu a}| <= 1.2 sqrt(1 + a/512) e^{-mu a} <= 2e-8 (coefficients at most (1 + mu)^3 times
larger), enclosed in [-1e-6, 1e-6]; nu_b in [eps, max(nu_a, nu_d)], m_b in [0, 1/(a + d)] subset [0, 1/576].

### 8.4 The strip 0 < a < 3 and the corner a, d -> 0 (Theorem B'')

**Theorem B'' (rigorous, computer-assisted).** For every integer n >= 37, and for the limit kernel (eps = 0), F > 0
and L1, L2, L3 > 0 at every point with 0 < a < 3 and d > 0, i.e. for all 1 < s < e^{3/n}, t > s.
(Charts S0-S4 below, all VERIFIED, no failure; 38,640 boxes and cells, 3,397 s of computation.)

**No factor a^2 left.** E^R(0, b) = 0 and d_a E^R(0, b) = 0 for every b: at s = 1, K_n(1,1,t) = kappa(b) =
cap R because R(b, b) = 1; by Euler's relation for the symmetric, degree-n homogeneous K_n at (1, 1, t),
d_a K_n(1, e^{a eps}, t)|_{a=0} = (kappa(b) - kappa'(b))/2 = d_a [e^{a/2} sqrt(kappa(b) kappa(b - a))]|_{a=0}, and
d_a R(b, b - a)|_{a=0} = 0. Hence X := E^R/a^2 = int_0^1 (1-u) d_a^2 E^R(ua, b) du is real-analytic on a neighbourhood
of {0 <= a <= 3, b >= 0}, the corner included (with the analytic branches kappa(z) = z^2 S(z),
sqrt(kappa(b) kappa(d)) = b d sqrt(S(b) S(d)), which define the continuation to d < 0), and X(0,0) = s_2(eps) > 0.
With W(z) = z^2 e^z S(-z):

    F = (a/b) Hhat,   Hhat = X e^{-(a+b)/2} / sqrt(S(-a) S(-b)),   Ghat = log Hhat   (Hhat(0,0) = 1),
    a L1 = 1 + a Ghat_a,   b L2 = 1 - b Ghat_b,   a b L3 = 1 - b Ghat_b + a Ghat_a - a b (Ghat_ab + Ghat_a Ghat_b),
    and for b > 0:  L2 = 1/b - Ghat_b,   a L3 = L2 - a (Ghat_ab + Ghat_a (Ghat_b - 1/b)).

So all conditions are statements about the bounded functions Ghat_a, Ghat_b, Ghat_ab; at the corner a L1, b L2,
a b L3 -> 1 (the scale-invariant margins), and as a -> 0 the leading margin is L2 = 1/b - Ghat_b(0, b) (the
"c'(b) < 0" condition of the plan, verified here as part of the boxes touching a = 0). The (s-1)^2 factorisation of
the previous version of this section is not needed. Forms used for X (exact identities, eps-smooth):
- direct (F1): K_n(1,s,t) = c N1/(b phi1(b eps)) - e^{(a+b)/3}, N1 = e^{a(1+eps)} P(d) - P(a); cap R as above;
- corner: N1(a, 0) = 0 because P(-a) = e^{-a(1+eps)} P(a) (phi1(-x) = e^{-x} phi1(x)), so N1/b is analytic and
  K_n(1,s,t) = c (N1/b)/phi1(b eps) - e^{(a+b)/3} near b = 0;
- nu-form (F2)+(F3): Ghat = -lam d + log nu_d - log S(-a)/2 + log(c)/2 + (log nu_b - log om_b)/2 - log(1+2eps)
  + log(Dhat/a^2) + log b, with gam_z = z^4 phi1(-z eps)^2 S(z) e^{-z}/c' for z <= 8 (no cancellation) and the
  nu-form gam_z for z > 8;
- far tail d >= 512: chart C4 for G = log(F/a) = Ghat - log b (see S4).

**Method (`tb_sx.py`).** Taylor models in a. Every quantity is, for each slot (j, k) (Taylor order j in b, order k <= 2
in eps; j <= 3 - k in the strip, j <= 10 - k in the corner), an arb power series in a of length 16 (C-level arb_series
arithmetic; products truncated; univariate functions composed with their Taylor coefficients, enclosures valid on the
whole argument ball: exp, log, sqrt, 1/x, phi1 as in 8.2; S(x; eps) from 120 exact eps-polynomial terms with
eps-Taylor coefficients up to order 3 and tails from Cauchy's estimate on |zeta - eps| <= 1/37; Phihat from cached
cells of width 1/128 with centred forms, on [-2, 2] its convergent series). Three evaluations per box
[a0, a1] x [b0, b1] x [e0, e1]:
- centre P (a_c, b_c, eps_c thin), face F (a = a_c thin; b, eps balls), box B (a, b, eps balls);
- F is tightened against P before every univariate function and after every product,
  F_{j,k} <- P_{j,k} + sum_{1<=q<Q} C(j+q,q) P_{j+q,k} Db^q + C(j+Q,Q) F_{j+Q,k} Db^Q + (k+1) F_{j,k+1} Deps (Q = top
  b-order of row k minus j; Taylor in b at eps_c, mean value in eps), intersected with the naive F;
- a_c = 0 if a0 = 0 (else the midpoint). At a_c = 0 the a-series of E^R (P and F) is divided by a^2 by a shift (the
  dropped coefficients are checked to contain 0), the box series by the same shift, which is valid because
  X^{(m)}(a)/m! = int_0^1 (m+1)(m+2)(1-u) u^m E^R_{m+2}(ua) du is a weighted mean of the (m+2)-th a-coefficients of E^R on
  [0, a]; in the corner N1/b is obtained in the same way by a shift of the b-slots (weighted mean in b);
- the box series of X is then replaced by its Taylor expansion from the tightened face,
  X_m <- sum_{l < 15-m} C(m+l,l) Xf_{m+l} Da^l + C(15, m) Xb_15 Da^{15-m} (intersected with the naive one), so that the
  cancellation in E^R meets interval arithmetic in the a-direction only through the top coefficient times Da^{15-m};
  with option --box the same Taylor shift is applied to the box values before every univariate function;
- each needed coefficient of Ghat (Ghat_a = c_{1,0}, Ghat_b = c_{0,1}, Ghat_ab = c_{1,1}) is enclosed on the box by
  the same Taylor model in a (face coefficients tightened as above, the top one from the box), and a L1 = M1,
  L2 > 0 (M2 > 0 or N2 > 0), L3 > 0 (M3 > 0 or N3 > 0) and X > 0 are checked in interval arithmetic with a in [a0, a1],
  b in [b0, b1]. A box that fails is bisected in b, eps or a (largest contribution to the enclosure widths).
Boxes are in coordinates (a, b) and may straddle the diagonal; there the analytic continuation to d < 0 is evaluated
(cap = e^{a/2} b d sqrt(S(b) S(d)) changes sign with d); this only enlarges what is verified. All bounds hold for every
real eps in [0, 1/37], so the result holds at eps = 1/n (n >= 37) and at eps = 0.

**Charts and coverage of {0 < a < 3, d > 0}** (every chart for all eps in [0, 1/37]):

| chart | region | form, script |
|---|---|---|
| S0 corner | 0 <= a <= 1/4, 0 <= b <= 1/4 | direct with N1/b by shift; Taylor model at (0,0), b-order 10; `tb_sx_run.py corner` |
| S1 | 12 a-strips [x0, x0 + 1/4] of [0, 3], 1/4 <= b <= x0 + 4 | direct (F1); `tb_sx_run.py direct 0 3 1/4 4 1/8 12 4` |
| S2 | 24 a-strips [y0, y1] of width 1/8, y1 + 15/4 <= b <= 15/2 | nu-form, --box; `tb_sx_run.py --box nu 0 3/2 15/4 15/2 12 64 4` and `... nu 3/2 3 ...` |
| S3 | 6 a-strips of width 1/2, 15/2 <= b <= 515 | nu-form; `tb_sx_run.py nu 0 3 15/2 515 6 16 4` |
| S4 far tail | 0 <= a <= 3, d >= 512 | C4 for G = log(F/a); `tb_sx_dtail.py 512 0 3 4 8 8` |

Coverage. Let 0 < a < 3, b > a. If b <= 1/4: S0. Let x0 = floor(4a)/4 and [y0, y1] the strip of width 1/8 containing
a; then y1 <= x0 + 1/4. If 1/4 <= b <= x0 + 4: S1. If x0 + 4 <= b <= 15/2: then b >= y1 + 15/4, so S2. If
15/2 <= b <= 515: S3. If b >= 515: d = b - a > 512: S4. The charts overlap (S1/S2 on y1 + 15/4 <= b <= x0 + 4, S2/S3 and
S3/S4 on their common boundaries), and S1-S4 overlap Theorem B' (8.3) along a = 3.

S4 (far tail, `tb_sx_dtail.py`). As C4 with w = 1/d and (w, eps) cells, but for G = log(F/a):
G = -lam d + log(d nu_d) + (log nu_b - log om_b)/2 - log S(-a)/2 + log(c)/2 - log(1+2eps) + log(Dhat/(a^2 d)),
Dhat/(a^2 d) = sg (M/a)^2 psi + tau (Ntil nu_d^2/a^2)/(khat + sg), and from Phihat(z) = -sqrt(z) phit(z)
M/a = phit_d g(a, w) + sqrt(1 + a w) e^{-mu a} (phit_d - phit_b)/a, g(a, w) = (1 - sqrt(1 + a w) e^{-mu a})/a
= -v phi1(a v), v = -mu + (w/2) log(1 + a w)/(a w) (analytic at a = 0, g(0, w) = mu - w/2 > 0.28). Bounds:
(phit_d - phit_b)/a = -int_0^1 phit'(b - (1-u) a) du has all (a, b)-Taylor coefficients of order <= 3 below
24 * 3.6e-19 (Lemma T' and Cauchy on unit discs), enclosed in [-1e-15, 1e-15]; Ntil nu_d^2 = T1 + T2 with
T1/a^2 = ((nu_d/nu_b) e^{-a/3} - 1)^2/(a^2 c'), ((nu_d/nu_b) e^{-a/3} - 1)/a = -(1/3 + eps) phi1(-a(1/3+eps))
+ nu_d phi1(-a eps) e^{-a/3} (modulus <= 2 on complex unit discs around [0, 3]), and T2 (the other terms of the perfect
square, times e^{2d/3} nu_d^2) <= 20 (2 + b)^2 e^{-(d-1)/3} there and vanishing to second order at a = 0; with
tau <= d e^{-(1/6-lam) d} the tau-term and its coefficients of order <= 3 are < 1e-15 for d >= 512; the remaining atoms
(phit_d - sqrt eta, sg - 1, psi - 1, om_b - 1 + nu_b/(1+2eps)) as in Lemma T''; all enclosed in [-1e-12, 1e-12].
Conditions N1 = 1 + a G_a = a L1, N2 = -G_b = L2, N3 = -G_b - a (G_ab + G_a G_b) = a L3 at the centre plus the
a-gradient on the box.

Results (`tb_sx_table.py` -> `tb_sx_table.md`; lower bounds are the smallest certified box lower bounds of the
conditions actually used in each chart, not the true minima):

| chart | region (all eps in [0, 1/37]) | log | boxes | time (s) | certified lower bounds | result |
|---|---|---|---|---|---|---|
| S0 corner | 0 <= a <= 1/4, 0 <= b <= 1/4 | `tb_sx_corner.log` | 1 | 1.0 | aL1 >= 0.9176, abL3 >= 0.7504, bL2 >= 0.9045 | VERIFIED |
| S1 direct | 0 <= a <= 3 (12 strips), 1/4 <= b <= x0 + 4 | `tb_sx_direct.log` | 14491 | 740.6 | L2 >= 0.09819, aL1 >= 0.9905, aL3 >= 5.989e-05 | VERIFIED |
| S2 nu, --box | 0 <= a <= 3/2 (12 strips of 1/8), y1 + 15/4 <= b <= 15/2 | `tb_sx_nu_low_a.log` | 10122 | 1106.3 | L2 >= 0.05144, aL1 >= 0.9652, aL3 >= 2.647e-05 | VERIFIED |
| S2 nu, --box | 3/2 <= a <= 3 (12 strips of 1/8), y1 + 15/4 <= b <= 15/2 | `tb_sx_nu_low_b.log` | 652 | 56.7 | L2 >= 0.1365, aL1 >= 0.9999, aL3 >= 0.0001879 | VERIFIED |
| S3 nu | 0 <= a <= 3 (6 strips), 15/2 <= b <= 515 | `tb_sx_nu.log` | 13118 | 1481.1 | L2 >= 0.02818, aL1 >= 0.3046, aL3 >= 2.133e-05 | VERIFIED |
| S4 far tail | 0 <= a <= 3, d >= 512 | `tb_sx_dtail.log` | 256 | 11.4 | a L1 >= 0.8065, L2 >= 0.06803, a L3 >= 0.05467 | VERIFIED |

Total: 38,640 boxes and cells, 3,397 s. S3 was run before the series form of gam_z (z <= 8) was introduced for S2; it
used the nu-form gam_z throughout (both are exact identities; the current code would use the series form for 15/2 <= b <= 8).

Checks (numerical, not part of the proof): `tb_sx_test.log` (Ghat_a, Ghat_b, Ghat_ab of the direct and nu forms at thin
centres, a = 0 (reference at a = 1e-20), a = 1/8 ... 3, d = 1e-6 ... 497, n = 37, 100, 1000 and the limit, against
mpmath numerical differentiation of the definitions: max deviation 2e-17; the corner expansion at (0,0) evaluated at
(a, b) = (0.01, 0.02), (0.05, 0.06), (0.1, 0.3), (0.2, 0.25), (0.3, 0.5), (0.5, 0.55): 0 to 1e-16 at small (a, b), up to
3e-6 at (0.5, 0.55) = truncation of the order-10 polynomial, which the proof bounds by the remainder);
`tb_sx_dtail_test.log` (far-tail form against the definitions at 7 points with d = 512 ... 2000, a = 0.001 ... 3:
max deviation 1.3e-17).

### 8.5 N0

The conditions hold for every n >= 37 and in the limit, with no negative margin anywhere (Theorems B' and B''); smaller
N0 were not attempted (numerically the design fails only for n <= 12, Section 3; n <= 36 is covered by the exact
verifier anyway). The regime that limits N0 numerically, the transition stationary/far (a ~ 64, d ~ 32-48), lies in
C3 and C1 and is verified for all n >= 37 (see the table).

### 8.6 Proposition 6' end to end at n = 37, 40 (numerical)

`endtoend_general.py n 6 2.0 digits`: 6 random pairs (A, B), r = 3..6 distinct eigenvalues of A (multiplicities
1-2), d <= 12. n = 37: identity p - tr((A^{n/3}B)^3) = Phi_B(K_n) = 3 sum <R^(l), G^(l)> to 4.0e-37 (40 digits) and
6.1e-58 (60 digits); smallest normalised eigenvalue of all G^(l): -2.3e-41 (40 digits), -3.4e-63 (60 digits), i.e.
a zero eigenvalue up to the working precision (repeated eigenvalues of A make the below block singular);
min p/tr = 1.0035. n = 40: 2.3e-37 / 5.8e-58; -1.4e-41 / +1.4e-61; min p/tr = 1.0102.
(`endtoend_general_n37.log`, `endtoend_general_n37_60d.log`, `endtoend_general_n40.log`, `endtoend_general_n40_60d.log`.)

### 8.7 Reproduction (venv python, OMP_NUM_THREADS=1; each verification prints RESULT: REGION VERIFIED or FAILED)

    python tb_formulas_mp.py > tb_formulas_mp.log      # closed forms vs definitions (numerical)
    python tb_check_arb.py > tb_check_arb.log          # ball values and gradients vs definitions (numerical)
    python tb_check_v4.py > tb_check_v4.log
    python tb_check_charts.py > tb_check_charts.log
    python tb_tail2.py 64 0 64 2 4 > tb_tail2_A64.log                       # C3
    python tb_tail2.py 64 64 512 2 4 > tb_tail2_A64_far.log                 # C3
    python tb_ddouble.py 4 4 16 > tb_ddouble.log                            # C5
    python tb_dtail.py 512 3 64 4 8 > tb_dtail.log                          # C4
    python tb_bb.py --dual nu2 3 16 3 16 0 1 1 37 26 26 > tb_core_A1.log    # C1
    python tb_bb.py --dual nu2 16 64 16 64 0 1 1 37 24 24 > tb_core_A2a_hi.log
    python tb_bb.py --dual nu2 16 64 15/4 16 0 1 1 37 24 49 > tb_core_A2a_lo1.log
    python tb_bb.py --dual mixed3 16 40 3 15/4 0 1 1 37 24 3 > tb_core_lo2_16_40.log   # and 40..64
    python tb_bb.py --dual nu2 3 16 16 64 0 1 1 37 13 24 > tb_core_A2b.log
    python tb_bb.py --dual nu2 3 64 64 512 0 1 1 37 61 56 > tb_core_far.log
    python tb_bb.py --dual mixed3 28 33 0 3 0 1 1 37 5 6 > tb_dstrip_28_33.log  # C2, likewise 3..8, ..., 23..28, 33..48, 48..64 (run_tb_guarded2.sh)
    python tb_table.py                                                      # table of 8.3
    python tb_sx_test.py > tb_sx_test.log ; python tb_sx_dtail_test.py > tb_sx_dtail_test.log   # strip forms vs definitions
    python tb_sx_run.py corner > tb_sx_corner.log                           # S0
    python tb_sx_run.py direct 0 3 1/4 4 1/8 12 4 > tb_sx_direct.log        # S1
    python tb_sx_run.py --box nu 0 3/2 15/4 15/2 12 64 4 > tb_sx_nu_low_a.log   # S2 (and 3/2 3 ... > tb_sx_nu_low_b.log)
    python tb_sx_run.py nu 0 3 15/2 515 6 16 4 > tb_sx_nu.log               # S3
    python tb_sx_dtail.py 512 0 3 4 8 8 > tb_sx_dtail.log                   # S4
    python tb_sx_table.py > tb_sx_table.md                                  # table of 8.4
    python tb_scan_strip.py > tb_scan_strip.log                             # numerical evidence for a < 3
    python endtoend_general.py 37 6 2.0 40 ; python endtoend_general.py 40 6 2.0 60

Library: `tb_arb.py` (jets, functions, forms (F2)-(F5), dual jets), `tb_tail.py`/`tb_tail2.py` (C3), `tb_dtail.py`
(C4), `tb_ddouble.py` (C5), `tb_bb.py` (C1, C2), `tb_sx.py` (Taylor models in a for the strip, S0-S3),
`tb_sx_run.py` (strip driver), `tb_sx_dtail.py` (S4), `tb_astrip.py`, `tb_strip6.py` (earlier strip approaches that fail,
kept for reference), `tb_formulas_mp.py` (mpmath versions and the reference definitions).
