# Proof of E(theta, X, Y) >= 0

Ansh Mishra, Aryan Senthilkumar

Last step of the local (second-order) form of Conjecture TF at commuting pairs (OQP 40 work).

Status: PROVED (analytic arguments + rigorous ball arithmetic; re-run and spot-checked independently by us, see
`independent-checks/`; not refereed externally); see Section 9 for the region table and
Section 10 for the commands.  Everything below is either an analytic argument written out here or a rigorous
ball-arithmetic computation (Arb via python-flint); purely numerical checks are labelled "numerical".

**Route.** In the coordinates x = X, y = rY one has E = theta x^2 y^2 H with H = g - tm (Lemma 2.2), g the
Golden-Thompson covariance term (positive, increasing in x and y), tm the remaining term.  (1) On the boundary
s = x + y = 0 the function H has a closed form and H(theta,x,-x) >= H(1/2,x,-x) = (2 sinh^2 t + tanh^2 t - 3t^2)/(8t^4)
> 0 (Theorem 3.1, analytic).  (2) In the compact square |x|, |y| <= 10 every box is certified either to have H > 0 or,
near the degenerate corner (theta, x, y) = (1/2, 0, 0), to have dH/ds > 0 at fixed (theta, x - y); integrating down
to s = 0 and using (1) gives H >= 0 (Lemma 4.1).  Boxes near the corner use Taylor models with Cauchy-type error
bounds (Section 6); the rest use interval arithmetic with monotone enclosures (Section 5).  (3) For
max(x, y) >= 10 explicit bounds give H > 0 (Section 7).

---------------------------------------------------------------------------------------------------

## 0. Statement

For theta in (0, 1/2] and real X, Y with Delta := theta X + (1-theta) Y >= 0 put r = (1-theta)/theta,
x = X, y = rY, p = e^X - 1, q = e^Y - 1, phi(s) = (e^s - 1)/s and

    E   = E_GT + E_m1,
    E_GT = theta [ x y (e^{x+y} - 1)/(x+y) - (e^x - 1)(e^y - 1) ],
    E_m1 = theta x y (1 - e^{-theta(x+y)})/(x+y)
           + p q/(p-q)^2 [ (1-theta) p (e^{theta(Y-X)} - 1) + theta q (e^{(1-theta)(X-Y)} - 1) ]

(removable singularities at x + y = 0 and at p = q filled in by continuity).

**Theorem.** E(theta, X, Y) >= 0 on the whole domain; E = 0 exactly when XY = 0.

Cross-check of the closed form against the integral definition
E = int_0^1 [N0 e^{N0 l} + e^{-l}] K du (numerical, mpmath 50 digits, 60 random points): max relative
difference 2.7e-48 (`verify_closed_form.py`).

---------------------------------------------------------------------------------------------------

## 1. Notation

* kappa = theta/(1-theta) = 1/r, so Y = kappa y;  s := x + y = Delta/theta (domain: s >= 0);
  d := x - y;  D := X - Y = x - kappa y.
* phi(z) = (e^z-1)/z = int_0^1 e^{zt} dt,  phi2(z) = (e^z - 1 - z)/z^2,
  psi(z) = 1/z - 1/(e^z - 1) = phi2(z)/phi(z),  mu(z) = 1 - psi(z) = 1/(1-e^{-z}) - 1/z.
  phi is increasing and log-convex on R (moment generating function of U ~ Unif[0,1]); mu(z) is the mean of
  the density e^{zt}/phi(z) on [0,1], hence increasing, and psi is decreasing; psi(z) + psi(-z) = 1.
* Divided differences of exp: exp[a,b] = e^a phi(b-a),  ee(a,b,c) := exp[a,b,c].  By Hermite-Genocchi
  ee(a,b,c) = int_{tau_i >= 0, tau_1+tau_2 <= 1} e^{(1-tau_1-tau_2) a + tau_1 b + tau_2 c} dtau, entire, and for
  real nodes increasing in each node.
* p = e^x - 1, q = e^Y - 1, Qa(u) = 1 + u p, Qb(u) = 1 + u q, l(u) = theta log Qa + (1-theta) log Qb,
  V(u) = Qa^{-1-theta} Qb^{-2+theta} = e^{-l}/(Qa Qb),
  J = int_0^1 V du,  J_1 = int_0^1 u V du.

## 2. Identities and elementary lemmas (analytic)

**Lemma 2.1 (the p, q term).** For theta in (0,1):
 (a) pq/(p-q)^2 [ (1-theta) p (e^{-theta D} - 1) + theta q (e^{(1-theta) D} - 1) ] = - theta (1-theta) p q J;
 (b) J   = [ e^Y ee(0,(1-theta)D, D) + ee(0, -theta D, (1-theta)D) ] / ( e^{2Y} phi(D)^2 );
 (c) J_1 = ee(0, -theta D, (1-theta)D) / ( e^{2Y} phi(D)^2 ).

*Proof.* For p != q substitute R = Qa/Qb (monotone in u, R(0) = 1, R(1) = e^D). Then
1 + uq = (p-q)/(p - qR), du = (1+uq)^2 dR/(p-q), u = (R-1)/(p - qR), and
J = (p-q)^{-2} int_1^{e^D} R^{-1-theta} (p - qR) dR,  J_1 = (p-q)^{-2} int_1^{e^D} R^{-1-theta} (R - 1) dR.
Integrating, J = (p-q)^{-2} [ p (1 - e^{-theta D})/theta - q (e^{(1-theta)D} - 1)/(1-theta) ], which is (a).
With p - q = e^Y (e^D - 1) = e^Y D phi(D), p - qR = e^Y (e^D - R) + (R - 1), and
int_1^{e^D} R^{-1-theta}(e^D - R) dR = D [e^D phi(-theta D) - phi((1-theta)D)] = D^2 ee(0,(1-theta)D,D),
int_1^{e^D} R^{-1-theta}(R - 1) dR = D [phi((1-theta)D) - phi(-theta D)] = D^2 ee(0,-theta D,(1-theta)D),
which gives (b), (c).  Both sides are continuous at p = q.  []

**Lemma 2.2 (normal form).** E = theta x y Phi with
  Phi = C_GT + theta C_m1,  C_GT = phi(s) - phi(x) phi(y),  C_m1 = phi(-theta s) - phi(x) phi(Y) J.
Phi vanishes identically on x = 0 and on y = 0; hence
  H := E/(theta x^2 y^2) = Phi/(xy) = g - tm,   g := C_GT/(xy),   tm := -theta C_m1/(xy)
extends analytically across the axes, and E >= 0 <=> H >= 0 off the axes (E = 0 on the axes).

*Proof.* E_GT = theta xy [phi(s) - phi(x)phi(y)] directly. The first term of E_m1 is
theta xy (1-e^{-theta s})/s = theta^2 xy phi(-theta s). By Lemma 2.1(a) the second term is
-theta(1-theta) pq J, and theta(1-theta) pq = theta(1-theta) x phi(x) kappa y phi(Y) = theta^2 xy phi(x) phi(Y)
(as (1-theta) kappa = theta), so E_m1 = theta^2 xy C_m1.
On y = 0 (q = 0): J = (1 - e^{-theta x})/(theta p) = phi(-theta x)/phi(x), so C_m1 = 0, and C_GT(x,0) = 0.
On x = 0 (p = 0): J = (1 - e^{-(1-theta)Y})/((1-theta) q) = phi(-theta y)/phi(Y) (as (1-theta)Y = theta y), so
C_m1 = 0, and C_GT(0,y) = 0.  []

**Lemma 2.3 (the Golden-Thompson part g).** With S, T independent Unif[0,1] and
D_x(a,b) = int_0^1 e^{x(b + v(a-b))} dv:
  g(x,y) = (1/2) E[(S-T)^2 D_x(S,T) D_y(S,T)]                         (Chebyshev covariance identity).
Consequences: (i) g > 0; (ii) g is increasing in x and in y (d/dx D_x >= 0 since b + v(a-b) in [0,1]);
(iii) for complex x, y: |g(x,y)| <= g(Re x, Re y) (|D_x| <= D_{Re x});
(iv) g = phi(x)phi(y) (mu(x) - mu(-y))/s (direct algebra);  (v) g(x,-x) = (phi(x)phi(-x) - 1)/x^2
= (2 cosh x - 2 - x^2)/x^4 =: G0(x) = 1/12 + sum_{k>=3} 2 x^{2k-4}/(2k)!, increasing in |x|.

**Lemma 2.4 (second formula for tm).** Let u* := theta psi(Y) + (1-theta) psi(x) in (0,1). For s != 0,
  tm = kappa phi(x) phi(Y) (u* J - J_1)/s = kappa phi(x) phi(Y) [u* e^Y E1 - (1-u*) E2]/(e^{2Y} phi(D)^2 s),
E1 = ee(0,(1-theta)D,D), E2 = ee(0,-theta D,(1-theta)D).

*Proof.* u* = Delta/(XY) - theta/q - (1-theta)/p. Since Qa Qb l'(u) = theta p + (1-theta) q + u pq and
V = e^{-l}/(Qa Qb): J_1 + (theta/q + (1-theta)/p) J = (pq)^{-1} int_0^1 l' e^{-l} du = (1 - e^{-Delta})/(pq).
Hence u* J - J_1 = (Delta/(pq)) [phi(X)phi(Y) J - phi(-Delta)] = -(Delta/(pq)) C_m1, and with Delta = theta s,
pq/(xy) = kappa phi(x) phi(Y) the claim follows; the second form is Lemma 2.1(b,c).  []

**Lemma 2.5 (crude bounds).** On the domain (s >= 0):
 (a) l is concave on [0,1] with l(0) = 0, l(1) = Delta >= 0, so l >= 0 and e^{-l} <= 1;
 (b) A := phi(x) phi(Y) J <= phi(x)phi(Y) int_0^1 du/(Qa Qb) = phi(x) phi(Y)/exp[x,Y];
 (c) if x, Y >= 0 then exp[x,Y] >= max(phi(x), phi(Y)), so A <= min(phi(x), phi(Y));
 (d) 0 < phi(-theta s) <= 1, and tm <= kappa A/s for s > 0 (Lemma 2.4 with u* <= 1, J_1 >= 0).

---------------------------------------------------------------------------------------------------

## 3. The boundary s = 0 (analytic)

**Theorem 3.1.** For theta in (0, 1/2] and x != 0:
  H(theta, x, -x) >= H(1/2, x, -x) = (2 sinh^2 t + tanh^2 t - 3 t^2)/(8 t^4) > 0,   t = x/2.

*Proof.* On s = 0: Y = -kappa x, D = x/(1-theta); put a = theta D = kappa x, b = (1-theta) D = x. Then
p = e^b - 1, q = e^{-a} - 1, and the bracket in E_m1 equals (1-theta)p(e^{-a}-1) + theta q (e^b - 1) = pq. The first
term of E_m1 tends to theta^2 xy = -theta^2 x^2. Hence
  E = theta x^2 [phi(x)phi(-x) - 1] - theta^2 x^2 + (pq/(p-q))^2,
  pq/(p-q) = -(e^a - 1)(e^b - 1)/(e^{a+b} - 1) = -(ab/(a+b)) R,   R := phi(a)phi(b)/phi(a+b),
and ab/(a+b) = theta x. So
  H(theta, x, -x) = E/(theta x^4) = [ phi(x)phi(-x) - 1 - theta (1 - R^2) ] / x^2,   R = phi(x)phi(kappa x)/phi((1+kappa)x).
d/dkappa log R = x [ (log phi)'(kappa x) - (log phi)'((1+kappa) x) ] <= 0 by convexity of log phi (both signs of x),
and R = 1 at kappa = 0; so 0 < R <= 1 and R decreases in kappa = theta/(1-theta). Thus theta (1 - R^2) is a product of
non-negative increasing functions of theta, and H(theta,x,-x) >= H(1/2,x,-x). At theta = 1/2, R = tanh(t)/t and
phi(x)phi(-x) - 1 = (sinh^2 t - t^2)/t^2, which gives the formula. Finally 2 sinh^2 t + tanh^2 t > 3t^2 for t != 0:
the function is even; for 0 < t <= sqrt 3, sinh^2 t >= t^2 + t^4/3 + 2t^6/45 (positive series of (cosh 2t - 1)/2) and
tanh t >= t - t^3/3 >= 0 (the difference has derivative t^2 - tanh^2 t >= 0), so the left side is
>= 3t^2 + t^6/5; for t >= sqrt 3, 2 sinh^2 t >= 2t^2 + 2t^4/3 >= 4t^2.  []

At (x, y) = (0, 0) one has H(theta, 0, 0) = (1+theta)(1-2theta)/(12(1-theta)) >= 0 (series; not needed below).

---------------------------------------------------------------------------------------------------

## 4. Reduction lemma

Write d/ds := (1/2)(d/dx + d/dy) (derivative in s at fixed theta and d).

**Lemma 4.1.** Let K = {theta in (0,1/2], |x| <= L, |y| <= L, s >= 0}. Suppose K is covered by finitely many closed
boxes (theta-ranges may stick out of (0, 1/2]; H is analytic there), each of type P (H > 0 on the box intersected
with K) or of type C (d/ds H > 0 there). Then H > 0 on K except at the points x = y = 0, where H >= 0.

*Proof.* Let P0 = (theta, x, y) in K with s > 0 and sigma(t) = (theta, x - t, y - t), 0 <= t <= s/2; sigma stays in K
(square convex, |d/2| <= L) and ends at (d/2, -d/2) on s = 0. Let V be the (closed) union of the P-boxes and {s = 0}.
Let t* be the least t with sigma(t) in V. For t < t*, sigma(t) lies in a C-box, so H(sigma(t)) is strictly
decreasing on [0, t*]; and H(sigma(t*)) >= 0 (P-box, or s = 0 and Theorem 3.1). Hence H(P0) > 0. Points with s = 0
are covered by Theorem 3.1.  []

---------------------------------------------------------------------------------------------------

## 5. Region B: interval boxes (rigorous ball arithmetic, `regionB.py`, `ecore.py`)

For a box Q = [th] x [x] x [y]:
* g >= g(x_lo - 10^-30, y_lo - 10^-30) on Q (Lemma 2.3(ii); the shift keeps the point off the axes); evaluated
  at that point in Arb, by the double power series g = sum_{j,k} x^j y^k/(j! k! (j+k+3)(j+2)(k+2)) (tail
  <= a^{K+1}/(12 (K+1)! (1 - a/(K+2))), a = |x|+|y|, K = 60) when |x|,|y| <= 1, else by the closed form.
* tm <= upper end of an Arb enclosure of tm over Q, computed with
  - formula (I): tm = -theta C_m1/(xy), C_m1 = phi(-theta s) - phi(x)phi(Y)J, J by Lemma 2.1(b), if Q avoids the axes;
  - formula (II): Lemma 2.4, if s > 0 on Q;
  monotone special functions (phi increasing, psi decreasing, ee increasing in each real node) are enclosed by their
  values at the endpoints of the argument balls; all other operations are Arb ball arithmetic.
* Q is of type P if g(x_lo, y_lo) - tm_upper > 0.
Point evaluations of phi, phi2, ee use: Taylor series with explicit geometric tail bounds when the arguments are
small (|z| <= 1, node spread <= 1, or argument balls too wide for the difference formula), otherwise the exact
difference formulas (expm1(z)/z, (exp[b,c] - exp[a,b])/(c-a) with the farthest pair as outer nodes).
All float upper bounds |z| used for branch choices and tail bounds are Arb upper bounds inflated by 1 + 2^-40.
Boxes are bisected adaptively (largest of 6*w_theta, w_x, w_y) down to minimum widths
(theta 2^-11, x and y 2^-9); a box is skipped if it lies in {s < 0}, or if all four (x, y)-corners satisfy
s <= s1 - 10^-9 and |d| <= d1 - 10^-9 for pieces of A' (Section 9) whose theta-intervals cover the box's
theta-interval. Initial boxes: theta-slabs of width 0.05 (exact endpoints) times unit squares of [-10, 10]^2.
Ball-arithmetic precision 192 bits.

## 6. Region A': Taylor models with Cauchy bounds (rigorous, `regionA2.py`, `regionA_run.py`)

A' is the union of the pieces listed in Section 9. It is covered by boxes
|theta - th0| <= rt (1 + 2^-20), |x - x0| <= 1/4, |y - y0| <= 1/4 (closed grid squares centred on (Z/2)^2 meeting
the piece; theta-centres th0 = th_a + (2i+1) rt; the factor 1 + 2^-20 makes neighbouring theta-boxes overlap).
For each box, with f(z) = H(th0 + z1, x0 + z2, y0 + z3) and radii rho' = (rho'_t, rho'_x, rho'_y):
1. *Analyticity.* Ball arithmetic over the closed polydisc |z_i| <= rho'_i checks max |Im x| < pi/2 - 0.05,
   max |Im Y| < pi/2 - 0.05 and |1 - theta| > 0.1. Then 1 + up and 1 + uq lie in Re > 0 for u in [0,1], J (integral
   form) is analytic, it equals the closed form of Lemma 2.1(b) (analytic continuation; |Im D| < pi so phi(D) != 0),
   and H = Phi/(xy) is analytic on the polydisc (Phi vanishes on the axes identically).
2. *Bound M' >= max |f| on the polydisc* = max on the torus T' (maximum principle). T' is covered by products of
   arc-balls (8 x 24 x 24 cells); on each cell
     |H| <= g(max Re x, max Re y) + |theta| ( phi(max Re(-theta s)) + phi(max Re x) phi(max Re Y) Jb ) / (|x|_min |y|_min),
     Jb = m_x^{-(1+theta_r)} m_Y^{-(2-theta_r)} exp(|theta_i| (|Im x| + |Im Y|)),  m_z = min(1, e^{min Re z} cos(max|Im z|)),
   using Lemma 2.3(iii), |phi(z)| <= phi(Re z), |1+up| >= Re(1+up) >= m_x, |arg(1+up)| <= |Im x|
   (|(1+up)^{-1-theta}| = |1+up|^{-1-theta_r} e^{theta_i arg(1+up)}; exponents taken at the worst end of theta_r;
   a factor is replaced by 1 when m >= 1); |x|_min is the distance from 0 to the rectangular ball.
   The tori avoid the axes: rho'_x is chosen with | |x0| - rho'_x | >= 1/4 and | |x0| - rho'_x/3 | >= 0.03 unless
   x0 = 0 (same for y); rho'_t = 3 rt (or 2.5 rt, 2 rt if the analyticity check needs it).
3. *Coefficients.* f is sampled at the 12 x 16 x 16 points of the torus T with radii rho = rho'/3 (point evaluations of
   formula (I), Arb); a DFT gives chat_alpha (alpha_1 <= 11, alpha_2 + alpha_3 <= 15), and
     |chat_alpha - c_alpha| <= M' prod_i rho_i'^{-alpha_i} [ prod_i (1 - 3^{-N_i})^{-1} - 1 ]    (aliasing),
   the true Taylor coefficients satisfying |c_alpha| <= M' rho'^{-alpha} (Cauchy).
4. *Certification.* With P = sum Re(chat_alpha) z^alpha, on the box (t_i = r_i/rho'_i):
     |H - P| <= sum_alpha e_alpha r^alpha + M' ( prod (1-t_i)^{-1} - sum_{alpha in S} t^alpha ),
     |H_x - P_x| <= sum alpha_2 e_alpha r^{alpha - e_2} + (M'/rho'_x) ( (1-t_1)^{-1}(1-t_2)^{-2}(1-t_3)^{-1} - sum_S alpha_2 t^{alpha-e_2} ),
   and similarly for H_y; d/ds = (H_x + H_y)/2. The box is split into 2 x 4 x 4 sub-boxes; each sub-box meeting
   {s >= 0} must satisfy P - err > 0 (type P) or d/ds P - err > 0 (type C) by Arb interval evaluation.
   A failing box would be split (theta halves, then quarter squares, depth <= 3).
Ball-arithmetic precision 128 bits.

## 7. Far region max(x, y) >= L = 10 (analytic, constants in `far_region.py`)

Here s >= 0, so max(|x|,|y|) >= L iff max(x, y) >= L. By Lemma 2.3(ii),(v): if x >= L then y >= -x and
g(x,y) >= g(x,-x) = G0(x) >= G0(L); if y >= L likewise g >= G0(y) >= G0(L). G0(10) = 2.1924... (Arb).
Upper bounds for tm (A = phi(x)phi(Y)J, B = phi(-theta s) in (0,1], tm = theta (A - B)/(xy)):
* xy < 0, |x|,|y| >= 1: tm = theta (B - A)/|xy| <= 1/2.
* x >= L, -1 < y < 0: Y in (-1,0), exp[x,Y] = e^Y phi(x - Y) >= e^{-1} phi(x), so A <= e phi(Y) <= e (Lemma 2.5(b)),
  and tm <= kappa A/s <= e/(L-1) (Lemma 2.5(d), s >= L-1).
* y >= L, -1 < x < 0: exp[x,Y] = e^x phi(Y - x) >= e^{-1} phi(Y), A <= e phi(x) <= e, tm <= e/(L-1).
* x, y > 0 near an axis (x >= L, 0 < y < 1, or y >= L, 0 < x < 1): A <= min(phi(x), phi(Y)) <= phi(1) (Lemma 2.5(c)),
  tm <= kappa A/s <= (e-1)/L.
* x, y >= 1 with x >= L: tm <= theta A/(xy) <= theta phi(Y)/(xy) <= theta phi(y)/(xy), while by Lemma 2.3(iv)
  g >= phi(x)phi(y)(mu(L) - mu(-1))/(x+y), mu(10) - mu(-1) = 0.4820... > 0.48; tm < g reduces to
  (1/x + 1/y)/2 < 0.48 phi(x), true as 0.55 < 0.48 phi(10). The case y >= L, x >= 1 is symmetric (A <= phi(x)).
In all cases tm <= max(1/2, e/9, (e-1)/10) < G0(10) <= g or tm < g directly, so H > 0.

## 8. Coverage

* theta: [0, 1/2] is the union of the theta-ranges of the runs (Section 9); theta = 0 is included harmlessly.
* (x, y): {s >= 0} = K_L  union  {max(x,y) >= L} (if max(x, y) < L and s >= 0 then min(x, y) > -L).
* K_L: region B starts from the grid of unit boxes of [-L, L]^2 and theta-slabs of width 0.05; every box is either
  certified, bisected (children cover it), skipped as contained in A' u {s < 0}, or recorded as failure (none).
  A' is covered by the closed grid squares meeting it (every point of the plane lies in a closed grid square, which
  then meets A'), times the theta-intervals of the pieces; `regionA_run.py` enumerates exactly these squares
  (l1-distance test in (s, d) coordinates, exact for the diamond image of a square).
* Lemma 4.1 then gives H >= 0 on K_L; Section 7 gives H > 0 on the far region; Lemma 2.2 gives E >= 0.

## 9. Region table

All runs: Python 3 with python-flint 0.9.0 (Arb), OMP_NUM_THREADS=1. "rigorous" = Arb ball arithmetic with the
error bounds of Sections 5-6.

| # | theta | (x, y) region (s = x+y, d = x-y) | method | result |
|---|-------|----------------------------------|--------|--------|
| S | (0, 1/2] | s = 0 | Theorem 3.1 (analytic) | H > 0 for x != 0 |
| A1 | [0, 0.30] | 0 <= s <= 0.3, \|d\| <= 0.6 (7 grid squares) | Taylor models, rt = 0.025 | 42 boxes, all sub-boxes H > 0 |
| A2 | [0.30, 0.35] | 0 <= s <= 0.6, \|d\| <= 1 (12 squares) | Taylor models, rt = 0.0125 | 24 boxes, all H > 0 |
| A3 | [0.35, 0.45] | 0 <= s <= 0.6, \|d\| <= 3 (28 squares) | Taylor models, rt = 0.0125 | 112 boxes, all H > 0 |
| A4 | [0.45, 0.50] | 0 <= s <= 0.6, \|d\| <= 3 (28 squares) | Taylor models, rt = 0.005 | 140 boxes (8 split in theta: 148 leaves); 3433 sub-boxes H > 0, 151 sub-boxes dH/ds > 0 |
| B | [0, 0.5] | [-10, 10]^2, s >= 0, minus A1-A4 | interval boxes + bisection | 167626 boxes H > 0, 0 failures |
| F | (0, 1/2] | max(x, y) >= 10, s >= 0 | analytic (Section 7) | H > 0 |
| axes | (0, 1/2] | x = 0 or y = 0 | Lemma 2.2 | E = 0 |

Final numbers (filled from the final runs, which use the corrected `ecore.py`; see LOG.md for the run logs):
* Region A' (`runs/A_final_{0,1}.log/.json`): 318 planned boxes, 326 certified leaves, 0 failures; sub-boxes: 7617 of
  type P (H > 0), 151 of type C (dH/ds > 0), the latter only for theta-centres 0.465..0.495 and |x0|, |y0| <= 1.
  Largest error bounds: 2.2e-2 for dH/ds, 9.1e-3 for H; largest torus bound M' = 1002; 788 s CPU in total.
* Region B (`runs/B_final_{lo,hi}.log/.json`): theta in [0, 0.3]: 47229 boxes verified, 4871 skipped (in A' or s < 0),
  0 failed, 93 s; theta in [0.3, 0.5]: 120397 verified, 5187 skipped, 0 failed, 109 s.
* `check_coverage.py`: "REGION A' COVERAGE: OK", "REGION B: OK" (exclusion list of both B runs equals the pieces of A').
* `far_region.py`: all assertions pass (G0(10) = 2.1924..., mu(10) - mu(-1) = 0.4820...).
* `test_ecore.py`: the ball-arithmetic H agrees with the closed form of Section 0 (mpmath, 60 digits) to 1.4e-50 at 200
  random points; 0 containment failures of box enclosures at sampled points (numerical sanity checks).

## 10. Commands (from this directory)

    python verify_closed_form.py          # closed form vs integral definition (numerical, mpmath)
    python test_ecore.py                  # ball-arithmetic formulas vs mpmath closed form; enclosure tests
    python far_region.py                  # constants of Section 7 (Arb, asserts)
    sh run_final_A.sh                     # region A' (two jobs) -> runs/A_final_{0,1}.json/.log
    sh run_final_B.sh                     # region B (two jobs)  -> runs/B_final_{lo,hi}.json/.log
    python check_coverage.py runs/A_final_0.json runs/A_final_1.json runs/B_final_lo.json runs/B_final_hi.json

Files: `ecore.py` (formulas, special functions, enclosures), `regionB.py`, `regionA2.py`, `regionA_run.py`,
`far_region.py`, `check_coverage.py`, `run_final_A.sh`, `run_final_B.sh`. Exploration scripts (numerical only) and a superseded first Taylor-model attempt are not included.
`runs/prelim/` holds the runs made before the last rigour fixes (same verdicts); `runs/B_pass1_*` and
`runs/B_probe*` are earlier region-B probes with other exclusion sets.

## 11. What the proof uses

* Used: the closed form of E (Section 0); Lemma 2.1 re-derives the p, q-term from the integral J.
* Not used: the corner series and two numerical observations from our working notes (E_m1 < 0 and a bound on
  -E_m1/E_GT); E_m1 < 0 was never needed. Both are consistent
  with the computations (e.g. only theta in [0.45, 0.5] needed the derivative test near the corner).
