import Mathlib

/-!
# Theorem 1 of the lower-half note, part 2: the kernel and its sign conditions

Authors: Ansh Mishra, Aryan Senthilkumar. License: MIT.

Notation of `math/04-lower-half-new-cases.md` (Sections 2.3-2.5) and `math/05-lower-half-m3.md`
(Sections 3-4, the case n = 3). The kernel of Lemma 3 at the apex `1` is, for `1 < X ≤ Y`,
$$E(X, Y) = \kappa(1, X, Y) - (Y - 1)(Y - X)\sqrt{(Y + 4)(Y + 4X)},$$
with $\kappa(x,y,z) = (x+y+z)(x^2+y^2+z^2) - 9xyz$ (`kerE`). We use the weight
$w(X) = (X-1)^{3/2}$ of `04-lower-half-new-cases.md`, Section 2.4, and
$F(X, Y) = E(X,Y) / (w(X) w(Y))$. The four conditions of Lemma 4 ($F \ge 0$, $F_X \ge 0$,
$F_Y \le 0$, $F_{XY} \le 0$) are, after multiplying by positive factors,
- `kerE_nonneg`: $E \ge 0$,
- `cond1`: $2(X-1) E_X - 3E \ge 0$,
- `cond2`: $3E - 2(Y-1) E_Y \ge 0$,
- `cond3`: $4(X-1)(Y-1) E_{XY} - 6(X-1) E_X - 6(Y-1) E_Y + 9E \le 0$,

where `kerEX`, `kerEY`, `kerEXY` are the closed forms of the partial derivatives (they are shown
to be the derivatives in `OQP40/Thm33Kernel.lean`). Each condition times a power of
$r = \sqrt{(Y+4)(Y+4X)}$ has the form $\alpha + \beta r$ with polynomials $\alpha, \beta$
(`math/05-lower-half-m3.md`, Lemma 8), and is proved by squaring (Lemma 9 there, `p1_nonneg`,
`p2_nonneg`): the polynomials needed have only nonnegative coefficients after the substitution
$X = 1 + u$, $Y = 1 + u + v$, which `ring_nf` and `positivity` check for $u, v \ge 0$.

The polynomials were computed for the weight $w = (X-1)^{3/2}$; for the weight
$\sqrt{E(X,X)}$ of `05-lower-half-m3.md` the same method works with larger polynomials.
-/

namespace OpenQuantumProblem40.Thm33

noncomputable section

/-- $\kappa(x,y,z) = (x+y+z)(x^2+y^2+z^2) - 9xyz$. -/
def kappa (x y z : ℝ) : ℝ := (x + y + z) * (x ^ 2 + y ^ 2 + z ^ 2) - 9 * x * y * z

/-- The radicand $(Y+4)(Y+4X)$. -/
def rad (X Y : ℝ) : ℝ := (Y + 4) * (Y + 4 * X)

/-- $r = \sqrt{(Y+4)(Y+4X)}$. -/
def rt (X Y : ℝ) : ℝ := Real.sqrt (rad X Y)

/-- $(Y-1)(Y-X)$. -/
def ell (X Y : ℝ) : ℝ := (Y - 1) * (Y - X)

/-- **The kernel** $E(X,Y) = \kappa(1,X,Y) - (Y-1)(Y-X)\sqrt{(Y+4)(Y+4X)}$ (for $X \le Y$). -/
def kerE (X Y : ℝ) : ℝ := kappa 1 X Y - ell X Y * rt X Y

/-- The closed form of $\partial_X E$. -/
def kerEX (X Y : ℝ) : ℝ :=
  (3 * X ^ 2 + 2 * X * Y + 2 * X + Y ^ 2 - 9 * Y + 1) + (Y - 1) * rt X Y
    - 2 * ell X Y * (Y + 4) / rt X Y

/-- The closed form of $\partial_Y E$. -/
def kerEY (X Y : ℝ) : ℝ :=
  (X ^ 2 + 2 * X * Y - 9 * X + 3 * Y ^ 2 + 2 * Y + 1) - (2 * Y - X - 1) * rt X Y
    - ell X Y * (Y + 2 * X + 2) / rt X Y

/-- The closed form of $\partial_X \partial_Y E$. -/
def kerEXY (X Y : ℝ) : ℝ :=
  (2 * X + 2 * Y - 9) + rt X Y - 2 * (2 * Y - X - 1) * (Y + 4) / rt X Y
    + (Y - 1) * (Y + 2 * X + 2) / rt X Y - 2 * ell X Y / rt X Y
    + 2 * ell X Y * (Y + 2 * X + 2) * (Y + 4) / rt X Y ^ 3

theorem rad_pos {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y) : 0 < rad X Y := by
  unfold rad; positivity

theorem rt_pos {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y) : 0 < rt X Y :=
  Real.sqrt_pos.2 (rad_pos hX hY)

theorem rt_sq {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y) : rt X Y ^ 2 = rad X Y :=
  Real.sq_sqrt (rad_pos hX hY).le

/-! ### Squaring (Lemma 9 of `05-lower-half-m3.md`) -/

/-- If `α ≥ 0`, `α² ≥ β² ρ` and `r² = ρ`, then `α + β r ≥ 0`. -/
theorem p1_nonneg {α β r ρ : ℝ} (hr2 : r ^ 2 = ρ) (hα : 0 ≤ α)
    (hΔ : 0 ≤ α ^ 2 - β ^ 2 * ρ) : 0 ≤ α + β * r := by
  have h1 : (β * r) ^ 2 ≤ α ^ 2 := by rw [mul_pow, hr2]; linarith
  have h2 : |β * r| ≤ |α| := sq_le_sq.1 h1
  rw [abs_of_nonneg hα] at h2
  have h3 := neg_abs_le (β * r)
  linarith

/-- If `β ≥ 0`, `β² ρ ≥ α²`, `r ≥ 0` and `r² = ρ`, then `α + β r ≥ 0`. -/
theorem p2_nonneg {α β r ρ : ℝ} (hr : 0 ≤ r) (hr2 : r ^ 2 = ρ) (hβ : 0 ≤ β)
    (hΔ : 0 ≤ β ^ 2 * ρ - α ^ 2) : 0 ≤ α + β * r := by
  have h1 : α ^ 2 ≤ (β * r) ^ 2 := by rw [mul_pow, hr2]; linarith
  have h2 : |α| ≤ |β * r| := sq_le_sq.1 h1
  rw [abs_of_nonneg (mul_nonneg hβ hr)] at h2
  have h3 := neg_abs_le α
  linarith

/-! ### The polynomials with nonnegative coefficients after `X = 1 + u`, `Y = 1 + u + v` -/

section Polynomials

variable {X Y : ℝ}

theorem sp0a (hX : 1 ≤ X) (hXY : X ≤ Y) : 0 ≤ kappa 1 X Y := by
  obtain ⟨u, hu, rfl⟩ : ∃ u, 0 ≤ u ∧ X = 1 + u := ⟨X - 1, by linarith, by ring⟩
  obtain ⟨v, hv, rfl⟩ : ∃ v, 0 ≤ v ∧ Y = 1 + u + v := ⟨Y - 1 - u, by linarith, by ring⟩
  unfold kappa; ring_nf; positivity

theorem sp0d (hX : 1 ≤ X) (hXY : X ≤ Y) :
    0 ≤ kappa 1 X Y ^ 2 - (-ell X Y) ^ 2 * rad X Y := by
  obtain ⟨u, hu, rfl⟩ : ∃ u, 0 ≤ u ∧ X = 1 + u := ⟨X - 1, by linarith, by ring⟩
  obtain ⟨v, hv, rfl⟩ : ∃ v, 0 ≤ v ∧ Y = 1 + u + v := ⟨Y - 1 - u, by linarith, by ring⟩
  unfold kappa ell rad; ring_nf; positivity

/-- $\alpha$ of condition 1. -/
def al1 (X Y : ℝ) : ℝ := (Y - 1) * (Y + 4) * (7 * X * Y - 12 * X + 3 * Y ^ 2 + 2 * Y)

/-- $\beta$ of condition 1. -/
def be1 (X Y : ℝ) : ℝ :=
  3 * X ^ 3 + X ^ 2 * Y - 5 * X ^ 2 - X * Y ^ 2 + 5 * X * Y - 5 * X - 3 * Y ^ 3 - 5 * Y ^ 2
    + 15 * Y - 5

/-- $\alpha$ of condition 2. -/
def al2 (X Y : ℝ) : ℝ :=
  (Y - 1) * (20 * X ^ 2 + 7 * X * Y ^ 2 + 6 * X * Y - 28 * X + 3 * Y ^ 3 + 4 * Y ^ 2 - 12 * Y)

/-- $\beta$ of condition 2. -/
def be2 (X Y : ℝ) : ℝ :=
  3 * X ^ 3 + X ^ 2 * Y + 5 * X ^ 2 - X * Y ^ 2 - 5 * X * Y - 15 * X - 3 * Y ^ 3 + 5 * Y ^ 2
    + 5 * Y + 5

/-- $\alpha$ of condition 3 (divided by $Y + 4$). -/
def al3 (X Y : ℝ) : ℝ :=
  -(Y - 1) * (56 * X ^ 2 * Y ^ 2 + 28 * X ^ 2 * Y + 16 * X ^ 2 + 55 * X * Y ^ 3 + 98 * X * Y ^ 2
    - 116 * X * Y - 112 * X + 9 * Y ^ 4 + 14 * Y ^ 3 - 40 * Y ^ 2 - 8 * Y)

/-- $\beta$ of condition 3 (divided by $Y + 4$). -/
def be3 (X Y : ℝ) : ℝ :=
  (4 * X + Y) * (9 * X ^ 3 + X ^ 2 * Y - 13 * X ^ 2 + X * Y ^ 2 + X * Y - 5 * X + 9 * Y ^ 3
    - 13 * Y ^ 2 - 5 * Y + 15)

theorem sp1a (hX : 1 ≤ X) (hXY : X ≤ Y) : 0 ≤ al1 X Y := by
  obtain ⟨u, hu, rfl⟩ : ∃ u, 0 ≤ u ∧ X = 1 + u := ⟨X - 1, by linarith, by ring⟩
  obtain ⟨v, hv, rfl⟩ : ∃ v, 0 ≤ v ∧ Y = 1 + u + v := ⟨Y - 1 - u, by linarith, by ring⟩
  unfold al1; ring_nf; positivity

theorem sp1d (hX : 1 ≤ X) (hXY : X ≤ Y) : 0 ≤ al1 X Y ^ 2 - be1 X Y ^ 2 * rad X Y := by
  obtain ⟨u, hu, rfl⟩ : ∃ u, 0 ≤ u ∧ X = 1 + u := ⟨X - 1, by linarith, by ring⟩
  obtain ⟨v, hv, rfl⟩ : ∃ v, 0 ≤ v ∧ Y = 1 + u + v := ⟨Y - 1 - u, by linarith, by ring⟩
  unfold al1 be1 rad; ring_nf; positivity

theorem sp2a (hX : 1 ≤ X) (hXY : X ≤ Y) : 0 ≤ al2 X Y := by
  obtain ⟨u, hu, rfl⟩ : ∃ u, 0 ≤ u ∧ X = 1 + u := ⟨X - 1, by linarith, by ring⟩
  obtain ⟨v, hv, rfl⟩ : ∃ v, 0 ≤ v ∧ Y = 1 + u + v := ⟨Y - 1 - u, by linarith, by ring⟩
  unfold al2; ring_nf; positivity

theorem sp2d (hX : 1 ≤ X) (hXY : X ≤ Y) : 0 ≤ al2 X Y ^ 2 - be2 X Y ^ 2 * rad X Y := by
  obtain ⟨u, hu, rfl⟩ : ∃ u, 0 ≤ u ∧ X = 1 + u := ⟨X - 1, by linarith, by ring⟩
  obtain ⟨v, hv, rfl⟩ : ∃ v, 0 ≤ v ∧ Y = 1 + u + v := ⟨Y - 1 - u, by linarith, by ring⟩
  unfold al2 be2 rad; ring_nf; positivity

theorem sp3b (hX : 1 ≤ X) (hXY : X ≤ Y) : 0 ≤ be3 X Y := by
  obtain ⟨u, hu, rfl⟩ : ∃ u, 0 ≤ u ∧ X = 1 + u := ⟨X - 1, by linarith, by ring⟩
  obtain ⟨v, hv, rfl⟩ : ∃ v, 0 ≤ v ∧ Y = 1 + u + v := ⟨Y - 1 - u, by linarith, by ring⟩
  unfold be3; ring_nf; positivity

theorem sp3d (hX : 1 ≤ X) (hXY : X ≤ Y) : 0 ≤ be3 X Y ^ 2 * rad X Y - al3 X Y ^ 2 := by
  obtain ⟨u, hu, rfl⟩ : ∃ u, 0 ≤ u ∧ X = 1 + u := ⟨X - 1, by linarith, by ring⟩
  obtain ⟨v, hv, rfl⟩ : ∃ v, 0 ≤ v ∧ Y = 1 + u + v := ⟨Y - 1 - u, by linarith, by ring⟩
  unfold al3 be3 rad; ring_nf; positivity

end Polynomials

/-! ### The derivative closed forms times powers of `r` -/

section Identities

variable {X Y : ℝ}

theorem rt_mul_kerE (X Y : ℝ) :
    rt X Y * kerE X Y = kappa 1 X Y * rt X Y - ell X Y * rt X Y ^ 2 := by
  unfold kerE; ring

theorem rt_mul_kerEX (h : rt X Y ≠ 0) :
    rt X Y * kerEX X Y = (3 * X ^ 2 + 2 * X * Y + 2 * X + Y ^ 2 - 9 * Y + 1) * rt X Y
      + (Y - 1) * rt X Y ^ 2 - 2 * ell X Y * (Y + 4) := by
  unfold kerEX; field_simp

theorem rt_mul_kerEY (h : rt X Y ≠ 0) :
    rt X Y * kerEY X Y = (X ^ 2 + 2 * X * Y - 9 * X + 3 * Y ^ 2 + 2 * Y + 1) * rt X Y
      - (2 * Y - X - 1) * rt X Y ^ 2 - ell X Y * (Y + 2 * X + 2) := by
  unfold kerEY; field_simp

theorem rt_cube_mul_kerEXY (h : rt X Y ≠ 0) :
    rt X Y ^ 3 * kerEXY X Y = (2 * X + 2 * Y - 9) * rt X Y ^ 3 + rt X Y ^ 4
      - 2 * (2 * Y - X - 1) * (Y + 4) * rt X Y ^ 2 + (Y - 1) * (Y + 2 * X + 2) * rt X Y ^ 2
      - 2 * ell X Y * rt X Y ^ 2 + 2 * ell X Y * (Y + 2 * X + 2) * (Y + 4) := by
  unfold kerEXY; field_simp

end Identities

/-! ### The four conditions -/

section Conditions

variable {X Y : ℝ}

/-- **Condition (0)**: $E(X,Y) \ge 0$ for $1 \le X \le Y$. -/
theorem kerE_nonneg (hX : 1 ≤ X) (hXY : X ≤ Y) : 0 ≤ kerE X Y := by
  have hr2 := rt_sq (X := X) (Y := Y) (by linarith) (by linarith)
  have h := p1_nonneg hr2 (sp0a hX hXY) (sp0d hX hXY)
  unfold kerE
  linarith

/-- **Condition (1)**, the sign of $F_X$: $2(X-1)E_X - 3E \ge 0$ for $1 < X < Y$. -/
theorem cond1 (hX : 1 < X) (hXY : X < Y) : 0 ≤ 2 * (X - 1) * kerEX X Y - 3 * kerE X Y := by
  have hr : 0 < rt X Y := rt_pos (by linarith) (by linarith)
  have hr2 := rt_sq (X := X) (Y := Y) (by linarith) (by linarith)
  have key : rt X Y * (2 * (X - 1) * kerEX X Y - 3 * kerE X Y) = al1 X Y + be1 X Y * rt X Y := by
    have e : rt X Y * (2 * (X - 1) * kerEX X Y - 3 * kerE X Y)
        = 2 * (X - 1) * (rt X Y * kerEX X Y) - 3 * (rt X Y * kerE X Y) := by ring
    rw [e, rt_mul_kerEX hr.ne', rt_mul_kerE]
    unfold rad at hr2
    unfold al1 be1 ell kappa
    linear_combination (-X * Y + X + 3 * Y ^ 2 - 5 * Y + 2) * hr2
  have h := p1_nonneg hr2 (sp1a hX.le hXY.le) (sp1d hX.le hXY.le)
  rw [← key] at h
  exact (mul_nonneg_iff_of_pos_left hr).1 h

/-- **Condition (2)**, the sign of $F_Y$: $3E - 2(Y-1)E_Y \ge 0$ for $1 < X < Y$. -/
theorem cond2 (hX : 1 < X) (hXY : X < Y) : 0 ≤ 3 * kerE X Y - 2 * (Y - 1) * kerEY X Y := by
  have hr : 0 < rt X Y := rt_pos (by linarith) (by linarith)
  have hr2 := rt_sq (X := X) (Y := Y) (by linarith) (by linarith)
  have key : rt X Y * (3 * kerE X Y - 2 * (Y - 1) * kerEY X Y) = al2 X Y + be2 X Y * rt X Y := by
    have e : rt X Y * (3 * kerE X Y - 2 * (Y - 1) * kerEY X Y)
        = 3 * (rt X Y * kerE X Y) - 2 * (Y - 1) * (rt X Y * kerEY X Y) := by ring
    rw [e, rt_mul_kerEY hr.ne', rt_mul_kerE]
    unfold rad at hr2
    unfold al2 be2 ell kappa
    linear_combination (X * Y - X + Y ^ 2 - 3 * Y + 2) * hr2
  have h := p1_nonneg hr2 (sp2a hX.le hXY.le) (sp2d hX.le hXY.le)
  rw [← key] at h
  exact (mul_nonneg_iff_of_pos_left hr).1 h

/-- **Condition (3)**, the sign of $F_{XY}$:
$4(X-1)(Y-1)E_{XY} - 6(X-1)E_X - 6(Y-1)E_Y + 9E \le 0$ for $1 < X < Y$. -/
theorem cond3 (hX : 1 < X) (hXY : X < Y) :
    4 * (X - 1) * (Y - 1) * kerEXY X Y - 6 * (X - 1) * kerEX X Y - 6 * (Y - 1) * kerEY X Y
      + 9 * kerE X Y ≤ 0 := by
  have hr : 0 < rt X Y := rt_pos (by linarith) (by linarith)
  have hr2 := rt_sq (X := X) (Y := Y) (by linarith) (by linarith)
  set Z := 4 * (X - 1) * (Y - 1) * kerEXY X Y - 6 * (X - 1) * kerEX X Y
    - 6 * (Y - 1) * kerEY X Y + 9 * kerE X Y with hZ
  have key : rt X Y ^ 3 * (-Z) = (Y + 4) * (al3 X Y + be3 X Y * rt X Y) := by
    have e : rt X Y ^ 3 * (-Z) = -(4 * (X - 1) * (Y - 1) * (rt X Y ^ 3 * kerEXY X Y)
        - 6 * (X - 1) * rt X Y ^ 2 * (rt X Y * kerEX X Y)
        - 6 * (Y - 1) * rt X Y ^ 2 * (rt X Y * kerEY X Y)
        + 9 * rt X Y ^ 2 * (rt X Y * kerE X Y)) := by rw [hZ]; ring
    rw [e, rt_cube_mul_kerEXY hr.ne', rt_mul_kerEX hr.ne', rt_mul_kerEY hr.ne', rt_mul_kerE]
    unfold rad at hr2
    unfold al3 be3 ell kappa
    linear_combination (-rt X Y ^ 2 * X * Y + rt X Y ^ 2 * X - 3 * rt X Y ^ 2 * Y ^ 2
      + 7 * rt X Y ^ 2 * Y - 4 * rt X Y ^ 2 + 9 * rt X Y * X ^ 3 + rt X Y * X ^ 2 * Y
      - 13 * rt X Y * X ^ 2 + rt X Y * X * Y ^ 2 + rt X Y * X * Y - 5 * rt X Y * X
      + 9 * rt X Y * Y ^ 3 - 13 * rt X Y * Y ^ 2 - 5 * rt X Y * Y + 15 * rt X Y
      - 4 * X ^ 2 * Y ^ 2 + 8 * X ^ 2 * Y - 4 * X ^ 2 - 11 * X * Y ^ 3 + X * Y ^ 2 + 6 * X * Y
      + 4 * X - 9 * Y ^ 4 - 13 * Y ^ 3 + 54 * Y ^ 2 - 8 * Y - 24) * hr2
  have h := p2_nonneg hr.le hr2 (sp3b hX.le hXY.le) (sp3d hX.le hXY.le)
  have h' : 0 ≤ (Y + 4) * (al3 X Y + be3 X Y * rt X Y) := mul_nonneg (by linarith) h
  rw [← key] at h'
  have := (mul_nonneg_iff_of_pos_left (pow_pos hr 3)).1 h'
  linarith

end Conditions

end

end OpenQuantumProblem40.Thm33
