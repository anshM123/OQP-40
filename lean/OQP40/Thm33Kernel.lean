import OQP40.Thm33Interval
import OQP40.Thm33Signs

/-!
# Theorem 1 of the lower-half note, part 3: the kernel `E` is positive semidefinite (Lemma 3)

Authors: Ansh Mishra, Aryan Senthilkumar. License: MIT.

We show that the kernel $E(X, Y)$ of `OQP40/Thm33Signs.lean` (Lemma 3 of
`math/04-lower-half-new-cases.md` at the apex `1`) is positive semidefinite on $(1, \infty)$:
for points $q_a > 1$ and a positive semidefinite form $R$,
$\sum_{a,b} R_{ab} E(\min(q_a,q_b), \max(q_a,q_b)) \ge 0$ (`kerE_psd`).

Write $E(X,Y) = w(X) w(Y) F(X,Y)$ with $w(X) = (X-1)^{3/2}$, i.e.
$F(X,Y) = E(X,Y)\,\omega(X)\,\omega(Y)$ with $\omega(X) = (X-1)^{-3/2}$ (`kerF`, `om`). The
derivatives of $F$ are computed in closed form (`hasDerivAt_kerF_X`, `hasDerivAt_kerF_Y`,
`hasDerivAt_kerFY_X`); their signs come from the four conditions of `OQP40/Thm33Signs.lean`. The
mean value theorem then gives the hypotheses of Lemma 4 (`intervalHyp_kerF`): $F \ge 0$, $F$
nondecreasing in $X$ and nonincreasing in $Y$, and the rectangle inequality (from
$F_{XY} \le 0$, by applying the mean value theorem twice). Lemma 4
(`OQP40/Thm33Interval.lean`) finishes.
-/

namespace OpenQuantumProblem40.Thm33

noncomputable section

open Set

/-- $\omega(X) = (X-1)^{-3/2}$, the inverse of the weight $w(X) = (X-1)^{3/2}$. -/
def om (X : ℝ) : ℝ := (X - 1) ^ (-(3 / 2 : ℝ))

/-- $\lambda(X) = w'(X)/w(X) = 3/(2(X-1))$. -/
def lam (X : ℝ) : ℝ := 3 / (2 * (X - 1))

/-- $F(X,Y) = E(X,Y)\,\omega(X)\,\omega(Y)$. -/
def kerF (X Y : ℝ) : ℝ := kerE X Y * om X * om Y

/-- The closed form of $\partial_Y F$. -/
def kerFY (X Y : ℝ) : ℝ := (kerEY X Y - lam Y * kerE X Y) * om X * om Y

theorem om_pos {X : ℝ} (hX : 1 < X) : 0 < om X :=
  Real.rpow_pos_of_pos (by linarith) _

/-! ### Derivatives -/

section Derivatives

variable {X Y : ℝ}

theorem hasDerivAt_om (hX : 1 < X) : HasDerivAt om (-(lam X) * om X) X := by
  have h1 : HasDerivAt (fun X : ℝ => X - 1) 1 X := (hasDerivAt_id' X).sub_const 1
  have h2 := h1.rpow_const (p := -(3 / 2 : ℝ)) (Or.inl (by linarith))
  refine h2.congr_deriv ?_
  unfold lam om
  rw [Real.rpow_sub_one (by linarith : X - 1 ≠ 0)]
  have : X - 1 ≠ 0 := by linarith
  field_simp

theorem hasDerivAt_kappa_X (Y : ℝ) :
    HasDerivAt (fun X => kappa 1 X Y) (3 * X ^ 2 + 2 * X * Y + 2 * X + Y ^ 2 - 9 * Y + 1) X := by
  have hx : HasDerivAt (fun X : ℝ => X) 1 X := hasDerivAt_id' X
  have h := (((hx.const_add 1).add_const Y).mul
    (((hasDerivAt_pow 2 X).const_add (1 ^ 2)).add_const (Y ^ 2))).sub
    ((hx.const_mul (9 * 1)).mul_const Y)
  refine h.congr_deriv ?_
  norm_num
  ring

theorem hasDerivAt_kappa_Y (X : ℝ) :
    HasDerivAt (fun Y => kappa 1 X Y) (X ^ 2 + 2 * X * Y - 9 * X + 3 * Y ^ 2 + 2 * Y + 1) Y := by
  have hy : HasDerivAt (fun Y : ℝ => Y) 1 Y := hasDerivAt_id' Y
  have h := ((hy.const_add (1 + X)).mul ((hasDerivAt_pow 2 Y).const_add (1 ^ 2 + X ^ 2))).sub
    (hy.const_mul (9 * 1 * X))
  have e : (fun Y => kappa 1 X Y)
      = fun Y => (1 + X + Y) * (1 ^ 2 + X ^ 2 + Y ^ 2) - 9 * 1 * X * Y := by
    funext Y; unfold kappa; ring
  rw [e]
  refine h.congr_deriv ?_
  norm_num
  ring

theorem hasDerivAt_rt_X (hX : 0 < X) (hY : 0 < Y) :
    HasDerivAt (fun X => rt X Y) (2 * (Y + 4) / rt X Y) X := by
  have hx : HasDerivAt (fun X : ℝ => X) 1 X := hasDerivAt_id' X
  have hrad : HasDerivAt (fun X => rad X Y) ((Y + 4) * (4 * 1)) X :=
    ((hx.const_mul 4).const_add Y).const_mul (Y + 4)
  have h := hrad.sqrt (rad_pos hX hY).ne'
  have hr : Real.sqrt (rad X Y) ≠ 0 := (rt_pos hX hY).ne'
  refine h.congr_deriv ?_
  rw [show rt X Y = Real.sqrt (rad X Y) from rfl]
  field_simp
  ring

theorem hasDerivAt_rt_Y (hX : 0 < X) (hY : 0 < Y) :
    HasDerivAt (fun Y => rt X Y) ((Y + 2 * X + 2) / rt X Y) Y := by
  have hy : HasDerivAt (fun Y : ℝ => Y) 1 Y := hasDerivAt_id' Y
  have hrad : HasDerivAt (fun Y => rad X Y) (1 * (Y + 4 * X) + (Y + 4) * 1) Y :=
    (hy.add_const 4).mul (hy.add_const (4 * X))
  have h := hrad.sqrt (rad_pos hX hY).ne'
  have hr : Real.sqrt (rad X Y) ≠ 0 := (rt_pos hX hY).ne'
  refine h.congr_deriv ?_
  rw [show rt X Y = Real.sqrt (rad X Y) from rfl]
  field_simp
  ring

theorem hasDerivAt_kerE_X (hX : 0 < X) (hY : 0 < Y) :
    HasDerivAt (fun X => kerE X Y) (kerEX X Y) X := by
  have hx : HasDerivAt (fun X : ℝ => X) 1 X := hasDerivAt_id' X
  have hell : HasDerivAt (fun X => ell X Y) ((Y - 1) * (-1)) X := (hx.const_sub Y).const_mul (Y - 1)
  have h := (hasDerivAt_kappa_X (X := X) Y).sub (hell.mul (hasDerivAt_rt_X hX hY))
  have hr : rt X Y ≠ 0 := (rt_pos hX hY).ne'
  refine h.congr_deriv ?_
  unfold kerEX
  field_simp
  ring

theorem hasDerivAt_kerE_Y (hX : 0 < X) (hY : 0 < Y) :
    HasDerivAt (fun Y => kerE X Y) (kerEY X Y) Y := by
  have hy : HasDerivAt (fun Y : ℝ => Y) 1 Y := hasDerivAt_id' Y
  have hell : HasDerivAt (fun Y => ell X Y) (1 * (Y - X) + (Y - 1) * 1) Y :=
    (hy.sub_const 1).mul (hy.sub_const X)
  have h := (hasDerivAt_kappa_Y (Y := Y) X).sub (hell.mul (hasDerivAt_rt_Y hX hY))
  have hr : rt X Y ≠ 0 := (rt_pos hX hY).ne'
  refine h.congr_deriv ?_
  unfold kerEY ell
  field_simp
  ring

theorem hasDerivAt_kerEY_X (hX : 0 < X) (hY : 0 < Y) :
    HasDerivAt (fun X => kerEY X Y) (kerEXY X Y) X := by
  have hx : HasDerivAt (fun X : ℝ => X) 1 X := hasDerivAt_id' X
  have hr : rt X Y ≠ 0 := (rt_pos hX hY).ne'
  have hrt := hasDerivAt_rt_X hX hY
  have hp : HasDerivAt (fun X : ℝ => X ^ 2 + 2 * X * Y - 9 * X + 3 * Y ^ 2 + 2 * Y + 1)
      (2 * X + 2 * Y - 9) X := by
    have := ((((hasDerivAt_pow 2 X).add ((hx.const_mul 2).mul_const Y)).sub
      (hx.const_mul 9)).add_const (3 * Y ^ 2)).add_const (2 * Y) |>.add_const 1
    refine this.congr_deriv ?_
    norm_num
  have hl : HasDerivAt (fun X : ℝ => 2 * Y - X - 1) (-1) X := (hx.const_sub (2 * Y)).sub_const 1
  have hell : HasDerivAt (fun X => ell X Y) ((Y - 1) * (-1)) X :=
    (hx.const_sub Y).const_mul (Y - 1)
  have hq : HasDerivAt (fun X : ℝ => Y + 2 * X + 2) (2 * 1) X :=
    ((hx.const_mul 2).const_add Y).add_const 2
  have h := (hp.sub (hl.mul hrt)).sub ((hell.mul hq).div hrt hr)
  refine h.congr_deriv ?_
  simp only [Pi.mul_apply]
  unfold kerEXY ell
  field_simp
  ring

theorem hasDerivAt_kerF_X (hX : 1 < X) (hY : 1 < Y) :
    HasDerivAt (fun X => kerF X Y) ((kerEX X Y - lam X * kerE X Y) * om X * om Y) X := by
  have h := ((hasDerivAt_kerE_X (by linarith : (0 : ℝ) < X) (by linarith : (0 : ℝ) < Y)).mul
    (hasDerivAt_om hX)).mul_const (om Y)
  refine h.congr_deriv ?_
  ring

theorem hasDerivAt_kerF_Y (hX : 1 < X) (hY : 1 < Y) :
    HasDerivAt (fun Y => kerF X Y) (kerFY X Y) Y := by
  have h := ((hasDerivAt_kerE_Y (by linarith : (0 : ℝ) < X) (by linarith : (0 : ℝ) < Y)).mul_const
    (om X)).mul (hasDerivAt_om hY)
  refine h.congr_deriv ?_
  unfold kerFY; ring

theorem hasDerivAt_kerFY_X (hX : 1 < X) (hY : 1 < Y) :
    HasDerivAt (fun X => kerFY X Y)
      ((kerEXY X Y - lam Y * kerEX X Y - lam X * (kerEY X Y - lam Y * kerE X Y)) * om X * om Y)
      X := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hY0 : (0 : ℝ) < Y := by linarith
  have h := ((((hasDerivAt_kerEY_X hX0 hY0).sub ((hasDerivAt_kerE_X hX0 hY0).const_mul (lam Y))).mul
    (hasDerivAt_om hX)).mul_const (om Y))
  refine h.congr_deriv ?_
  simp only [Pi.sub_apply]
  ring

end Derivatives

/-! ### Signs of the derivatives -/

section Signs

variable {X Y : ℝ}

theorem kerF_X_nonneg (hX : 1 < X) (hXY : X < Y) :
    0 ≤ (kerEX X Y - lam X * kerE X Y) * om X * om Y := by
  have h := cond1 hX hXY
  have hX1 : 0 < X - 1 := by linarith
  have e : kerEX X Y - lam X * kerE X Y = (2 * (X - 1) * kerEX X Y - 3 * kerE X Y) / (2 * (X - 1)) := by
    unfold lam; field_simp
  rw [e]
  have := om_pos hX
  have := om_pos (by linarith : 1 < Y)
  positivity

theorem kerFY_nonpos (hX : 1 < X) (hXY : X < Y) : kerFY X Y ≤ 0 := by
  have h := cond2 hX hXY
  have hY1 : 0 < Y - 1 := by linarith
  have e : kerEY X Y - lam Y * kerE X Y = -((3 * kerE X Y - 2 * (Y - 1) * kerEY X Y) / (2 * (Y - 1))) := by
    unfold lam; field_simp; ring
  unfold kerFY
  rw [e]
  have h1 := om_pos hX
  have h2 := om_pos (by linarith : 1 < Y)
  have : 0 ≤ (3 * kerE X Y - 2 * (Y - 1) * kerEY X Y) / (2 * (Y - 1)) * om X * om Y := by positivity
  linarith

theorem kerFY_X_nonpos (hX : 1 < X) (hXY : X < Y) :
    (kerEXY X Y - lam Y * kerEX X Y - lam X * (kerEY X Y - lam Y * kerE X Y)) * om X * om Y ≤ 0 := by
  have h := cond3 hX hXY
  have hX1 : 0 < X - 1 := by linarith
  have hY1 : 0 < Y - 1 := by linarith
  have e : kerEXY X Y - lam Y * kerEX X Y - lam X * (kerEY X Y - lam Y * kerE X Y)
      = -(-(4 * (X - 1) * (Y - 1) * kerEXY X Y - 6 * (X - 1) * kerEX X Y
          - 6 * (Y - 1) * kerEY X Y + 9 * kerE X Y) / (4 * (X - 1) * (Y - 1))) := by
    unfold lam; field_simp; ring
  rw [e]
  have h1 := om_pos hX
  have h2 := om_pos (by linarith : 1 < Y)
  have h3 : 0 ≤ -(4 * (X - 1) * (Y - 1) * kerEXY X Y - 6 * (X - 1) * kerEX X Y
      - 6 * (Y - 1) * kerEY X Y + 9 * kerE X Y) := by linarith
  have : 0 ≤ -(4 * (X - 1) * (Y - 1) * kerEXY X Y - 6 * (X - 1) * kerEX X Y
          - 6 * (Y - 1) * kerEY X Y + 9 * kerE X Y) / (4 * (X - 1) * (Y - 1)) * om X * om Y := by
    positivity
  linarith

end Signs

/-! ### The hypotheses of Lemma 4 for `F` on `(1, ∞)` -/

/-- $F$ is nondecreasing in its first variable on $1 < s \le s' \le t$. -/
theorem kerF_mono {s s' t : ℝ} (hs : 1 < s) (hss' : s ≤ s') (hs't : s' ≤ t) :
    kerF s t ≤ kerF s' t := by
  have hmono : MonotoneOn (fun X => kerF X t) (Icc s s') := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg
      (f' := fun X => (kerEX X t - lam X * kerE X t) * om X * om t) (convex_Icc s s') ?_ ?_ ?_
    · intro x hx
      exact (hasDerivAt_kerF_X (by linarith [hx.1]) (by linarith [hx.1, hx.2])).continuousAt
        |>.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact (hasDerivAt_kerF_X (by linarith [hx.1]) (by linarith [hx.1, hx.2])).hasDerivWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact kerF_X_nonneg (by linarith [hx.1]) (by linarith [hx.2])
  exact hmono ⟨le_rfl, hss'⟩ ⟨hss', le_rfl⟩ hss'

/-- $F$ is nonincreasing in its second variable on $1 < s \le t \le t'$. -/
theorem kerF_anti {s t t' : ℝ} (hs : 1 < s) (hst : s ≤ t) (htt' : t ≤ t') :
    kerF s t' ≤ kerF s t := by
  have hanti : AntitoneOn (fun Y => kerF s Y) (Icc t t') := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := fun Y => kerFY s Y) (convex_Icc t t') ?_ ?_ ?_
    · intro y hy
      exact (hasDerivAt_kerF_Y hs (by linarith [hy.1])).continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      exact (hasDerivAt_kerF_Y hs (by linarith [hy.1])).hasDerivWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      exact kerFY_nonpos hs (by linarith [hy.1])
  exact hanti ⟨le_rfl, htt'⟩ ⟨htt', le_rfl⟩ htt'

/-- $\partial_Y F$ is nonincreasing in $X$ on $1 < s' \le s < Y$. -/
theorem kerFY_anti {s' s Y : ℝ} (hs' : 1 < s') (hs's : s' ≤ s) (hsY : s < Y) :
    kerFY s Y ≤ kerFY s' Y := by
  have hanti : AntitoneOn (fun X => kerFY X Y) (Icc s' s) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos
      (f' := fun X => (kerEXY X Y - lam Y * kerEX X Y - lam X * (kerEY X Y - lam Y * kerE X Y))
        * om X * om Y) (convex_Icc s' s) ?_ ?_ ?_
    · intro x hx
      exact (hasDerivAt_kerFY_X (by linarith [hx.1]) (by linarith [hx.1, hx.2])).continuousAt
        |>.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact (hasDerivAt_kerFY_X (by linarith [hx.1]) (by linarith [hx.1, hx.2])).hasDerivWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact kerFY_X_nonpos (by linarith [hx.1]) (by linarith [hx.2])
  exact hanti ⟨le_rfl, hs's⟩ ⟨hs's, le_rfl⟩ hs's

/-- **The rectangle inequality** for $F$ on $1 < s' \le s \le t \le t'$. -/
theorem kerF_rect {s' s t t' : ℝ} (hs' : 1 < s') (hs's : s' ≤ s) (hst : s ≤ t) (htt' : t ≤ t') :
    kerF s' t + kerF s t' ≤ kerF s' t' + kerF s t := by
  have hs : 1 < s := by linarith
  have hanti : AntitoneOn (fun Y => kerF s Y - kerF s' Y) (Icc t t') := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := fun Y => kerFY s Y - kerFY s' Y)
      (convex_Icc t t') ?_ ?_ ?_
    · intro y hy
      exact ((hasDerivAt_kerF_Y hs (by linarith [hy.1])).sub
        (hasDerivAt_kerF_Y hs' (by linarith [hy.1]))).continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      exact ((hasDerivAt_kerF_Y hs (by linarith [hy.1])).sub
        (hasDerivAt_kerF_Y hs' (by linarith [hy.1]))).hasDerivWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      have := kerFY_anti hs' hs's (by linarith [hy.1] : s < y)
      linarith
  have := hanti ⟨le_rfl, htt'⟩ ⟨htt', le_rfl⟩ htt'
  simp only at this
  linarith

theorem kerF_nonneg {s t : ℝ} (hs : 1 < s) (hst : s ≤ t) : 0 ≤ kerF s t := by
  unfold kerF
  have := kerE_nonneg hs.le hst
  have := om_pos hs
  have := om_pos (by linarith : 1 < t)
  positivity

/-- **The hypotheses of Lemma 4** hold for $F$ on $(1, \infty)$. -/
theorem intervalHyp_kerF : IntervalHyp (Ioi 1) kerF where
  nonneg _ hs _ _ hst := kerF_nonneg hs hst
  mono _ hs _ _ _ _ h1 h2 := kerF_mono hs h1 h2
  anti _ hs _ _ _ _ h1 h2 := kerF_anti hs h1 h2
  rect _ hs' _ _ _ _ _ _ h1 h2 h3 := kerF_rect hs' h1 h2 h3

/-- **Lemma 3 at the apex `1`**: the kernel $E$ is positive semidefinite on $(1, \infty)$. -/
theorem kerE_psd {ι : Type*} [Fintype ι] (q : ι → ℝ) (hq : ∀ a, 1 < q a) (R : ι → ι → ℝ)
    (hR : PSDForm R) :
    0 ≤ ∑ a, ∑ b, R a b * kerE (min (q a) (q b)) (max (q a) (q b)) := by
  have h := interval_mixture intervalHyp_kerF q (fun a => hq a) _ (hR.weight fun a => (om (q a))⁻¹)
  refine le_of_le_of_eq h (Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_)
  have ha := (om_pos (hq a)).ne'
  have hb := (om_pos (hq b)).ne'
  have hw : om (min (q a) (q b)) * om (max (q a) (q b)) = om (q a) * om (q b) := by
    rcases le_total (q a) (q b) with h | h
    · rw [min_eq_left h, max_eq_right h]
    · rw [min_eq_right h, max_eq_left h, mul_comm]
  unfold kerF
  rw [mul_assoc (kerE _ _), hw]
  field_simp

end

end OpenQuantumProblem40.Thm33
