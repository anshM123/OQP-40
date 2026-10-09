import OQP40.Thm33Kernel

/-!
# Theorem 1 of the lower-half note, part 4: the apex shares and the finite inequality

Authors: Ansh Mishra, Aryan Senthilkumar. License: MIT.

This file proves the finite form of Theorem 1 of `math/04-lower-half-new-cases.md`: for a positive
semidefinite complex matrix `b` and reals `α i ≥ 0`,
$$\sum_{i,j,k} \operatorname{Re}(b_{ij} b_{jk} b_{ki})\, \kappa(\alpha_i, \alpha_j, \alpha_k) \ge 0
\qquad (\texttt{kernel\_sum\_nonneg}).$$
In the proof of Theorem 1, `b` is the second matrix written in an eigenbasis of the first, and the
`α i` are the eigenvalues of the first matrix.

The proof follows Sections 2.2-2.4 of the note, with the indices themselves (whose values `α i`
may repeat) in place of the distinct eigenvalues:
- **The certificate** (Section 2.3, `share`): the value of κ on a triple of points is split among
  the three points; the largest point gets $\operatorname{cap}$, the smallest gets
  $E = \kappa - \operatorname{cap}$, the middle one gets `0`. Points with equal values give no
  share, and the share identity still holds (`share_add_share_add_share`).
- **Lemma 2** (`sum_kappa_eq_three_mul_sum_share`): by the rotation invariance of
  $T(i,j,k) = b_{ij} b_{jk} b_{ki}$ the triple sum equals three times
  $\sum_l \sum_{a,b} \operatorname{Re} T(l,a,b)\, G^{(l)}_{ab}$.
- **The matrices $R^{(l)}_{ab} = \operatorname{Re} T(l,a,b)$ are positive semidefinite**
  (`psdForm_reT`).
- **Each $G^{(l)}$ pairs nonnegatively with $R^{(l)}$** (`sum_mul_share_nonneg`): the block below
  the apex is a rank-one matrix $u u^T$, the block above the apex is the kernel $E$ of Lemma 3,
  rescaled to the apex `1` (`above_eq`, `OQP40/Thm33Kernel.lean`).
- **Semidefinite case** (Section 2.6): for `α i ≥ 0` the inequality follows from the case
  `α i > 0` by letting `α i + ε → α i`.
-/

namespace OpenQuantumProblem40.Thm33

noncomputable section

open Matrix Finset Filter Topology
open scoped ComplexOrder

/-! ### The certificate -/

/-- $\operatorname{cap}_z(x,y) = (z-x)(z-y)\sqrt{z+4x}\sqrt{z+4y}$, the share of the largest
point `z` of a triple. -/
def cap (x y z : ℝ) : ℝ := (z - x) * (z - y) * Real.sqrt (z + 4 * x) * Real.sqrt (z + 4 * y)

/-- $E_x(y,z) = \kappa(x,y,z) - \operatorname{cap}_{\max(y,z)}(x, \min(y,z))$, the share of the
smallest point `x` of a triple. -/
def above (x y z : ℝ) : ℝ := kappa x y z - cap x (min y z) (max y z)

/-- **The share** $G^{(l)}_{ab}$ of the point with value `x` in the triple with values `x, y, z`:
`cap` if `x` is the largest value, `above` if it is the smallest, `0` otherwise (in particular if
two of the values are equal and one of them is `x`). -/
def share (x y z : ℝ) : ℝ :=
  if y < x ∧ z < x then cap y z x else if x < y ∧ x < z then above x y z else 0

theorem kappa_comm12 (x y z : ℝ) : kappa x y z = kappa y x z := by unfold kappa; ring

theorem kappa_comm23 (x y z : ℝ) : kappa x y z = kappa x z y := by unfold kappa; ring

theorem cap_comm (x y z : ℝ) : cap x y z = cap y x z := by unfold cap; ring

theorem share_comm (x y z : ℝ) : share x y z = share x z y := by
  unfold share above
  rw [cap_comm y z x, min_comm z y, max_comm z y, kappa_comm23 x z y]
  by_cases h1 : y < x ∧ z < x
  · rw [if_pos h1, if_pos (show z < x ∧ y < x from ⟨h1.2, h1.1⟩)]
  · rw [if_neg h1, if_neg (show ¬(z < x ∧ y < x) from fun h => h1 ⟨h.2, h.1⟩)]
    by_cases h2 : x < y ∧ x < z
    · rw [if_pos h2, if_pos (show x < z ∧ x < y from ⟨h2.2, h2.1⟩)]
    · rw [if_neg h2, if_neg (show ¬(x < z ∧ x < y) from fun h => h2 ⟨h.2, h.1⟩)]

/-- The sum of the three shares of a triple. -/
def shareSum (x y z : ℝ) : ℝ := share x y z + share y z x + share z x y

theorem shareSum_rotate (x y z : ℝ) : shareSum x y z = shareSum y z x := by
  unfold shareSum; ring

theorem shareSum_swap (x y z : ℝ) : shareSum x y z = shareSum x z y := by
  unfold shareSum
  rw [share_comm x y z, share_comm z x y, share_comm y z x]
  ring

/-- The share identity for sorted values. -/
theorem shareSum_sorted {x y z : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hyz : y ≤ z) :
    shareSum x y z = kappa x y z := by
  unfold shareSum
  rcases hxy.lt_or_eq with hxy | rfl <;> rcases hyz.lt_or_eq with hyz | rfl
  · -- x < y < z
    have hxz := hxy.trans hyz
    rw [share, if_neg (fun h => absurd h.1 (not_lt.2 hxy.le)), if_pos ⟨hxy, hxz⟩,
      share, if_neg (fun h => absurd h.1 (not_lt.2 hyz.le)),
      if_neg (fun h => absurd h.2 (not_lt.2 hxy.le)),
      share, if_pos ⟨hxz, hyz⟩, above, min_eq_left hyz.le, max_eq_right hyz.le]
    ring
  · -- x < y = z
    rw [share, if_neg (fun h => absurd h.1 (not_lt.2 hxy.le)), if_pos ⟨hxy, hxy⟩,
      share, if_neg (fun h => lt_irrefl y h.1), if_neg (fun h => lt_irrefl y h.1),
      share, if_neg (fun h => lt_irrefl y h.2), if_neg (fun h => absurd h.1 (not_lt.2 hxy.le)),
      above, min_self, max_self, cap]
    ring
  · -- x = y < z
    rw [share, if_neg (fun h => lt_irrefl x h.1), if_neg (fun h => lt_irrefl x h.1),
      share, if_neg (fun h => lt_irrefl x h.2), if_neg (fun h => lt_irrefl x h.2),
      share, if_pos ⟨hyz, hyz⟩, cap]
    have h := Real.mul_self_sqrt (by linarith : 0 ≤ z + 4 * x)
    unfold kappa
    linear_combination (z - x) * (z - x) * h
  · -- x = y = z
    rw [share, if_neg (fun h => lt_irrefl x h.1), if_neg (fun h => lt_irrefl x h.1)]
    unfold kappa
    ring

/-- **The share identity**: for values `x, y, z ≥ 0` the three shares add up to
$\kappa(x,y,z)$. -/
theorem share_add_share_add_share {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    share x y z + share y z x + share z x y = kappa x y z := by
  change shareSum x y z = kappa x y z
  rcases le_total x y with hxy | hxy <;> rcases le_total y z with hyz | hyz <;>
    rcases le_total x z with hxz | hxz
  · exact shareSum_sorted hx hxy hyz
  · exact shareSum_sorted hx hxy hyz
  · rw [shareSum_swap, shareSum_sorted hx hxz hyz, kappa_comm23]
  · rw [shareSum_rotate, shareSum_rotate, shareSum_sorted hz hxz hxy]; unfold kappa; ring
  · rw [shareSum_swap, shareSum_rotate, shareSum_rotate, shareSum_sorted hy hxy hxz]
    unfold kappa; ring
  · rw [shareSum_rotate, shareSum_sorted hy hyz hxz]; unfold kappa; ring
  · rw [shareSum_swap, shareSum_rotate, shareSum_rotate, shareSum_sorted hy hxy hxz]
    unfold kappa; ring
  · rw [shareSum_swap, shareSum_rotate, shareSum_sorted hz hyz hxy]; unfold kappa; ring

/-! ### Homogeneity: the block above the apex is the kernel of Lemma 3 -/

theorem kappa_scale (x X Y : ℝ) : kappa x (x * X) (x * Y) = x ^ 3 * kappa 1 X Y := by
  unfold kappa; ring

theorem cap_scale {x X Y : ℝ} (hx : 0 ≤ x) (hY : 0 ≤ Y + 4) :
    cap x (x * X) (x * Y) = x ^ 3 * (ell X Y * rt X Y) := by
  unfold cap ell rt rad
  rw [show x * Y + 4 * x = x * (Y + 4) by ring, show x * Y + 4 * (x * X) = x * (Y + 4 * X) by ring,
    Real.sqrt_mul hx, Real.sqrt_mul hx, Real.sqrt_mul hY]
  have h := Real.mul_self_sqrt hx
  linear_combination (x ^ 2 * (Y - 1) * (Y - X) * Real.sqrt (Y + 4) * Real.sqrt (Y + 4 * X)) * h

/-- **Homogeneity**: for `0 < x < y, z`,
$E_x(y,z) = x^3 E(\min(y,z)/x, \max(y,z)/x)$ with the kernel $E$ at the apex `1`. -/
theorem above_eq {x y z : ℝ} (hx : 0 < x) (hy : x < y) :
    above x y z = x ^ 3 * kerE (min y z / x) (max y z / x) := by
  have hm : min y z = x * (min y z / x) := by field_simp
  have hM : max y z = x * (max y z / x) := by field_simp
  have hY : 0 ≤ max y z / x + 4 := by
    have : 0 < max y z / x := div_pos (by linarith [le_max_left y z]) hx
    linarith
  have hk : kappa x y z = kappa x (min y z) (max y z) := by
    rcases le_total y z with h | h
    · rw [min_eq_left h, max_eq_right h]
    · rw [min_eq_right h, max_eq_left h, kappa_comm23]
  unfold above kerE
  rw [hk]
  conv_lhs => rw [hm, hM]
  rw [kappa_scale, cap_scale hx.le hY]
  ring

/-! ### Each `G^(l)` pairs nonnegatively with a positive semidefinite form -/

/-- The vector $u$ of the block below the apex `x`. -/
def below (x y : ℝ) : ℝ := if y < x then (x - y) * Real.sqrt (x + 4 * y) else 0

/-- The indicator of the points above the apex `x`. -/
def isAbove (x y : ℝ) : ℝ := if x < y then 1 else 0

/-- The rescaled point $y / x$ for the points above the apex (and `2` for the others). -/
def scaled (x y : ℝ) : ℝ := if x < y then y / x else 2

theorem one_lt_scaled {x : ℝ} (hx : 0 < x) (y : ℝ) : 1 < scaled x y := by
  unfold scaled
  split_ifs with h
  · rw [lt_div_iff₀ hx]; linarith
  · norm_num

/-- The share of the apex `x` splits into the block below and the block above. -/
theorem share_split {x : ℝ} (hx : 0 < x) (y z : ℝ) :
    share x y z = below x y * below x z
      + x ^ 3 * (isAbove x y * isAbove x z
          * kerE (min (scaled x y) (scaled x z)) (max (scaled x y) (scaled x z))) := by
  by_cases hQ : x < y ∧ x < z
  · -- both points above the apex
    have hP : ¬(y < x ∧ z < x) := fun h => absurd h.1 (not_lt.2 hQ.1.le)
    rw [share, if_neg hP, if_pos hQ, above_eq hx hQ.1]
    unfold below isAbove scaled
    simp only [if_pos hQ.1, if_pos hQ.2, if_neg (not_lt.2 hQ.1.le), if_neg (not_lt.2 hQ.2.le),
      min_div_div_right hx.le, max_div_div_right hx.le]
    ring
  · by_cases hP : y < x ∧ z < x
    · -- both points below the apex
      rw [share, if_pos hP]
      unfold below isAbove cap
      simp only [if_pos hP.1, if_pos hP.2, if_neg (not_lt.2 hP.1.le), if_neg (not_lt.2 hP.2.le)]
      ring
    · -- otherwise the share is `0`, and so are both blocks
      rw [share, if_neg hP, if_neg hQ]
      have hb : below x y * below x z = 0 := by
        unfold below
        by_cases hy : y < x
        · rw [if_pos hy, if_neg (fun hz => hP ⟨hy, hz⟩), mul_zero]
        · rw [if_neg hy, zero_mul]
      have ha : isAbove x y * isAbove x z = 0 := by
        unfold isAbove
        by_cases hy : x < y
        · rw [if_pos hy, if_neg (fun hz => hQ ⟨hy, hz⟩), mul_zero]
        · rw [if_neg hy, zero_mul]
      rw [hb, ha]
      ring

/-- **The pairing with one apex**: for an apex value `x > 0`, any values `α a`, and a positive
semidefinite form `R`, $\sum_{a,b} R_{ab}\, G^{(x)}_{ab} \ge 0$. -/
theorem sum_mul_share_nonneg {ι : Type*} [Fintype ι] {x : ℝ} (hx : 0 < x) (α : ι → ℝ)
    (R : ι → ι → ℝ) (hR : PSDForm R) :
    0 ≤ ∑ a, ∑ b, R a b * share x (α a) (α b) := by
  have h1 := hR (fun a => below x (α a))
  have h2 := kerE_psd (fun a => scaled x (α a)) (fun a => one_lt_scaled hx (α a)) _
    (hR.weight fun a => isAbove x (α a))
  have e : ∑ a, ∑ b, R a b * share x (α a) (α b)
      = ∑ a, ∑ b, below x (α a) * below x (α b) * R a b
        + x ^ 3 * ∑ a, ∑ b, (isAbove x (α a) * isAbove x (α b) * R a b)
          * kerE (min (scaled x (α a)) (scaled x (α b))) (max (scaled x (α a)) (scaled x (α b))) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [share_split hx]
    ring
  rw [e]
  have := pow_pos hx 3
  positivity

/-! ### Lemma 2: the reduction to the apex shares -/

/-- Rotating the summation variables of a triple sum. -/
theorem sum_rotate {ι : Type*} [Fintype ι] (g : ι → ι → ι → ℝ) :
    ∑ i, ∑ j, ∑ k, g j k i = ∑ i, ∑ j, ∑ k, g i j k := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]

/-- **Lemma 2.** If `T` is invariant under rotation of its arguments and the values `α i` are
`≥ 0`, then $\sum_{i,j,k} T(i,j,k)\,\kappa(\alpha_i,\alpha_j,\alpha_k)
= 3 \sum_l \sum_{a,b} T(l,a,b)\, G^{(l)}_{ab}$. -/
theorem sum_kappa_eq_three_mul_sum_share {ι : Type*} [Fintype ι] (T : ι → ι → ι → ℝ)
    (hT : ∀ i j k, T i j k = T j k i) (α : ι → ℝ) (hα : ∀ i, 0 ≤ α i) :
    ∑ i, ∑ j, ∑ k, T i j k * kappa (α i) (α j) (α k)
      = 3 * ∑ l, ∑ a, ∑ b, T l a b * share (α l) (α a) (α b) := by
  have e1 : ∑ i, ∑ j, ∑ k, T i j k * kappa (α i) (α j) (α k)
      = ∑ i, ∑ j, ∑ k, T i j k * share (α i) (α j) (α k)
        + ∑ i, ∑ j, ∑ k, T i j k * share (α j) (α k) (α i)
        + ∑ i, ∑ j, ∑ k, T i j k * share (α k) (α i) (α j) := by
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => ?_
    rw [← share_add_share_add_share (hα i) (hα j) (hα k)]
    ring
  have e2 : ∑ i, ∑ j, ∑ k, T i j k * share (α j) (α k) (α i)
      = ∑ i, ∑ j, ∑ k, T i j k * share (α i) (α j) (α k) := by
    rw [← sum_rotate (fun l a b => T l a b * share (α l) (α a) (α b))]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => ?_
    rw [hT i j k]
  have e3 : ∑ i, ∑ j, ∑ k, T i j k * share (α k) (α i) (α j)
      = ∑ i, ∑ j, ∑ k, T i j k * share (α i) (α j) (α k) := by
    rw [sum_rotate (fun a b c => T c a b * share (α c) (α a) (α b))]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => ?_
    rw [hT i j k, hT j k i]
  rw [e1, e2, e3]
  ring

/-! ### The matrices `R^(l)` are positive semidefinite -/

/-- For a positive semidefinite `b` and every `l`, the real matrix
$R^{(l)}_{ac} = \operatorname{Re}(b_{la} b_{ac} b_{cl})$ is positive semidefinite: for real
`y`, $\sum_{a,c} y_a y_c R^{(l)}_{ac} = \operatorname{Re}(w^* b\, w)$ with $w_c = y_c b_{cl}$. -/
theorem psdForm_reT {n : Type*} [Fintype n] {b : Matrix n n ℂ} (hb : b.PosSemidef) (l : n) :
    PSDForm (fun a c => (b l a * b a c * b c l).re) := by
  intro y
  set w : n → ℂ := fun a => (y a : ℂ) * b a l with hw
  have h := hb.dotProduct_mulVec_nonneg w
  have hre : 0 ≤ (star w ⬝ᵥ (b *ᵥ w)).re := (Complex.nonneg_iff.1 h).1
  have e : star w ⬝ᵥ (b *ᵥ w) = ∑ a, ∑ c, ((y a * y c : ℝ) : ℂ) * (b l a * b a c * b c l) := by
    simp only [dotProduct, mulVec, Pi.star_apply, hw, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    rw [star_mul', hb.isHermitian.apply l a, Complex.star_def, Complex.conj_ofReal]
    push_cast
    ring
  rw [e, Complex.re_sum] at hre
  refine le_of_le_of_eq hre (Finset.sum_congr rfl fun a _ => ?_)
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Complex.re_ofReal_mul]

/-! ### The finite inequality -/

/-- **The finite inequality for positive values**: for `b` positive semidefinite and `α i > 0`,
$\sum_{i,j,k} \operatorname{Re}(b_{ij} b_{jk} b_{ki})\,\kappa(\alpha_i,\alpha_j,\alpha_k) \ge 0$. -/
theorem kernel_sum_nonneg_of_pos {n : Type*} [Fintype n] {b : Matrix n n ℂ} (hb : b.PosSemidef)
    (α : n → ℝ) (hα : ∀ i, 0 < α i) :
    0 ≤ ∑ i, ∑ j, ∑ k, (b i j * b j k * b k i).re * kappa (α i) (α j) (α k) := by
  rw [sum_kappa_eq_three_mul_sum_share (fun i j k => (b i j * b j k * b k i).re)
    (fun i j k => by ring_nf) α (fun i => (hα i).le)]
  refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun l _ => ?_)
  exact sum_mul_share_nonneg (hα l) α _ (psdForm_reT hb l)

/-- **The finite inequality** (Theorem 1 in the eigenbasis of the first matrix): for `b` positive
semidefinite and `α i ≥ 0`,
$\sum_{i,j,k} \operatorname{Re}(b_{ij} b_{jk} b_{ki})\,\kappa(\alpha_i,\alpha_j,\alpha_k) \ge 0$. -/
theorem kernel_sum_nonneg {n : Type*} [Fintype n] {b : Matrix n n ℂ} (hb : b.PosSemidef)
    (α : n → ℝ) (hα : ∀ i, 0 ≤ α i) :
    0 ≤ ∑ i, ∑ j, ∑ k, (b i j * b j k * b k i).re * kappa (α i) (α j) (α k) := by
  set f : ℝ → ℝ := fun ε => ∑ i, ∑ j, ∑ k, (b i j * b j k * b k i).re
    * kappa (α i + ε) (α j + ε) (α k + ε) with hf
  have hc : Continuous f := by
    rw [hf]
    unfold kappa
    fun_prop
  have hpos : ∀ ε > 0, 0 ≤ f ε := fun ε hε =>
    kernel_sum_nonneg_of_pos hb (fun i => α i + ε) (fun i => by linarith [hα i])
  have hlim : Tendsto f (𝓝[>] 0) (𝓝 (f 0)) :=
    hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have h0 := ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun ε hε => hpos ε hε)
  simpa [hf] using h0

end

end OpenQuantumProblem40.Thm33
