import Mathlib

/-!
# Theorem 1 of the lower-half note, part 1: interval mixtures (Lemma 4)

Authors: Ansh Mishra, Aryan Senthilkumar. License: MIT.

This file proves Lemma 4 of `math/04-lower-half-new-cases.md` (interval mixtures) in the form used
by the proof of Theorem 1. Let `F` be a real function of two variables such that, on a set `S` of
reals and for `s' ≤ s ≤ t ≤ t'` in `S`,
- `F s t ≥ 0`,
- `F` is nondecreasing in the first variable and nonincreasing in the second,
- `F s' t + F s t' ≤ F s' t' + F s t` (the rectangle inequality).

Then for every finite family of points `p a ∈ S` the kernel `F (min (p a) (p b)) (max (p a) (p b))`
is positive semidefinite. We state positive semidefiniteness in the form that the proof of
Theorem 1 uses: its trace inner product with every positive semidefinite form `R` is
nonnegative (`interval_mixture`). Points may repeat.

The proof is by induction on the set of values of `p`. The smallest value `m` is removed by the
decomposition `F s t = F m t + (F s t - F m t)`: both parts satisfy the hypotheses on the
remaining values, and the points equal to `m` are moved to the next value `m'` at the cost of the
nonnegative rank-one term `(F m m - F m m') 1[p a = m] 1[p b = m]`.

## Main results
- `PSDForm`: a real matrix with nonnegative quadratic form.
- `IntervalHyp`: the hypotheses of Lemma 4 on a set `S`.
- `interval_mixture`: Lemma 4.
-/

namespace OpenQuantumProblem40.Thm33

open Finset

/-- A real matrix `R` indexed by a finite type is a **positive semidefinite form** if
`∑ a b, c a * c b * R a b ≥ 0` for every real vector `c`. -/
def PSDForm {ι : Type*} [Fintype ι] (R : ι → ι → ℝ) : Prop :=
  ∀ c : ι → ℝ, 0 ≤ ∑ a, ∑ b, c a * c b * R a b

/-- Scaling a positive semidefinite form by `e a * e b` keeps it positive semidefinite. -/
theorem PSDForm.weight {ι : Type*} [Fintype ι] {R : ι → ι → ℝ} (hR : PSDForm R) (e : ι → ℝ) :
    PSDForm (fun a b => e a * e b * R a b) := by
  intro c
  have h := hR (fun a => c a * e a)
  refine le_of_le_of_eq h (Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_)
  ring

/-- **The hypotheses of Lemma 4** on a set `S`: `F ≥ 0`, `F` nondecreasing in the first and
nonincreasing in the second variable, and the rectangle inequality, on `{s ≤ t}`. -/
structure IntervalHyp (S : Set ℝ) (F : ℝ → ℝ → ℝ) : Prop where
  nonneg : ∀ s ∈ S, ∀ t ∈ S, s ≤ t → 0 ≤ F s t
  mono : ∀ s ∈ S, ∀ s' ∈ S, ∀ t ∈ S, s ≤ s' → s' ≤ t → F s t ≤ F s' t
  anti : ∀ s ∈ S, ∀ t ∈ S, ∀ t' ∈ S, s ≤ t → t ≤ t' → F s t' ≤ F s t
  rect : ∀ s' ∈ S, ∀ s ∈ S, ∀ t ∈ S, ∀ t' ∈ S, s' ≤ s → s ≤ t → t ≤ t' →
    F s' t + F s t' ≤ F s' t' + F s t

/-- The hypotheses pass to subsets. -/
theorem IntervalHyp.mono_set {S S' : Set ℝ} {F : ℝ → ℝ → ℝ} (hF : IntervalHyp S F)
    (h : S' ⊆ S) : IntervalHyp S' F where
  nonneg s hs t ht hst := hF.nonneg s (h hs) t (h ht) hst
  mono s hs s' hs' t ht h1 h2 := hF.mono s (h hs) s' (h hs') t (h ht) h1 h2
  anti s hs t ht t' ht' h1 h2 := hF.anti s (h hs) t (h ht) t' (h ht') h1 h2
  rect s' hs' s hs t ht t' ht' h1 h2 h3 := hF.rect s' (h hs') s (h hs) t (h ht) t' (h ht') h1 h2 h3

/-- Lemma 4 for the points of a finite set `V`, by induction on `V` (removing its minimum). -/
theorem interval_mixture_aux {ι : Type*} [Fintype ι] (V : Finset ℝ) :
    ∀ (F : ℝ → ℝ → ℝ), IntervalHyp (↑V) F → ∀ (p : ι → ℝ), (∀ a, p a ∈ V) →
      ∀ R : ι → ι → ℝ, PSDForm R →
        0 ≤ ∑ a, ∑ b, R a b * F (min (p a) (p b)) (max (p a) (p b)) := by
  classical
  induction V using Finset.induction_on_min with
  | empty =>
    intro F _ p hp R _
    have : IsEmpty ι := ⟨fun a => by simpa using hp a⟩
    simp
  | insert m V hm ih =>
    intro F hF p hp R hR
    have hmS : m ∈ (↑(insert m V) : Set ℝ) := by simp
    have hVS : ∀ x ∈ V, x ∈ (↑(insert m V) : Set ℝ) := fun x hx => by simp [hx]
    rcases V.eq_empty_or_nonempty with hV | hV
    · -- all points are equal to `m`
      subst hV
      have hpm : ∀ a, p a = m := fun a => by simpa using hp a
      have h1 := hR (fun _ => 1)
      have h2 : 0 ≤ F m m := hF.nonneg m hmS m hmS le_rfl
      have e : ∑ a, ∑ b, R a b * F (min (p a) (p b)) (max (p a) (p b))
          = F m m * ∑ a, ∑ b, (fun _ => (1 : ℝ)) a * (fun _ => (1 : ℝ)) b * R a b := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [hpm a, hpm b, min_self, max_self]
        ring
      rw [e]
      exact mul_nonneg h2 h1
    · set m' := V.min' hV with hm'def
      have hm'V : m' ∈ V := V.min'_mem hV
      have hmm' : m < m' := hm m' hm'V
      have hle : ∀ x ∈ V, m' ≤ x := fun x hx => V.min'_le x hx
      -- the points other than `m` lie in `V`
      have hpV : ∀ a, p a ≠ m → p a ∈ V := by
        intro a ha
        have := hp a
        rw [Finset.mem_insert] at this
        exact this.resolve_left ha
      let p' : ι → ℝ := fun a => if p a = m then m' else p a
      have hp' : ∀ a, p' a ∈ V := by
        intro a
        by_cases h : p a = m
        · simp only [p', h, if_true]; exact hm'V
        · simp only [p', h, if_false]; exact hpV a h
      let ind : ι → ℝ := fun a => if p a = m then 1 else 0
      let ind' : ι → ℝ := fun a => if p a = m then 0 else 1
      let Φ : ℝ → ℝ → ℝ := fun _ t => F m t
      let G : ℝ → ℝ → ℝ := fun s t => F s t - F m t
      have hmlt : ∀ x ∈ V, m ≤ x := fun x hx => (hm x hx).le
      have hΦ : IntervalHyp (↑V) Φ := by
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro s hs t ht _
          exact hF.nonneg m hmS t (hVS t ht) (hmlt t ht)
        · intro s _ s' _ t _ _ _
          exact le_rfl
        · intro s _ t ht t' ht' _ htt'
          exact hF.anti m hmS t (hVS t ht) t' (hVS t' ht') (hmlt t ht) htt'
        · intro s' _ s _ t _ t' _ _ _ _
          show F m t + F m t' ≤ F m t' + F m t
          linarith
      have hG : IntervalHyp (↑V) G := by
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro s hs t ht hst
          have := hF.mono m hmS s (hVS s hs) t (hVS t ht) (hmlt s hs) hst
          show 0 ≤ F s t - F m t
          linarith
        · intro s hs s' hs' t ht h1 h2
          have := hF.mono s (hVS s hs) s' (hVS s' hs') t (hVS t ht) h1 h2
          show F s t - F m t ≤ F s' t - F m t
          linarith
        · intro s hs t ht t' ht' h1 h2
          have := hF.rect m hmS s (hVS s hs) t (hVS t ht) t' (hVS t' ht') (hmlt s hs) h1 h2
          show F s t' - F m t' ≤ F s t - F m t
          linarith
        · intro s' hs' s hs t ht t' ht' h1 h2 h3
          have := hF.rect s' (hVS s' hs') s (hVS s hs) t (hVS t ht) t' (hVS t' ht') h1 h2 h3
          show F s' t - F m t + (F s t' - F m t') ≤ F s' t' - F m t' + (F s t - F m t)
          linarith
      -- the decomposition of the kernel
      have hdecomp : ∀ a b, F (min (p a) (p b)) (max (p a) (p b)) =
          (F m m - F m m') * (ind a * ind b) + Φ (min (p' a) (p' b)) (max (p' a) (p' b))
            + ind' a * ind' b * G (min (p' a) (p' b)) (max (p' a) (p' b)) := by
        intro a b
        by_cases ha : p a = m <;> by_cases hb : p b = m
        · simp only [p', ind, ind', Φ, G, ha, hb, if_true, min_self, max_self]
          ring
        · have hb1 : m < p b := hm (p b) (hpV b hb)
          have hb2 : m' ≤ p b := hle (p b) (hpV b hb)
          simp only [p', ind, ind', Φ, G, ha, hb, if_true, if_false, min_eq_left hb1.le,
            max_eq_right hb1.le, max_eq_right hb2]
          ring
        · have ha1 : m < p a := hm (p a) (hpV a ha)
          have ha2 : m' ≤ p a := hle (p a) (hpV a ha)
          simp only [p', ind, ind', Φ, G, ha, hb, if_true, if_false, min_eq_right ha1.le,
            max_eq_left ha1.le, max_eq_left ha2]
          ring
        · simp only [p', ind, ind', Φ, G, ha, hb, if_false]
          ring
      have e : ∑ a, ∑ b, R a b * F (min (p a) (p b)) (max (p a) (p b))
          = (F m m - F m m') * ∑ a, ∑ b, ind a * ind b * R a b
            + ∑ a, ∑ b, R a b * Φ (min (p' a) (p' b)) (max (p' a) (p' b))
            + ∑ a, ∑ b, (fun a b => ind' a * ind' b * R a b) a b
                * G (min (p' a) (p' b)) (max (p' a) (p' b)) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [hdecomp a b]
        ring
      rw [e]
      have t1 : 0 ≤ (F m m - F m m') * ∑ a, ∑ b, ind a * ind b * R a b :=
        mul_nonneg (sub_nonneg.2 (hF.anti m hmS m hmS m' (hVS m' hm'V) le_rfl hmm'.le)) (hR ind)
      have t2 := ih Φ hΦ p' hp' R hR
      have t3 := ih G hG p' hp' _ (hR.weight ind')
      linarith

/-- **Lemma 4 (interval mixtures).** If `F` satisfies the hypotheses of Lemma 4 on `S`, then for
all points `p a ∈ S` (repetitions allowed) and every positive semidefinite form `R`,
`∑ a b, R a b * F (min (p a) (p b)) (max (p a) (p b)) ≥ 0`. -/
theorem interval_mixture {ι : Type*} [Fintype ι] {S : Set ℝ} {F : ℝ → ℝ → ℝ}
    (hF : IntervalHyp S F) (p : ι → ℝ) (hp : ∀ a, p a ∈ S) (R : ι → ι → ℝ) (hR : PSDForm R) :
    0 ≤ ∑ a, ∑ b, R a b * F (min (p a) (p b)) (max (p a) (p b)) := by
  classical
  refine interval_mixture_aux (Finset.univ.image p) F (hF.mono_set ?_) p
    (fun a => Finset.mem_image_of_mem p (Finset.mem_univ a)) R hR
  intro x hx
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hx
  exact hp a

end OpenQuantumProblem40.Thm33
