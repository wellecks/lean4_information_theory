/- F-divergences and their basic properties

This file defines f-divergences $D_f(p || q) = ∑_x q(x) f(p(x)/q(x))$ for discrete,
finite probability mass functions `p` and `q`.

## Scope and Limitations

This formalization currently restricts the defining function `f` to be `ℝ → ℝ`.
This means divergences like the standard KL divergence (`f(t) = t log t`) are supported,
but others like the reverse KL divergence (which involve ∞) are currently excluded.

This restriction is currently in place for pragmatic reasons related to
boundary cases and existing mathlib infrastructure (at least as I understood them):

- Convexity: we need to prove convexity on `Set.Ici 0` (`[0, ∞)`). I wasn't sure how to
  do this for a function with a EReal or ENNReal co-domain.

- Jensen's inequality: basic results like non-negativity depend on Jensen's inequality.
  I believe this again requires convexity on `Set.Ici 0` (`[0, ∞)`) in its current form.
  Invoking Jensen's inequality on `Set.Ioi 0` (`(0, ∞)`) runs into issues since `(p x / q x)`
  can equal zero, and a condition for Jensen's inequality is that `(p x / q x)` is in the
  set over which convexity holds.

These issues are perhaps not insurmountable, but as a start this file supports a strict subset
of $f$-divergences.

We use our discrete, finite-alphabet `pmf`.

References:
- https://people.ece.cornell.edu/zivg/ECE_5630_Lectures6.pdf
- https://www.ee.bgu.ac.il/~haimp/ml/lectures/lect10_f_div/Lecture_on_f_divergence_and_hypothesis_testing
- https://en.wikipedia.org/wiki/F-divergence
- https://www.personal.soton.ac.uk/cz1y20/Reading_Group/mlts-2023w/Tsybakov_Nonparametric_Estimation.pdf

Author: Sean Welleck
-/
import LLMlean

import InformationTheory.InformationTheory
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions

open InformationTheory

namespace InformationTheory

noncomputable section

open Classical BigOperators Real Set

variable {Ω : Type*}[Fintype Ω]

class FDivFunction (f : ℝ → ℝ) where
  one : f 1 = 0
  convex : ConvexOn ℝ (Set.Ici 0) f

def fdiv (f : ℝ → ℝ) [FDivFunction f] (p q : pmf Ω) [Dominates q p]: ℝ :=
  ∑ x, q x * f (p x / q x)

lemma jensens_invocation
  (f: ℝ → ℝ) [FDivFunction f] (g: Ω → ℝ) (q: pmf Ω)
  (hmem: ∀ x ∈ Finset.univ, g x ∈ (Set.Ici 0)) :
  ∑ x : Ω, (q x) * f (g x) ≥ f (∑ x : Ω, (q x) * (g x)) := by
    have hsum : ∑ x : Ω, q x = 1 := by
      simp [pmf.sum_one']
    have hnonneg : ∀ x ∈ Finset.univ, 0 ≤ q x := by
      intro x hx
      exact q.non_neg x
    refine' FDivFunction.convex.map_sum_le (s := Set.Ici 0) hnonneg hsum hmem

lemma sum_cancel (f : ℝ → ℝ) [FDivFunction f] (p q : pmf Ω) [Dominates q p] :
    ∑ x, q.f x * (p.f x / q.f x) = ∑ x, p.f x := by
    apply Finset.sum_congr rfl
    intro x hx
    by_cases h : q x = 0
    · simp_all [dominates_qx0_px0 p q x]
    · field_simp [h]

/- F-divergence is non-negative. -/
theorem fdiv_nonneg (f : ℝ → ℝ) [FDivFunction f] (p q : pmf Ω) [Dominates q p]:
    0 ≤ fdiv f p q := by
  calc
    ∑ x, q x * f (p x / q x)
        ≥ f (∑ x, q x * (p x / q x)) := by
          have hmem : ∀ x ∈ Finset.univ, p.f x / q.f x ∈ Set.Ici 0 := by
            intro x hx
            by_cases h : q x = 0
            simp_all
            exact div_nonneg (p.non_neg x) (q.non_neg x)
          exact jensens_invocation f (λ x => (p x / q x)) q hmem
      _ = f (∑ x, p.f x) := by rw [sum_cancel f p q]
      _ = f 1 := by rw [pmf.sum_one']
      _ = 0 := by exact FDivFunction.one

/- KL divergence is a f-divergence. -/
def kldivF : ℝ → ℝ := fun x ↦ x * log x

instance : FDivFunction kldivF where
  one := by simp [kldivF]
  convex := Real.convexOn_mul_log

theorem kldiv_is_fdivergence (p q : pmf Ω) [Dominates q p] :
  fdiv kldivF p q = kld p q := by
  unfold fdiv kldivF kld
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hp : p x = 0
  · simp [hp]
  · have hq : q x ≠ 0 := dominates_pxne0_qxne0 p q x hp
    field_simp [hq, hp]

theorem kldiv_nonneg (p q : pmf Ω) [Dominates q p] :
  0 ≤ kld p q := by
  rw [← kldiv_is_fdivergence]
  exact fdiv_nonneg kldivF p q

theorem kldiv_self (p : pmf Ω) [Dominates p p] :
  0 = kld p p := by
  unfold kld; simp


/- Total variation distance. -/
def tvF : ℝ → ℝ := fun x ↦
  (1 / 2) * |x - 1|

instance : FDivFunction tvF where
  one := by simp [tvF]
  convex := by
    unfold tvF
    apply ConvexOn.smul
    · norm_num
    · simp_rw [abs_eq_max_neg]
      apply ConvexOn.sup
      · exact ConvexOn.sub
          (convexOn_id (convex_Ici 0))
          (concaveOn_const 1 (convex_Ici 0))
      · simp
        exact ConvexOn.sub
          (convexOn_const 1 (convex_Ici 0))
          (convexOn_id (convex_Ici 0))

def tvd (p q: pmf Ω)[Dominates q p]: ℝ :=
   ∑ x, (1/2)*|p x - q x|

/- Total variation distance is a f-divergence. -/
theorem tvd_is_fdivergence (p q : pmf Ω) [Dominates q p] :
  fdiv tvF p q = tvd p q := by
  unfold fdiv tvF tvd
  apply Finset.sum_congr rfl
  intro x hx
  field_simp
  by_cases hq : q x = 0
  · simp_all [dominates_qx0_px0 p q x hq]
  · field_simp [px_pos, abs_div, abs_of_pos]

theorem tvd_nonneg (p q : pmf Ω) [Dominates q p] :
  0 ≤ tvd p q := by
  rw [← tvd_is_fdivergence]
  exact fdiv_nonneg tvF p q

theorem tvd_leq_one (p q : pmf Ω) [Dominates q p] : tvd p q ≤ 1 := by
  unfold tvd
  calc ∑ x, 1 / 2 * |p.f x - q.f x|
        = ∑ x, 1 / 2 * |- q x + p x| := by
          apply Finset.sum_congr rfl
          intro x hx
          simp [neg_add_eq_sub]
      _ ≤ ∑ x, (1/2*|- q x| + 1/2*|p x|) := by
          apply Finset.sum_le_sum
          intro x hx
          rw [← mul_add]
          apply mul_le_mul_of_nonneg_left
          apply abs_add
          norm_num
      _ ≤ 1 := by
          calc ∑ x, (1/2*|- q x| + 1/2*|p x|)
              = ∑ x, 1/2*|- q x| + ∑ x, 1/2*|p x| := by
                  apply Finset.sum_add_distrib
            _ = 1/2 * ∑ x, |- q x| + 1/2 * ∑ x, |p x| := by
                  rw [← Finset.mul_sum, ← Finset.mul_sum]
            _ = 1/2 * 1 + 1/2 * 1 := by
                  simp [abs_of_nonneg (q.non_neg _),
                        abs_of_nonneg (p.non_neg _), pmf.sum_one']
            _ = 1 := by norm_num
          norm_num

theorem tvd_self (p : pmf Ω)[Dominates p p] : 0 = tvd p p := by
  unfold tvd; field_simp

theorem tvd_comm (p q : pmf Ω)[Dominates q p][Dominates p q] : tvd p q = tvd q p := by
  unfold tvd
  apply Finset.sum_congr rfl
  intro x hx
  rw [abs_sub_comm (p x) (q x)]

theorem tvd_triangle (p q r : pmf Ω) [Dominates q p][Dominates r q][Dominates r p] :
  tvd p r ≤ tvd p q + tvd q r := by
  unfold tvd
  repeat (ring_nf; rw [← Finset.sum_mul])
  field_simp
  gcongr
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x hx
  apply abs_sub_le

theorem tvd_zero_iff_eq (p q : pmf Ω)[Dominates q p] : tvd p q = 0 ↔ p = q := by
  constructor
  · intro h
    unfold tvd at h
    ring_nf at h
    rw [Finset.sum_eq_zero_iff_of_nonneg] at h
    · simp_all
      apply InformationTheory.ext
      intro x
      specialize h x
      linarith
    · simp
  · intro h
    unfold tvd
    rw [h]
    simp

-- Discrete version of Lemma 2.1 in Tsybakov
theorem scheffes_theorem (p q : pmf Ω)[Dominates q p] :
  tvd p q = 1 - ∑ x, min (p x) (q x) := by
  unfold tvd
  rw [← Finset.mul_sum]
  have l₁ (x y : ℝ): min x y = (x + y - |x - y|) / 2 := by
    rcases le_total x y with h_x_le_y | h_y_le_x
    · rw [min_eq_left h_x_le_y]
      rw [abs_of_nonpos (sub_nonpos.mpr h_x_le_y)]
      ring
    · rw [min_eq_right h_y_le_x]
      rw [abs_eq_self.mpr (sub_nonneg.mpr h_y_le_x)]
      ring
  have l₂ (x y : ℝ) : |x - y| = x + y - 2 * min x y := by
    linarith [l₁ x y]
  have : ∑ x, |p x - q x| = ∑ x, (p x + q x - 2 * min (p x) (q x)) := by
    apply Finset.sum_congr rfl
    intro x _
    rw [l₂]
  rw [this]
  rw [Finset.sum_sub_distrib]
  rw [Finset.sum_add_distrib]
  rw [p.sum_one']
  rw [q.sum_one']
  norm_num
  rw [← Finset.mul_sum]
  ring


/- Squared Hellinger distance-/
def hellingerSqF : ℝ → ℝ := fun x ↦
  (1/2) * (√x - 1)^2

instance : FDivFunction hellingerSqF where
  one := by simp [hellingerSqF]
  convex := by
    unfold hellingerSqF
    apply ConvexOn.smul (by norm_num)
    -- We will expand the function and show convexity of each part
    let f x := (Real.sqrt x - 1) ^ 2
    let h x := x - 2 * Real.sqrt x + 1
    -- Prove that f and h are equal on the set Set.Ici 0
    have h_eqon : EqOn f h (Set.Ici 0) := by
      intro x hx
      unfold f h
      ring_nf
      rw [pow_two]
      rw [Real.mul_self_sqrt hx]
    -- Switch the goal
    have h_iff : ConvexOn ℝ (Set.Ici 0) f ↔ ConvexOn ℝ (Set.Ici 0) h := by
      constructor
      · intro hc
        exact ConvexOn.congr hc h_eqon
      · intro hc
        exact ConvexOn.congr hc h_eqon.symm
    rw [h_iff]
    unfold h
    -- Now prove convexity of the expanded version
    apply ConvexOn.add
    · apply ConvexOn.add
      · exact convexOn_id (convex_Ici 0)
      · apply ConcaveOn.neg
        apply ConcaveOn.smul (by norm_num)
        exact strictConcaveOn_sqrt.concaveOn
    exact convexOn_const 1 (convex_Ici 0)

/- We use the definition from Wikipedia:
    https://en.wikipedia.org/wiki/Hellinger_distance
  Note that Tsybakov (we prove some results from this
  text below) defines Squared Hellinger without the 1/2.
-/
def hellingerSq (p q: pmf Ω)[Dominates q p]: ℝ :=
   ∑ x, (1/2)*(√(p x) - √(q x))^2

def tsybakov_hellingerSq (p q: pmf Ω)[Dominates q p]: ℝ :=
  2 * hellingerSq p q

/- Squared hellinger distance is a f-divergence. -/
theorem hellingerSq_is_fdivergence (p q : pmf Ω) [Dominates q p] :
  fdiv hellingerSqF p q = hellingerSq p q := by
  unfold fdiv hellingerSqF hellingerSq
  apply Finset.sum_congr rfl
  intro x hx
  field_simp
  by_cases hq : q x = 0
  · simp_all [dominates_qx0_px0 p q x hq]
  · have hq_pos : 0 < q x := px_pos q x hq
    field_simp

theorem hellingerSq_self (p : pmf Ω)[Dominates p p] : 0 = hellingerSq p p := by
  unfold hellingerSq; field_simp

theorem hellingerSq_comm (p q : pmf Ω)[Dominates q p][Dominates p q] :
  hellingerSq p q = hellingerSq q p := by
  unfold hellingerSq
  apply Finset.sum_congr rfl
  intro x hx
  field_simp
  rw [sub_sq_comm]

theorem hellingerSq_zero_iff_eq (p q : pmf Ω)[Dominates q p]
  : hellingerSq p q = 0 ↔ p = q := by
  constructor
  · intro h
    unfold hellingerSq at h
    rw [Finset.sum_eq_zero_iff_of_nonneg] at h
    · simp_all
      apply InformationTheory.ext
      intro x
      specialize h x
      rw [← Real.sqrt_inj, ← sub_eq_zero]
      exact h
      · exact p.non_neg x
      · exact q.non_neg x
    · intro x hx
      simp [mul_nonneg, pow_two_nonneg]
  · intro h
    unfold hellingerSq
    rw [h]
    simp

-- Property (iii) in Tsybakov (Section 2.4)
lemma tsybakov_hellingerSq_multiplicative_form (p q : pmf Ω)[Dominates q p]
  : tsybakov_hellingerSq p q = 2*(1 - ∑ x, √((p x)*(q x))) := by
  unfold tsybakov_hellingerSq; unfold hellingerSq
  field_simp
  have h₁ : ∑ x, (√(p.f x) - √(q.f x)) ^ 2 = ∑ x, (p x - 2*√(p x * q x)+ q x) := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [sub_sq, sq_sqrt, sq_sqrt, sqrt_mul]
    ring
    · exact p.non_neg x
    · exact q.non_neg x
    · exact p.non_neg x
  have h₂ : ∑ x, (p x - 2*√(p x * q x) + q x) = 2 - ∑ x, 2*√(p x * q x) := by
    simp [Finset.sum_add_distrib, p.sum_one', q.sum_one']
    ring
  suffices ∑ x, (√(p.f x) - √(q.f x)) ^ 2 = 2 - ∑ x, 2*√(p.f x * q.f x) by
    rw [← Finset.sum_div, this]
    field_simp
    rw [sub_mul]
    rw [Finset.sum_mul]
    field_simp
    apply Finset.sum_congr rfl
    intro x hx
    ring
  simp [h₁, h₂]

theorem hellingerSq_multiplicative_form (p q : pmf Ω)[Dominates q p]
  : hellingerSq p q = (1 - ∑ x, √((p x)*(q x))) := by
  have : 2 * hellingerSq p q = 2*(1 - ∑ x, √((p x)*(q x))) := by
    rw [← tsybakov_hellingerSq]
    exact tsybakov_hellingerSq_multiplicative_form p q
  linarith


/- Neyman χ² divergence-/
def chiSqF : ℝ → ℝ := fun x ↦ (x - 1)^2

instance : FDivFunction chiSqF where
  one := by simp [chiSqF]
  convex := by
    unfold chiSqF
    let f x : ℝ := (x - 1) ^ 2
    let h x : ℝ := x^2 - 2 * x + 1
    have h_eqon : EqOn f h (Set.Ici 0) := by
      intro x hx
      unfold f h
      ring_nf
    have h_iff : ConvexOn ℝ (Set.Ici (0: ℝ)) f ↔ ConvexOn ℝ (Set.Ici (0: ℝ)) h := by
      constructor
      · intro hc
        exact ConvexOn.congr hc h_eqon
      · intro hc
        exact ConvexOn.congr hc h_eqon.symm
    rw [h_iff]
    unfold h
    apply ConvexOn.add
    · apply ConvexOn.add
      apply ConvexOn.pow
      · exact convexOn_id (convex_Ici 0)
      · intro x hx
        simp_all
      apply ConcaveOn.neg
      apply ConcaveOn.smul (by norm_num)
      apply concaveOn_id (convex_Ici 0)
    · exact convexOn_const 1 (convex_Ici 0)

def chiSq (p q: pmf Ω)[Dominates q p]: ℝ :=
   ∑ x, (p x - q x)^2 / q x

/- χ² divergence is a f-divergence. -/
theorem chiSq_is_fdivergence (p q : pmf Ω) [Dominates q p] :
  fdiv chiSqF p q = chiSq p q := by
  unfold fdiv chiSqF chiSq
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hq : q x = 0
  · simp_all
  · field_simp
    ring

theorem chiSq_self (p : pmf Ω)[Dominates p p] : 0 = chiSq p p := by
  unfold chiSq; field_simp

theorem chiSq_zero_iff_eq (p q : pmf Ω)[Dominates q p]
  : chiSq p q = 0 ↔ p = q := by
  constructor
  · intro h
    unfold chiSq at h
    rw [Finset.sum_eq_zero_iff_of_nonneg] at h
    · simp_all
      apply InformationTheory.ext
      intro x
      specialize h x
      rw [← sub_eq_zero]
      rcases h with h₁ | h₂
      · assumption
      · simp_all [dominates_qx0_px0 p q x h₂]
    · intro x hx
      by_cases hqx: q x = 0
      · simp_all
      · exact div_nonneg (pow_two_nonneg _) (q.non_neg x)
  · intro h
    unfold chiSq
    rw [h]
    simp

/- Le Cam's inequality

Lemma 2.3, Equation 2.16 in Tsybekov.
-/
lemma max_min_eq_two (p q : pmf Ω) [Dominates q p] :
  ∑ x, max (p x) (q x) + ∑ x, min (p x) (q x) = 2 := by
  rw [← Finset.sum_add_distrib]
  conv =>
    left
    right
    ext x
    rw [max_add_min]
  rw [Finset.sum_add_distrib]
  norm_num [pmf.sum_one']

lemma max_eq_two_min (p q : pmf Ω) [Dominates q p] :
  ∑ x, max (p x) (q x) = 2 - ∑ x, min (p x) (q x) := by
  rw [← max_min_eq_two p q]
  field_simp

lemma sum_sqrt_mul_sq_le_sum_mul_sum {Ω : Type*} [Fintype Ω]
    (a b : Ω → ℝ) (ha_nonneg : ∀ x, 0 ≤ a x) (hb_nonneg : ∀ x, 0 ≤ b x) :
    (∑ x, √(a x * b x))^2 ≤ (∑ x, a x) * (∑ x, b x) := by
  -- Apply Cauchy-Schwarz: (∑ uᵢvᵢ)² ≤ (∑ uᵢ²) (∑ vᵢ²)
  let u := fun x => Real.sqrt (a x)
  let v := fun x => Real.sqrt (b x)
  suffices (∑ x, u x * v x) ^ 2 ≤ (∑ x, u x ^ 2) * (∑ x, v x ^ 2) by
    simp_all [u, v]
  exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u v

theorem lecam_inequality (p q : pmf Ω) [Dominates q p] :
  (1/2)*(∑ x, √(p x * q x))^2 ≤ ∑ x, min (p x) (q x) := by
  calc (1/2)*(∑ x, √(p x * q x))^2
        = (1/2)*(∑ x, √(max (p x) (q x) * min (p x ) (q x)))^2 := by
          congr 3; funext x
          rw [max_mul_min]
      _ ≤ (1/2)*((∑ x, max (p x) (q x)) * (∑ x, min (p x) (q x))) := by
          apply mul_le_mul_of_nonneg_left
          · apply sum_sqrt_mul_sq_le_sum_mul_sum (fun x => max (p x) (q x)) (fun x => min (p x) (q x))
            · intro x
              exact le_max_of_le_left (p.non_neg x)
            · intro x
              exact le_min (p.non_neg x) (q.non_neg x)
          · simp
      _ = (1/2)*((2 - ∑ x, min (p x) (q x))*(∑ x, (min (p x) (q x)))) := by
          congr 1
          conv =>
            right
            rw [← max_eq_two_min]
      _ ≤ ∑ x, min (p x) (q x) := by
        let S := ∑ x, min (p x) (q x)
        suffices (1/2) * ((2 - S)*S) ≤ S by assumption
        rw [sub_mul]
        nlinarith

theorem lecam_connector_lemma (p q : pmf Ω) [Dominates q p] :
  (1/2)*(∑ x, √(p x * q x))^2 = (1/2)*(1 - (2 * hellingerSq p q)/2)^2 := by
    rw [hellingerSq_multiplicative_form p q]
    ring

theorem lecam_hellingerSq (p q : pmf Ω) [Dominates q p] :
  (1/2)*(1 - (2 * hellingerSq p q)/2)^2 ≤ ∑ x, min (p x) (q x) := by
  rw [← lecam_connector_lemma p q]
  exact lecam_inequality p q


/- Le Cam's inequality: H²(p, q) ≤ TV(p, q)
Lemma 2.3, Equation 2.17 in Tsybekov.
-/
theorem lecam_hellingerSq_le_tvd (p q : pmf Ω) [Dominates q p] :
  hellingerSq p q ≤ tvd p q := by
  rw [hellingerSq_multiplicative_form, scheffes_theorem]
  apply (sub_le_sub (by simp))
  apply Finset.sum_le_sum
  intro x hx
  have h: (min (p x) (q x))^2 ≤ (p x)*(q x) := by
    rcases le_total (p x) (q x) with hp | hq
    · rw [min_eq_left hp]
      nlinarith [hp, p.non_neg x]
    · rw [min_eq_right hq]
      nlinarith [hq, q.non_neg x]
  calc min (p x) (q x)
    _ = √((min (p x) (q x))*(min (p x) (q x))) := by
      ring_nf
      rw [Real.sqrt_sq (le_min (p.non_neg x) (q.non_neg x))]
    _ ≤ √((p x)*(q x)) := by
      ring_nf
      exact sqrt_le_sqrt h

/- Link between Hellinger and KL.
Lemma 2.4 in Tsybekov. -/
theorem hellingerSq_le_kld (p q : pmf Ω) [Dominates q p] :
  hellingerSq p q ≤ (1/2)*kld p q := by
  suffices 2*hellingerSq p q ≤ kld p q by linarith
  rw [kld_eq_kld_supp p q]
  unfold kld_supp
  calc ∑ x ∈ p.support, p.f x * log (p.f x / q.f x)
      = (∑ x ∈ p.support, (p x)*(log ((√((p x)/(q x)))^2))) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [sq_sqrt]
        by_cases hq: (q x = 0)
        · simp_all
        · exact div_nonneg (p.non_neg x) (q.non_neg x)
    _ = 2 * (∑ x ∈ p.support, (p x)*(log (√(p x)/√(q x)))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        field_simp
        rw [sqrt_div (p.non_neg x)]
        ring
    _ = -2*(∑ x ∈ p.support, (p x)*(log ((√(q x) / √(p x) - 1) + 1))) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        field_simp
        simp at hx
        have hq := dominates_pxne0_qxne0 p q x hx
        rw [Real.log_div, Real.log_div]
        ring
        · rwa [sqrt_ne_zero (q.non_neg x)]
        · rwa [sqrt_ne_zero (p.non_neg x)]
        · rwa [sqrt_ne_zero (p.non_neg x)]
        · rwa [sqrt_ne_zero (q.non_neg x)]
    _ ≥ -2*(∑ x ∈ p.support, (p x)*(√(q x / p x) - 1)) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_le_sum
        intro x hx
        field_simp
        simp at hx
        rw [mul_le_mul_left]
        rw [sqrt_div (q.non_neg x)]
        apply Real.log_le_sub_one_of_pos
        have hqx_pos : 0 < q.f x := px_pos q x (dominates_pxne0_qxne0 p q x hx)
        have hpx_pos : 0 < p.f x := px_pos p x hx
        exact div_pos (sqrt_pos.2 hqx_pos) (sqrt_pos.2 hpx_pos)
        · exact px_pos p x hx
    _ = -2*(∑ x ∈ p.support, √(p x * q x) - 1) := by
        conv =>
          left
          right
          right
          ext x
          rw [mul_sub_left_distrib]
          rw [sqrt_div (q.non_neg x)]
        rw [Finset.sum_sub_distrib]
        field_simp
        apply Finset.sum_congr rfl
        intro x hx
        rw [mul_comm]
        rw [mul_div_assoc]
        rw [div_sqrt]
        rw [sqrt_mul (p.non_neg x)]
        ring
    _ = 2*(1 - ∑ x ∈ p.support, √(p x * q x)) := by ring
    _ = 2*hellingerSq p q := by
      rw [hellingerSq_multiplicative_form]
      rw [Finset.sum_subset p.support.subset_univ]
      intro x hx hp
      rw [sqrt_eq_zero]
      · simp_all
      · simp_all
