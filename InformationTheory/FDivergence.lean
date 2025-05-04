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

@[simp]
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
    simp_all
    apply InformationTheory.ext
    intro x
    specialize h x
    linarith
    simp
  · intro h
    unfold tvd
    rw [h]
    simp


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

def hellingerSq (p q: pmf Ω)[Dominates q p]: ℝ :=
   ∑ x, (1/2)*(√(p x) - √(q x))^2

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
