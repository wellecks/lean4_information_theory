/- F-divergences and their basic properties

We use our discrete, finite-alphabet `pmf`.

References:
- https://people.ece.cornell.edu/zivg/ECE_5630_Lectures6.pdf
- https://www.ee.bgu.ac.il/~haimp/ml/lectures/lect10_f_div/Lecture_on_f_divergence_and_hypothesis_testing
- https://en.wikipedia.org/wiki/F-divergence

Author: Sean Welleck
-/
import LLMlean

import InformationTheory.InformationTheory
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions

open InformationTheory

namespace InformationTheory

noncomputable section

open Classical BigOperators Real

variable {Ω : Type*}[Fintype Ω]

class FDivFunction (f : ℝ → ℝ) where
  nonneg : ∀ x, 0 ≤ f x
  one : f 1 = 0
  convex : ConvexOn ℝ (Set.Ici 0) f

def fdiv (f : ℝ → ℝ) [FDivFunction f] (p q : pmf Ω) : ℝ :=
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
