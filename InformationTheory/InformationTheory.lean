/-
Information theory basics from Chapter 2 of
   "Elements of Information Theory" by Thomas M. Cover & Joy A. Thomas,
with discrete random variables.

Current main results:
- Information inequality (`information_inequality`)

Current main definitions:
- Probability mass function (`pmf`)
- Entropy (`entropy`), KL-divergence (`kld`)

Author: Sean Welleck
-/
import LLMlean

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions

namespace InformationTheory

noncomputable section

open Classical BigOperators Real

variable {Ω : Type*}[Fintype Ω]

section pmf

/- **`pmf Ω`** is a finite-alphabet real-valued probability
mass function. This had advantages over `PMF Ω` for this formalization:
   1. Working in ℝ led to fewer conversions to and from ℝ≥0∞,
      e.g., in proofs involving logarithms.
   2. We can use Mathlib's Jensen inequality for `Finset` sums
      (`ConvexOn.le_map_sum` / `ConcaveOn.le_map_sum`).

Also note that `pmf` has an explicit non-negativity condition due to (1).
-/
structure pmf (Ω : Type*)[Fintype Ω] where
   (f : Ω → ℝ)
   (non_neg : ∀ x : Ω, 0 ≤ f x)
   (sum_one : HasSum f 1)

-- Allows for `p x` notation.
instance pmfCoe : CoeFun (pmf Ω) (fun _ => Ω → ℝ) where
  coe p := p.f

theorem hasSum_coe_one (p : pmf Ω) : HasSum p 1 := p.sum_one

-- Probability of any outcome is at most one.
theorem coe_le_one (p : pmf Ω) (x : Ω) : p x ≤ 1 := by
  refine' hasSum_le _ (hasSum_ite_eq x (p x)) (hasSum_coe_one p)
  intro x'
  by_cases hx : x' = x
  · simp [hx]
  · simp [hx, p.non_neg x']

-- Writes has_sum in terms of Finset.sum
theorem pmf.sum_one' (p : pmf Ω) : ∑ x, p x = 1 := by
   rw [← tsum_fintype]
   exact p.sum_one.tsum_eq

/-- The support of a `pmf` is the set where it is nonzero. -/
def pmf.support (p : pmf Ω) : Finset Ω := {x | p x ≠ 0}.toFinset

theorem mem_support_pos (p : pmf Ω) (x : Ω) : x ∈ p.support ↔ p x > 0 := by
   constructor
   ·  intro hx
      unfold pmf.support at hx
      simp_all [Set.mem_toFinset]
      rw [lt_iff_le_and_ne]
      constructor
      ·  exact p.non_neg x
      ·  simp_all [Ne.symm]
   ·  intro h
      unfold pmf.support
      simp_all [Set.mem_toFinset]
      linarith

@[simp]
theorem mem_support_iff (p : pmf Ω) (x : Ω) : x ∈ p.support ↔ p x ≠ 0 := by
   unfold pmf.support
   simp [Set.mem_toFinset]

@[simp]
theorem pmf.support_sum (p: pmf Ω) : ∑ x ∈ p.support, p x = 1 := by
   rw [← p.sum_one']
   apply Finset.sum_subset
   ·  exact Finset.subset_univ p.support
   ·  simp_all

theorem support_pos (p: pmf Ω) : 0 < ∑ x ∈ p.support, p x := by simp

theorem support_eq_inner (p: pmf Ω) (f : Ω → ℝ) (g : Ω → ℝ)
  (hsupp: ∀ x ∈ p.support, f x = g x) :
     ∑ x ∈ p.support, f x = ∑ x ∈ p.support, g x := by
   simp only [Finset.sum_congr rfl hsupp]

@[simp]
theorem support_nonempty (p : pmf Ω) : p.support.Nonempty := by
   by_contra h
   simp at h
   have h' : ∑ x ∈ p.support, p x = ∑ x ∈ (∅: Finset Ω), p x := by rw [h]
   simp [Finset.sum_empty] at h'

/--Turn a mathlib `PMF` into our real-valued `pmf` (finite alphabet). -/
def PMF.to_pmf {Ω : Type*} [Fintype Ω] (p : PMF Ω) : pmf Ω where
  f        := fun x ↦ (p x).toReal
  non_neg  := fun x ↦ (p x).toReal_nonneg
  sum_one  := by
   have h_has := hasSum_fintype (fun x : Ω ↦ (p x).toReal)
   have h_sum : (∑ x : Ω, (p x).toReal) = 1 := by
      rw [← ENNReal.toReal_sum]
      ·  have : ∑ a, p a = 1 := by simp [← tsum_fintype, p.tsum_coe]
         rw [this]
         exact ENNReal.toReal_one
      ·  intro x hx
         exact p.apply_ne_top x
   simp_all

/--Turn our finite, real-valued `pmf` into mathlib’s `PMF`. -/
def pmf.toPMF (p : pmf Ω) : PMF Ω := by
   let f := fun x ↦ ENNReal.ofReal (p x)
   refine PMF.ofFinset f p.support ?sum_one ?outside_zero
   · simp [pmf.support_sum, f, ENNReal.ofReal_toReal]
     rw [← ENNReal.ofReal_sum_of_nonneg]
     · simp
     · intro x hx
       exact p.non_neg x
   · intro x hx
     simp_all
     simp [f, hx]

omit [Fintype Ω] in
theorem log_eq_inner {s} (f : Ω → ℝ) (g : Ω → ℝ)
   (hsupp: ∑ x ∈ s, f x = ∑ x ∈ s, g x) :
    log (∑ x ∈ s, f x) = log (∑ x ∈ s, g x) := by simp [hsupp]

end pmf

section entropy
/- 2.1 Entropy -/
-- The entropy $H(X)$ of a discrete random variable $X$
def entropy (p : pmf Ω) : ℝ :=
   ∑ x, - ((p x) * (log (p x)))

-- If $X∼p(x), the expected value of the random variable $g(X)$
def expected_value (p : pmf Ω) (g : Ω → ℝ) : ℝ :=
   ∑ x, (p x) * (g x)

-- Remark 2.3: The entropy of $X$ is the expected value of the random variable
-- $log (1/p(X))$, where $X∼p(x)$.
lemma entropy_as_expectation (p : pmf Ω) : entropy p = expected_value p (λ x => - log (p x)) := by
   simp [entropy, expected_value]

-- L2.1.1: Entropy is non-negative.
lemma entropy_nonneg (p: pmf Ω) : entropy p ≥ 0 := by
   apply Finset.sum_nonneg
   intro x hx
   simp [mul_nonpos_iff]
   constructor
   constructor
   · exact p.non_neg x
   · rw [log_nonpos_iff] <;> simp [coe_le_one, p.non_neg]

end entropy

section kld

/- We say that `q` dominates `p` if $q(x) = 0$ implies $p(x) = 0$.
   Equivalently, we can say that the measure of `p`
   is absolutely continuous with respect to the measure of `q`.
   We prove the equivalence of this subset form below.
   See: https://en.wikipedia.org/wiki/Absolute_continuity. -/
class Dominates (q: pmf Ω) (p: pmf Ω) where
   abs_cont : p.support ⊆ q.support

theorem dominates_mem_supp (p q: pmf Ω)[Dominates q p]
   (x : Ω) (hsupp: x ∈ p.support) : x ∈ q.support := Dominates.abs_cont hsupp

lemma dominates_qx0_px0 (p q : pmf Ω)[Dominates q p] (x : Ω) : q x = 0 → p x = 0 := by
   intro hq0
   by_contra h
   have hx_p : x ∈ p.support := by
      simpa [mem_support_iff]
   have hx_q : x ∈ q.support := dominates_mem_supp p q x hx_p
   simp_all

lemma dominates_pxne0_qxne0 (p q : pmf Ω)[Dominates q p] (x : Ω) : p x ≠ 0 → q x ≠ 0 := by
   by_contra h
   simp at h
   simp_all [h.2, dominates_qx0_px0 p q x]

lemma qx0_px0_dominates (p q : pmf Ω) (hzero : ∀ x, q x = 0 → p x = 0)
   : Dominates q p := by
      refine ⟨?hsubset⟩
      intro x hx_p
      have hp_ne : p x ≠ 0 := by
         simpa [mem_support_iff] using hx_p
      by_contra hx_not
      have hq0 : q x = 0 := by
         have : x ∉ q.support := by
            simpa [mem_support_iff] using hx_not
         simpa
      have hp0 : p x = 0 := hzero x hq0
      exact hp_ne hp0

/- The subset condition in `Dominates` is equivalent to the condition
   if $q(x) = 0$ implies $p(x) = 0$. -/
theorem dominates_iff_zero_imp_zero (p q : pmf Ω) :
   Dominates q p ↔ (∀ x, q x = 0 → p x = 0) := by
   constructor
   ·  intro hdom
      exact dominates_qx0_px0 p q
   ·  exact qx0_px0_dominates p q

lemma equal_support (p q : pmf Ω)[Dominates q p] :
  (∑ x ∈ p.support, p x) = (∑ x ∈ q.support, p x) := by
    refine Finset.sum_subset Dominates.abs_cont ?_
    intro x hxq hxp
    simp_all

lemma qsupport_sum (p q : pmf Ω)[Dominates q p] :
  ∑ x ∈ q.support, p x = 1 := by rw [← equal_support, p.support_sum]

theorem dominated_lte (p q: pmf Ω)[Dominates q p] :
   ∑ x ∈ p.support, q x ≤ ∑ x ∈ q.support, q x := by
   refine' Finset.sum_le_sum_of_subset_of_nonneg Dominates.abs_cont _
   intro x _ _
   exact q.non_neg x

theorem dominated_supp_gt_0 (p q: pmf Ω)[Dominates q p] :
   0 < ∑ x ∈ pmf.support p, q x := by
   apply Finset.sum_pos
   ·  intro x hx
      have h := dominates_mem_supp p q x hx
      rw [mem_support_pos] at h
      exact h
   ·  exact support_nonempty p

-- D2.26 KL divergence
def kld (p q: pmf Ω)[Dominates q p]: ℝ :=
   ∑ x, if p x = 0 then 0
        else (p x)*(log (p x / q x))

def kld_supp (p q: pmf Ω)[Dominates q p]: ℝ :=
   ∑ x ∈ p.support, (p x)*(log (p x / q x))

lemma kld_eq_kld_supp (p q : pmf Ω)[Dominates q p] :
   kld p q = kld_supp p q := by
   rw [kld, kld_supp]
   have h_filter :
      (∑ x : Ω, if hp : p x = 0 then 0 else p x * log (p x / q x)) =
        ∑ x ∈ Finset.filter (fun x : Ω ↦ p x ≠ 0) Finset.univ,
            p x * log (p x / q x) := by
      simp [Finset.sum_filter, mem_support_iff]
   simpa [h_filter, pmf.support]

-- 2.6: Jensen's Inequality And Its Consequences
/- Thm. 2.6.2 (Jensen's Inequality.)
   We prove the concave version:
   If f is a concave function and X is a random variable, then
   𝔼[f(X)] ≤ f(𝔼[X]).  -/
theorem jensens_inequality_concave
   {S : Set ℝ} (f: ℝ → ℝ) (g: Ω → ℝ)
   (p: pmf Ω) (hf: ConcaveOn ℝ S f) (hmem: ∀ x ∈ p.support, g x ∈ S) :
   ∑ x ∈ p.support, (p x) * f (g x) ≤ f (∑ x ∈ p.support, (p x) * (g x)) := by
   have hnonneg : ∀ (x : Ω), x ∈ p.support → 0 ≤ p x := by
      intro x _
      exact p.non_neg x
   refine' hf.le_map_sum hnonneg p.support_sum hmem

theorem neg_sum {α: Type*} (S : Finset α) (f : α → ℝ) :
   - ∑ x ∈ S, f x = ∑ x ∈ S, - (f x) := by simp

theorem neg_logpq_eq_logqp (p q: pmf Ω)[Dominates q p] (x : Ω) (h : x ∈ p.support) :
   - log (p x / q x) = log (q x / p x) := by
   calc
      - log (p x / q x) = - ((log (p x)) - (log (q x))) := by
         rw [log_div]
         simpa using h
         simpa using (dominates_mem_supp p q x h)
      _ = (log (q x) - log (p x)) := by ring
      _ = log (q x / p x) := by
         rw [← log_div]
         simpa using (dominates_mem_supp p q x h)
         simpa using h

theorem neg_plogpq_eq_plogqp (p q: pmf Ω)[Dominates q p] (x : Ω) (h : x ∈ p.support) :
   -(p x * log (p x / q x)) = p x * log (q x / p x) := by
   rw [mul_comm, ←neg_mul, (neg_logpq_eq_logqp p q x h), mul_comm]

theorem log_concave : ConcaveOn ℝ (Set.Ioi 0) log := by
   refine' StrictConcaveOn.concaveOn _
   exact strictConcaveOn_log_Ioi

@[simp]
theorem inv_supp_cancel (p : pmf Ω) (x : Ω) (hsupp: x ∈ p.support) : (p x)⁻¹ * (p x) = 1 := by
  have hx_pos := (mem_support_pos p x).mp hsupp
  field_simp [hx_pos.ne']

/- Theorem 2.6.3 (Information inequality)
   Let $p(x), q(x), x ∈ X$ be two probability mass functions.
   Then $KL(p || q) ≥ 0$.

   This version uses the KL defined on the support.
-/
theorem information_inequality_supp (p q: pmf Ω)[Dominates q p]: kld_supp p q ≥ 0 := by
   rw [kld_supp]
   suffices hrev : - kld_supp p q ≤ 0 by
    apply neg_nonpos.mp
    exact hrev

   unfold kld_supp
   rw [neg_sum]
   calc
      ∑ x ∈ p.support, -(p x * log (p x / q x)) = ∑ x ∈ p.support, p x * log (q x / p x) := by
         apply Finset.sum_congr rfl
         intro x hx
         exact neg_plogpq_eq_plogqp p q x hx
      _ ≤ log (∑ x ∈ p.support, p x * (q x / p x)) := by
         apply jensens_inequality_concave (S:= (Set.Ioi 0)) log (λ x => (q x / p x)) p log_concave
         intros x hp
         have hq := dominates_mem_supp p q x hp
         rw [mem_support_pos] at hp
         rw [mem_support_pos] at hq
         simp
         apply div_pos
         · exact hq
         · exact hp
      _ = log (∑ x ∈ p.support, q x) := by
         ring_nf
         apply log_eq_inner
         apply support_eq_inner
         intro x hx
         rwa [mul_assoc, mul_comm, mul_assoc, inv_supp_cancel p x, mul_one]
      _ ≤ log (∑ x ∈ q.support, q x) := by
         apply log_le_log
         · exact dominated_supp_gt_0 p q
         · apply dominated_lte p q
      _ = 0 := by
         simp [q.support_sum]

/- Theorem 2.6.3 (Information inequality)
   Let $p(x), q(x), x ∈ X$ be two probability mass functions.
   Then $KL(p || q) ≥ 0$.
-/
theorem information_inequality (p q: pmf Ω)[Dominates q p]: kld p q ≥ 0 := by
   rw [kld_eq_kld_supp]
   apply information_inequality_supp

end kld

end
