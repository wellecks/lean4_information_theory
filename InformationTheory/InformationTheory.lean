/-
Information theory basics from Chapter 2 of
   "Elements of Information Theory" by Thomas M. Cover & Joy A. Thomas,
with discrete random variables.

Current main results:
- Information inequality (`information_inequality`)

Current main definitions:
- Probability mass function (`pmf`)
- Entropy (`entropy`), KL-divergence (`kld`)

-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Algebra.Order.Field.Basic

namespace InformationTheory

noncomputable section

open Classical BigOperators Real

variable {Ω : Type*}[Fintype Ω]

/- Define our own pmf, partly for learning and partly for convenience.
   Differences with mathlib's PMF include:
   1. The mass function `f` is defined on ℝ versus ℝ≥0∞. This led to
     fewer conversions to and from ℝ and `ENNReal` (e.g., in proofs
     involving logarithms).
   2. Fintype: this allowed for Jensen's results for `Finset`s.
   3. Explicit `non_neg` condition (following from (1)).
-/
structure pmf (Ω : Type*)[Fintype Ω] :=
   (f : Ω → ℝ)
   (non_neg : ∀ x : Ω, 0 ≤ f x)
   (sum_one : HasSum f 1)

-- Allows for `p x` notation.
instance funLike : FunLike (pmf Ω) Ω fun _ => ℝ where
  coe p x := p.f x
  coe_injective' p q h := by
   cases p
   cases q
   congr

theorem hasSum_coe_one (p : pmf Ω) : HasSum p 1 := p.sum_one

-- Probability of any outcome is at most one.
theorem coe_le_one (p : pmf Ω) (x : Ω) : p x ≤ 1 := by
   refine' hasSum_le _ (hasSum_ite_eq x (p x)) (hasSum_coe_one p)
   intro x
   split_ifs with h
   rw [h]
   exact p.non_neg x

-- Writes has_sum in terms of Finset.sum
theorem pmf.sum_one' (p : pmf Ω) : ∑ x, p x = 1 := by
   have hsum := p.sum_one.tsum_eq
   rw [tsum_eq_sum] at hsum
   exact hsum
   intros x hx
   simp at hx

/-- The support of a `pmf` is the set where it is nonzero. -/
def pmf.support (p : pmf Ω) : Finset Ω := {x | p x ≠ 0}.toFinset

theorem mem_support_pos (p : pmf Ω) (x : Ω) : x ∈ p.support ↔ p x > 0 := by
   apply Iff.intro
   unfold pmf.support
   intro hx
   rw [Set.mem_toFinset] at hx
   simp [hx]
   rw [lt_iff_le_and_ne]
   apply And.intro
   exact p.non_neg x
   apply Ne.symm
   simp
   exact hx
   intro h
   unfold pmf.support
   rw [Set.mem_toFinset]
   simp [h]
   exact ne_of_gt h

@[simp]
theorem mem_support_iff (p : pmf Ω) (x : Ω) : x ∈ p.support ↔ p x ≠ 0 := by
   unfold pmf.support
   rw [Set.mem_toFinset]
   simp

@[simp]
theorem pmf.support_sum (p: pmf Ω) : ∑ x in p.support, p x = 1 := by
   rw [← p.sum_one']
   apply Finset.sum_subset
   simp
   intro x _ hxs
   simp at hxs
   exact hxs

theorem support_pos (p: pmf Ω) : 0 < ∑ x in p.support, p x := by simp

theorem support_eq_inner (p: pmf Ω) (f : Ω → ℝ) (g : Ω → ℝ) (hsupp: ∀ x ∈ p.support, f x = g x) :
    ∑ x in p.support, f x = ∑ x in p.support, g x := by
      simp only [Finset.sum_congr rfl hsupp]

@[simp]
theorem support_nonempty (p : pmf Ω) : p.support.Nonempty := by
   by_contra h
   simp at h
   have h' : ∑ x in p.support, p x = ∑ x in (∅: Finset Ω), p x := by rw [h]
   simp [Finset.sum_empty] at h'

theorem log_eq_inner {s} (f : Ω → ℝ) (g : Ω → ℝ) (hsupp: ∑ x in s, f x = ∑ x in s, g x) :
    log (∑ x in s, f x) = log (∑ x in s, g x) := by simp [hsupp]

/- 2.1 Entropy -/
-- The entropy $H(X)$ of a discrete random variable $X$
def entropy (p : pmf Ω) : ℝ :=
   ∑ x in p.support, - ((p x) * (log (p x)))

-- If $X∼p(x), the expected value of the random variable $g(X)$
def expected_value (p : pmf Ω) (g : Ω → ℝ) : ℝ :=
   ∑ x in p.support, (p x) * (g x)

-- Remark 2.3: The entropy of $X$ is the expected value of the random variable
-- $log (1/p(X))$, where $X∼p(x)$.
lemma entropy_as_expectation (p : pmf Ω) : entropy p = expected_value p (λ x => - log (p x)) := by
   simp [entropy, expected_value]

-- L2.1.1: Entropy is non-negative.
lemma entropy_nonneg (p: pmf Ω) : entropy p ≥ 0 := by
   rw [entropy]
   apply Finset.sum_nonneg
   intro x _
   simp
   rw [mul_nonpos_iff]
   left
   constructor
   exact p.non_neg x
   rw [log_nonpos_iff']
   exact coe_le_one p x
   exact p.non_neg x

/- We say that `q` dominates `p` if $q(x) = 0$ implies $p(x) = 0$.
   Equivalently, we can say that the measure of `p`
   is absolutely continuous with respect to the measure of `q`.
   See: https://en.wikipedia.org/wiki/Absolute_continuity. -/
class Dominates (q: pmf Ω) (p: pmf Ω) where
   abs_cont : p.support ⊆ q.support

theorem dominates_mem_supp (p q: pmf Ω)[Dominates q p]
   (x : Ω) (hsupp: x ∈ p.support) : x ∈ q.support := Dominates.abs_cont hsupp

theorem dominated_lte (p q: pmf Ω)[Dominates q p] :
   ∑ x in p.support, q x ≤ ∑ x in q.support, q x := by
      refine' Finset.sum_le_sum_of_subset_of_nonneg Dominates.abs_cont _
      intro x _ _
      exact q.non_neg x

theorem dominated_supp_gt_0 (p q: pmf Ω)[Dominates q p] :
   0 < ∑ x in pmf.support p, q x := by
   apply Finset.sum_pos
   intro x hx
   have h := dominates_mem_supp p q x hx
   rw [mem_support_pos] at h
   exact h
   simp

-- D2.26 KL divergence
def kld (p q: pmf Ω)[Dominates q p]: ℝ :=
   ∑ x in p.support, (p x)*(log (p x / q x))

-- 2.6: Jensen's Inequality And Its Consequences
/- Thm. 2.6.2 (Jensen's Inequality.)
   We prove the concave version:
   If f is a concave function and X is a random variable, then
   𝔼[f(X)] ≤ f(𝔼[X]).  -/
theorem jensens_inequality_concave
   {S : Set ℝ} (f: ℝ → ℝ) (g: Ω → ℝ)
   (p: pmf Ω) (hf: ConcaveOn ℝ S f) (hmem: ∀ x ∈ p.support, g x ∈ S) :
   ∑ x in p.support, (p x) * f (g x) ≤ f (∑ x in p.support, (p x) * (g x)) := by
   have hnonneg : ∀ (x : Ω), x ∈ p.support → 0 ≤ p x := by
      intro x _
      exact p.non_neg x
   refine' hf.le_map_sum hnonneg p.support_sum hmem

theorem neg_sum {α: Type*} (S : Finset α) (f : α → ℝ) :
   - ∑ x in S, f x = ∑ x in S, - (f x) := by simp

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
   apply inv_mul_cancel
   simpa using hsupp

/- Theorem 2.6.3 (Information inequality)
   Let $p(x), q(x), x ∈ X$ be two probability mass functions.
   Then $KL(p || q) ≥ 0$. -/
theorem information_inequality (p q: pmf Ω)[Dominates q p]: kld p q ≥ 0 := by
   rw [kld]
   suffices hrev : - kld p q ≤ 0
   simpa using hrev

   unfold kld
   rw [neg_sum]
   calc
      ∑ x in p.support, -(p x * log (p x / q x)) = ∑ x in p.support, p x * log (q x / p x) := by
         rw [Finset.sum_eq_sum_iff_of_le]
         intros x hx
         exact neg_plogpq_eq_plogqp p q x hx
         intros x hx
         rw [neg_plogpq_eq_plogqp p q x hx]
      _ ≤ log (∑ x in p.support, p x * (q x / p x)) := by
         apply jensens_inequality_concave (S:= (Set.Ioi 0)) log (λ x => (q x / p x)) p  _
         intros x hp
         have hq := dominates_mem_supp p q x hp
         rw [mem_support_pos] at hp
         rw [mem_support_pos] at hq
         simp
         apply div_pos
         exact hq
         exact hp
         exact log_concave
      _ = log (∑ x in p.support, q x) := by
         ring_nf
         apply log_eq_inner
         apply support_eq_inner
         intro x hx
         rwa [mul_assoc, mul_comm, mul_assoc, inv_supp_cancel p x, mul_one]
      _ ≤ log (∑ x in q.support, q x) := by
         rw [log_le_log]
         exact dominated_lte p q
         exact dominated_supp_gt_0 p q
         exact support_pos q
      _ = 0 := by
         rw [q.support_sum]
         simp
