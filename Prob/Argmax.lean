import Prob.Basic

/-!
# Most likely element of a `Prob α`
-/

open Classical
open Set
open scoped Real
noncomputable section

namespace Prob

variable {α : Type}

/-- The most likely element, breaking ties arbitrarily (`Option` version) -/
def argmax' (p : Prob α) : Option α := p.supp.toList.argmax p.prob

/-- `argmax'` is never `none` -/
lemma argmax'_isSome (p : Prob α) : p.argmax'.isSome := by
  rw [← Option.ne_none_iff_isSome, ne_eq, argmax', List.argmax_eq_none, Finset.toList_eq_nil]
  have t := p.total
  contrapose t
  simp only [ne_eq, not_not, supp] at t
  simp only [Finsupp.sum, t, Finset.sum_empty, zero_ne_one, not_false_eq_true]

/-- The most likely element, breaking ties arbitrarily -/
def argmax (p : Prob α) : α := p.argmax'.get (argmax'_isSome p)

/-- `argmax` unwraps `pure` -/
@[simp] lemma argmax_pure (x : α) : argmax (pure x) = x := by
  suffices h : argmax' (pure x) = some x by
    simp only [argmax, h, Option.get_some]
  simp only [argmax', supp_pure, Finset.toList_singleton, List.argmax_singleton]

/-- `argmax` has the largest probability -/
lemma le_prob_argmax (p : Prob α) (x : α) : p.prob x ≤ p.prob (p.argmax) := by
  by_cases px : p.prob x = 0
  · simp only [px, prob_nonneg]
  · have e : p.argmax' = some p.argmax := by simp [argmax]
    generalize p.argmax = a at e
    rw [argmax', List.argmax_eq_some_iff] at e
    apply e.2.1
    simpa only [supp, Finset.mem_toList, Finsupp.mem_support_iff, ne_eq]

/-- `argmax` has nonzero probability -/
lemma prob_argmax_ne_zero (p : Prob α) : p.prob p.argmax ≠ 0 := by
  have t := p.total
  contrapose t
  have z : p.prob.sum (fun _ p ↦ p) = 0 := by
    simp only [ne_eq, not_not] at t
    apply Finset.sum_eq_zero fun x _ ↦ ?_
    simp only
    refine le_antisymm ?_ (prob_nonneg _)
    rw [← t]
    exact le_prob_argmax p x
  simp only [z, zero_ne_one, not_false_eq_true]

/-- `argmax` has positive probability -/
@[bound] lemma prob_argmax_pos (p : Prob α) : 0 < p.prob (p.argmax) :=
  p.prob_argmax_ne_zero.symm.lt_of_le p.prob_nonneg

lemma argmax_mem_supp (p : Prob α) : p.argmax ∈ p.supp := by
  simp only [supp, Finsupp.mem_support_iff]
  exact prob_argmax_ne_zero p
