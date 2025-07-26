import Misc.Bound
import Prob.Defs

/-!
# Force a function into a probability distribution

This is useful if we have a function that we know corresponds to valid probabilities, and just want
to treat as a `Prob`.
-/

noncomputable section

open Classical
variable {α : Type}
namespace Prob

/-- Turn a bunch of reals into a distribution, producing something arbitrary if invalid -/
def force [n : Nonempty α] (p : α → ℝ) (s : Finset α) : Prob α :=
  if h : (∀ x ∈ s, 0 ≤ p x) ∧ ∑ x ∈ s, p x = 1 then {
    prob := ∑ x ∈ s, .single x (p x),
    prob_nonneg := by
      intro x
      simp only [Finsupp.coe_finset_sum, Finset.sum_apply]
      bound
    total := by
      refine Eq.trans ?_ h.2
      simp only [Finsupp.sum, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.single_apply,
        Finset.sum_ite_eq', Finset.sum_ite_mem]
      refine Finset.sum_subset (by simp) (fun z m n ↦ ?_)
      simp only [Finset.mem_inter, Finsupp.mem_support_iff, Finsupp.coe_finset_sum,
        Finset.sum_apply, m, and_true, Decidable.not_not] at n
      rw [Finset.sum_eq_zero_iff_of_nonneg (by bound)] at n
      simp only [Finsupp.single_apply, ite_eq_right_iff] at n
      exact n z m rfl
  } else pure Classical.ofNonempty

/-- The key property of `force`, for use with `rw` -/
lemma prob_force {n : Nonempty α} (p : α → ℝ) (s : Finset α)
    (h : (∀ x ∈ s, 0 ≤ p x) ∧ ∑ x ∈ s, p x = 1) :
    (force (n := n) p s).prob = fun x ↦ if x ∈ s then p x else 0 := by
  ext x
  simp only [force, h, and_true]
  split_ifs with h n
  all_goals simp_all [Finsupp.single_apply]
