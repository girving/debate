import Misc.Bound
import Prob.Defs

/-!
# Force a function into a probability distribution

This is useful if we have a function that we know corresponds to valid probabilities, and just want
to treat as a `Prob`.
-/

noncomputable section

open Classical
variable {X Y : Type}
variable [Fintype Y] [Inhabited Y]
namespace Prob

/-- Turn a bunch of reals into a distribution, producing something arbitrary if invalid -/
def force (p : Y → ℝ) : Prob Y :=
  if h : (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1 then {
    prob := ∑ x, .single x (p x),
    prob_nonneg := by
      intro x
      simp only [Finsupp.coe_finset_sum, Finset.sum_apply]
      bound
    total := by
      refine Eq.trans ?_ h.2
      simp only [Finsupp.sum, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.single_apply,
        Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      refine Finset.sum_subset (fun _ _ ↦ Finset.mem_univ _) (fun z _ h ↦ ?_)
      simpa only [Finsupp.mem_support_iff, Finsupp.coe_finset_sum, Finset.sum_apply, ne_eq,
        Decidable.not_not, Finsupp.single_apply, Finset.sum_ite_eq', Finset.mem_univ,
        ite_true] using h
  } else pure default

/-- The key property of `force`, for use with `rw` -/
lemma prob_force (p : Y → ℝ) (h : (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1) : (force p).prob = p := by
  ext y
  simp only [force, h, implies_true, and_self, ↓reduceDIte, Finsupp.coe_finset_sum,
    Finset.sum_apply]
  rw [Finset.sum_eq_single (a := y)]
  all_goals aesop
