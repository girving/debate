import Prob.Arith
import Prob.Argmax

/-!
# A predicate that a probability distribution is pure
-/

open Classical
open scoped Real
noncomputable section
namespace Prob

variable {α : Type}

/-- A probability distribution is pure if each outcome has probability 0 or 1 -/
def IsPure (p : Prob α) : Prop :=
  ∀ x, p.prob x = 0 ∨ p.prob x = 1

/-- `pure` satisfies IsPure -/
@[simp] lemma pure_is_pure (x : α) : (pure x : Prob α).IsPure := by
  intro z
  simp [Prob.prob_pure, ne_or_eq]

/-- Two probabilities can't sum to more than 1 -/
lemma prob_add_prob_le_one (p : Prob α) {x y : α} (h : x ≠ y) : p.prob x + p.prob y ≤ 1 := by
  set q := (fun z ↦ decide (z = x)) <$> p
  simp only [← q.bool_total]
  refine add_le_add (le_of_eq ?_) ?_
  · simp only [prob_map, decide_eq_true_eq, q, pr_eq_prob]
  · simp only [← pr_eq_prob, pr_map, decide_eq_false_iff_not, q]
    apply pr_mono
    aesop

/-- Pure distributions are equal to pure of their argmax -/
lemma IsPure.eq_pure {p : Prob α} (h : IsPure p) : p = pure p.argmax := by
  have a1 : p.prob p.argmax = 1 := by
    specialize h p.argmax
    contrapose h
    simpa only [prob_argmax_ne_zero, false_or, ne_eq]
  ext y
  by_cases ya : y = p.argmax
  · simp only [ya, a1, prob_pure, ↓reduceIte]
  · have t := p.prob_add_prob_le_one ya
    simp only [prob_pure, ya, ↓reduceIte, a1] at t ⊢
    linarith [p.prob_nonneg (x := y)]
