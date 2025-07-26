import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Prob.Arith

/-!
# Jensen's inequality for expectation
-/

open Classical
open Real (log logb)
open Set
namespace Prob

variable {α : Type}

/-- Convex Jensen's inequality for `Prob` -/
lemma map_exp_le (p : Prob α) {f : ℝ → ℝ} {s : Set ℝ} (fc : ConvexOn ℝ s f) {g : α → ℝ}
    (sub : ∀ x, p.prob x ≠ 0 → g x ∈ s) : f (p.exp g) ≤ p.exp (fun x ↦ f (g x)) := by
  simp only [exp, Finsupp.sum]
  refine ConvexOn.map_sum_le fc ?_ ?_ ?_
  · intro _ _; exact p.prob_nonneg
  · simpa only [Finsupp.sum] using p.total
  · intro x px; simp only [Finsupp.mem_support_iff] at px; exact sub x px

/-- Concave Jensen's inequality for `Prob` -/
lemma le_map_exp (p : Prob α) {f : ℝ → ℝ} {s : Set ℝ} (fc : ConcaveOn ℝ s f) {g : α → ℝ}
    (sub : ∀ x, p.prob x ≠ 0 → g x ∈ s) : p.exp (fun x ↦ f (g x)) ≤ f (p.exp g) := by
  rw [← neg_le_neg_iff, ← exp_neg]
  exact p.map_exp_le (f := fun x ↦ -f x) fc.neg sub

/-- `logb` is concave -/
lemma concaveOn_logb_Ioi {b : ℝ} (b1 : 1 ≤ b) : ConcaveOn ℝ (Ioi 0) (logb b) := by
  have e : logb b = fun x ↦ log x / log b := rfl
  simp only [e, div_eq_inv_mul, ← smul_eq_mul]
  apply strictConcaveOn_log_Ioi.concaveOn.smul
  simp only [inv_nonneg]
  exact Real.log_nonneg b1

/-- Special case for absolute value -/
lemma abs_exp_le_exp_abs (p : Prob α) (g : α → ℝ) : |p.exp g| ≤ p.exp (fun x ↦ |g x|) := by
  simp only [← Real.norm_eq_abs]
  exact map_exp_le (s := univ) _ convexOn_univ_norm (by simp)
