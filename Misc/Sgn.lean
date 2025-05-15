import Mathlib.Data.Real.Basic

/-!
# The `sgn` function
-/

/-- The sign of a real number, treating zero as positive -/
noncomputable def sgn (x : ℝ) : ℝ := if 0 ≤ x then 1 else -1

@[simp] lemma sq_sgn (x : ℝ) : sgn x ^ 2 = 1 := by simp [sgn, apply_ite (f := (· ^ 2))]
@[simp] lemma abs_sgn (x : ℝ) : |sgn x| = 1 := by simp [sgn, apply_ite (f := abs)]

@[simp] lemma sgn_mul_eq_abs (x : ℝ) : sgn x * x = |x| := by
  by_cases x0 : 0 ≤ x
  · simp [sgn, x0, abs_of_nonneg]
  · simp only [not_le] at x0
    simp [sgn, x0, abs_of_neg]
