import Mathlib.Data.Real.Basic

/-!
# Bool utilities
-/

open scoped Real

/-- Lift a bool to a real number -/
@[coe] def Bool.toReal (b : Bool) : ℝ := if b then 1 else 0
instance : CoeTail Bool ℝ := ⟨Bool.toReal⟩
@[simp] lemma Bool.toReal_true : (true : ℝ) = 1 := rfl
@[simp] lemma Bool.toReal_false : (false : ℝ) = 0 := rfl
